/*
 * One HTTP request with libcurl, for LeanTools.Http.
 *
 * leantools_http_request(method, url, headers, body, timeout_ms, max_bytes) performs the request
 * and returns the HTTP status, response body and response headers, or an IO error. It
 * blocks; the caller runs it on a task of its own.
 *
 * - The body is bytes; its length is given to curl, not computed from a C string.
 * - Redirects are not followed, so headers such as Authorization go to no other host.
 * - Only http and https are allowed.
 * - "Expect: 100-continue" is not sent, so a body is sent without a wait.
 * - CURLOPT_NOSIGNAL: libcurl uses no signals, which a multi-threaded caller needs.
 * - The proxy comes from the environment (libcurl reads http_proxy and https_proxy itself); the CA
 *   bundle from SSL_CERT_FILE or NIX_SSL_CERT_FILE when one is set, else libcurl's default.
 * - A response longer than max_bytes is an error.
 */

#include <lean/lean.h>
#include <curl/curl.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static pthread_once_t init_once = PTHREAD_ONCE_INIT;
static CURLcode init_result = CURLE_FAILED_INIT;

static void init(void) { init_result = curl_global_init(CURL_GLOBAL_DEFAULT); }

struct buffer {
  uint8_t *data;
  size_t size;
  size_t cap;
  size_t max;
  int too_long;
};

static size_t on_data(char *ptr, size_t size, size_t nmemb, void *userdata) {
  struct buffer *b = userdata;
  size_t n = size * nmemb;
  if (n > b->max - b->size) {
    b->too_long = 1;
    return 0; /* curl stops with CURLE_WRITE_ERROR */
  }
  if (b->size + n > b->cap) {
    size_t cap = b->cap ? b->cap : 16384;
    while (cap < b->size + n) cap = cap > SIZE_MAX / 2 ? SIZE_MAX : cap * 2;
    uint8_t *data = realloc(b->data, cap);
    if (!data) return 0;
    b->data = data;
    b->cap = cap;
  }
  memcpy(b->data + b->size, ptr, n);
  b->size += n;
  return n;
}

static lean_obj_res fail(char const *what, char const *detail) {
  size_t n = strlen(what) + strlen(detail) + 3;
  char *msg = malloc(n);
  if (!msg) return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(what)));
  snprintf(msg, n, "%s: %s", what, detail);
  lean_obj_res r = lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
  free(msg);
  return r;
}

/* (method url : @& String) (headers : @& Array String) (body : @& ByteArray) (timeoutMs : UInt32)
   (maxBytes : USize) : IO (UInt32 × ByteArray × ByteArray) */
LEAN_EXPORT lean_obj_res leantools_http_request(b_lean_obj_arg method, b_lean_obj_arg url,
                                                b_lean_obj_arg headers, b_lean_obj_arg body,
                                                uint32_t timeout_ms, size_t max_bytes) {
  pthread_once(&init_once, init);
  if (init_result != CURLE_OK) return fail("curl_global_init", curl_easy_strerror(init_result));

  CURL *curl = curl_easy_init();
  if (!curl) return fail("curl_easy_init", "failed");

  struct curl_slist *list = NULL;
  int list_ok = 1;
  size_t nh = lean_array_size(headers);
  for (size_t i = 0; i < nh && list_ok; i++) {
    struct curl_slist *l = curl_slist_append(list, lean_string_cstr(lean_array_get_core(headers, i)));
    if (l) list = l; else list_ok = 0;
  }
  if (list_ok) {
    struct curl_slist *l = curl_slist_append(list, "Expect:");
    if (l) list = l; else list_ok = 0;
  }
  if (!list_ok) {
    curl_slist_free_all(list);
    curl_easy_cleanup(curl);
    return fail("curl_slist_append", "out of memory");
  }

  struct buffer b = {NULL, 0, 0, max_bytes, 0};
  struct buffer h = {NULL, 0, 0, 64 * 1024, 0};
  char errbuf[CURL_ERROR_SIZE];
  errbuf[0] = 0;
  char const *ca = getenv("SSL_CERT_FILE");
  if (!ca || !*ca) ca = getenv("NIX_SSL_CERT_FILE");

  size_t body_size = lean_sarray_size(body);
  curl_easy_setopt(curl, CURLOPT_URL, lean_string_cstr(url));
  curl_easy_setopt(curl, CURLOPT_CUSTOMREQUEST, lean_string_cstr(method));
  curl_easy_setopt(curl, CURLOPT_HTTPHEADER, list);
  if (body_size > 0 || strcmp(lean_string_cstr(method), "GET") != 0) {
    curl_easy_setopt(curl, CURLOPT_POSTFIELDS, (char const *)lean_sarray_cptr((lean_object *)body));
    curl_easy_setopt(curl, CURLOPT_POSTFIELDSIZE_LARGE, (curl_off_t)body_size);
  }
  curl_easy_setopt(curl, CURLOPT_TIMEOUT_MS, (long)timeout_ms);
  curl_easy_setopt(curl, CURLOPT_NOSIGNAL, 1L);
  curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 0L);
  curl_easy_setopt(curl, CURLOPT_PROTOCOLS_STR, "http,https");
  curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, on_data);
  curl_easy_setopt(curl, CURLOPT_WRITEDATA, &b);
  curl_easy_setopt(curl, CURLOPT_HEADERFUNCTION, on_data);
  curl_easy_setopt(curl, CURLOPT_HEADERDATA, &h);
  curl_easy_setopt(curl, CURLOPT_ERRORBUFFER, errbuf);
  if (ca && *ca) curl_easy_setopt(curl, CURLOPT_CAINFO, ca);

  CURLcode rc = curl_easy_perform(curl);
  long status = 0;
  curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &status);
  curl_slist_free_all(list);
  curl_easy_cleanup(curl);

  if (b.too_long || h.too_long) {
    free(b.data);
    free(h.data);
    return fail(h.too_long ? "response headers" : "response", "longer than the limit");
  }
  if (rc != CURLE_OK) {
    free(b.data);
    free(h.data);
    return fail(curl_easy_strerror(rc), errbuf[0] ? errbuf : "no detail");
  }

  lean_object *arr = lean_alloc_sarray(1, b.size, b.size);
  if (b.size > 0) memcpy(lean_sarray_cptr(arr), b.data, b.size);
  free(b.data);
  lean_object *header_arr = lean_alloc_sarray(1, h.size, h.size);
  if (h.size > 0) memcpy(lean_sarray_cptr(header_arr), h.data, h.size);
  free(h.data);
  lean_object *payload = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(payload, 0, arr);
  lean_ctor_set(payload, 1, header_arr);
  lean_object *pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, lean_box_uint32((uint32_t)status));
  lean_ctor_set(pair, 1, payload);
  return lean_io_result_mk_ok(pair);
}
