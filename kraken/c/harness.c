/*
 * harness gen: print test permutations, one per line as "n p0 .. p(n-1)".
 * harness run: read such lines and print the result of permute for each,
 * as "ok d1 .. dk" or "blocked offset excess".
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* the bound on n in permute.c */
#define MAX_N 1024

int64_t permute(uint64_t n, uint16_t *perm, uint8_t *trace, uint16_t *blocked);

static void print_perm(int n, const int *p)
{
	printf("%d", n);
	for (int i = 0; i < n; i++)
		printf(" %d", p[i]);
	printf("\n");
}

/* every permutation of 0 .. n-1, in lexicographic order */
static void all_perms(int n)
{
	int p[16];
	for (int i = 0; i < n; i++)
		p[i] = i;
	for (;;) {
		print_perm(n, p);
		int i = n - 2;
		while (i >= 0 && p[i] > p[i + 1])
			i--;
		if (i < 0)
			return;
		int j = n - 1;
		while (p[j] < p[i])
			j--;
		int t = p[i]; p[i] = p[j]; p[j] = t;
		for (int a = i + 1, b = n - 1; a < b; a++, b--) {
			t = p[a]; p[a] = p[b]; p[b] = t;
		}
	}
}

static uint64_t rng = 0x9e3779b97f4a7c15u;

static uint64_t next(void)
{
	rng ^= rng << 13;
	rng ^= rng >> 7;
	rng ^= rng << 17;
	return rng;
}

static void random_perm(int n, int *p)
{
	for (int i = 0; i < n; i++)
		p[i] = i;
	for (int i = n - 1; i > 0; i--) {
		int j = next() % (i + 1);
		int t = p[i]; p[i] = p[j]; p[j] = t;
	}
}

/* a random permutation that moves only the top 17 positions, so no swap is blocked */
static void shallow_perm(int n, int *p)
{
	int k = n < 17 ? n : 17;
	random_perm(k, p + n - k);
	for (int i = 0; i < n - k; i++)
		p[i] = i;
	for (int i = n - k; i < n; i++)
		p[i] += n - k;
}

static int gen(void)
{
	int p[MAX_N];
	for (int n = 0; n <= 6; n++)
		all_perms(n);
	for (int r = 0; r < 2000; r++) {
		int n = next() % 41;
		random_perm(n, p);
		print_perm(n, p);
	}
	for (int r = 0; r < 500; r++) {
		int n = next() % 257;
		shallow_perm(n, p);
		print_perm(n, p);
	}
	for (int r = 0; r < 300; r++) {
		int n = next() % (MAX_N + 1);
		shallow_perm(n, p);
		print_perm(n, p);
	}
	for (int r = 0; r < 100; r++) {
		int n = next() % (MAX_N + 1);
		random_perm(n, p);
		print_perm(n, p);
	}
	int sizes[] = { 255, 256, 257, 300, MAX_N - 1, MAX_N };
	for (int s = 0; s < 6; s++) {
		int n = sizes[s];
		shallow_perm(n, p);
		print_perm(n, p);
		random_perm(n, p);
		print_perm(n, p);
	}
	/* one swap of two slots far below the top: blocked with a large offset and excess */
	for (int i = 0; i < MAX_N; i++)
		p[i] = i;
	p[300] = 301;
	p[301] = 300;
	print_perm(MAX_N, p);
	return 0;
}

static int run(void)
{
	uint64_t n;
	while (scanf("%lu", &n) == 1) {
		if (n > MAX_N)
			return 1;
		uint16_t perm[MAX_N], blocked[2];
		uint8_t trace[2 * MAX_N];
		for (uint64_t i = 0; i < n; i++) {
			unsigned v;
			if (scanf("%u", &v) != 1)
				return 1;
			perm[i] = v;
		}
		int64_t k = permute(n, perm, trace, blocked);
		if (k < 0) {
			printf("blocked %u %u\n", blocked[0], blocked[1]);
		} else {
			printf("ok");
			for (int64_t i = 0; i < k; i++)
				printf(" %u", trace[i]);
			printf("\n");
		}
	}
	return 0;
}

int main(int argc, char **argv)
{
	if (argc == 2 && strcmp(argv[1], "gen") == 0)
		return gen();
	if (argc == 2 && strcmp(argv[1], "run") == 0)
		return run();
	fprintf(stderr, "usage: harness gen|run\n");
	return 2;
}
