/* SPDX-License-Identifier: GPL-3.0-or-later */
/* Replay retained inputs through the unchanged guided test callback. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int LLVMFuzzerTestOneInput(const uint8_t *, size_t);

int main(int argc, char **argv)
{
    for (int i = 1; i < argc; i++) {
        FILE *input = fopen(argv[i], "rb");
        if (input == NULL || fseek(input, 0, SEEK_END) != 0) {
            perror(argv[i]);
            return EXIT_FAILURE;
        }
        long length = ftell(input);
        if (length < 0 || length > 1048576L || fseek(input, 0, SEEK_SET) != 0) {
            fputs("invalid corpus file size\n", stderr);
            fclose(input);
            return EXIT_FAILURE;
        }
        size_t size = (size_t)length;
        uint8_t *bytes = malloc(size + 1U);
        if (bytes == NULL) {
            fclose(input);
            return EXIT_FAILURE;
        }
        size_t count = fread(bytes, 1U, size, input);
        int closed = fclose(input);
        if (count != size || closed != 0) {
            fputs("cannot read corpus file\n", stderr);
            free(bytes);
            return EXIT_FAILURE;
        }
        LLVMFuzzerTestOneInput(bytes, size);
        free(bytes);
    }
    return EXIT_SUCCESS;
}
