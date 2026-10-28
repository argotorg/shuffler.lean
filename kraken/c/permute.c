#include <stdint.h>

#define MAX_SWAP_DEPTH 16

/*
 * perm[i] is the destination of the slot at position i. Position n - 1 is the
 * top of the stack. permute writes the depth of each swap to trace and returns
 * the number of swaps. If a swap is deeper than MAX_SWAP_DEPTH, permute writes
 * the offset and the excess of that swap to blocked and returns -1.
 *
 * n <= 1024, perm holds a permutation of 0 .. n - 1 (n words), trace has room
 * for 2n bytes, and blocked has room for 2 words.
 */
int64_t permute(uint64_t n, uint16_t *perm, uint8_t *trace, uint16_t *blocked)
{
	if (n == 0)
		return 0;
	uint64_t top = n - 1;
	int64_t k = 0;
	for (;;) {
		uint64_t pos = perm[top];
		if (pos == top) {
			/* the last out-of-place position below the top */
			for (uint64_t i = 0; i < top; i++)
				if (perm[i] != i)
					pos = i;
			if (pos == top)
				return k;
		}
		uint64_t idx = top - pos;
		if (idx > MAX_SWAP_DEPTH) {
			blocked[0] = pos;
			blocked[1] = idx - MAX_SWAP_DEPTH;
			return -1;
		}
		trace[k++] = idx;
		uint16_t tmp = perm[top];
		perm[top] = perm[pos];
		perm[pos] = tmp;
	}
}
