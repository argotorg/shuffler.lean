/*
 * bbu_harness gen: print valid buildBottomUp states, one per line as
 * "m n s1 .. sm t1 .. tn d1 .. dm k v1 .. vk" (see test/BuildBottomUpMain.lean).
 * bbu_harness run: read such lines and print the result of build_bottom_up for
 * each, as "ok op1 .. opj", "blocked offset excess" or "assertion". ops holds
 * the kind and the argument of each operation.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int64_t build_bottom_up(uint64_t m, uint64_t n, const uint64_t *source,
			const uint64_t *target, const uint64_t *dest,
			const uint8_t *spilled, uint64_t *ops, uint64_t *blocked);

struct state {
	int m, n, k;
	uint32_t source[1024], target[1024];
	int dest[1024], spills[1024];
};

/* Not isSpilled: test/bin_objdump.sh finds the code by that name. */
static int in_spills(const struct state *s, uint32_t v)
{
	if (v < 2 || v % 2)
		return 0;
	for (int i = 0; i < s->k; i++)
		if ((uint32_t)s->spills[i] == (v - 2) / 2)
			return 1;
	return 0;
}

/* a literal or wildcard, a spilled variable or a value on the source stack */
static int available(const struct state *s, uint32_t v)
{
	if (v == 0 || (v % 2 && v != 1) || in_spills(s, v))
		return 1;
	for (int i = 0; i < s->m; i++)
		if (s->source[i] == v)
			return 1;
	return 0;
}

static int valid(const struct state *s)
{
	for (int j = 0; j < s->n; j++)
		if (!available(s, s->target[j]))
			return 0;
	return 1;
}

static void print_state(const struct state *s)
{
	printf("%d %d", s->m, s->n);
	for (int i = 0; i < s->m; i++)
		printf(" %u", s->source[i]);
	for (int j = 0; j < s->n; j++)
		printf(" %u", s->target[j]);
	for (int i = 0; i < s->m; i++)
		printf(" %d", s->dest[i]);
	printf(" %d", s->k);
	for (int i = 0; i < s->k; i++)
		printf(" %d", s->spills[i]);
	printf("\n");
}

/* every injection of the m sources into the n targets */
static void all_dests(struct state *s, int i, int used)
{
	if (i == s->m) {
		print_state(s);
		return;
	}
	for (int d = 0; d < s->n; d++) {
		if (used & 1 << d)
			continue;
		s->dest[i] = d;
		all_dests(s, i + 1, used | 1 << d);
	}
}

/* every valid state with m <= mmax, n <= nmax, values from alpha and no spills */
static void exhaustive(int mmax, int nmax, const uint32_t *alpha, int na)
{
	struct state s = { .k = 0 };
	for (s.m = 0; s.m <= mmax; s.m++)
		for (s.n = s.m; s.n <= nmax; s.n++) {
			int total = 1;
			for (int i = 0; i < s.m + s.n; i++)
				total *= na;
			for (int c = 0; c < total; c++) {
				int r = c;
				for (int i = 0; i < s.m; i++, r /= na)
					s.source[i] = alpha[r % na];
				for (int j = 0; j < s.n; j++, r /= na)
					s.target[j] = alpha[r % na];
				if (valid(&s))
					all_dests(&s, 0, 0);
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

/* a random value from `vars` variables, `lits` literals, a wildcard and a return label */
static uint32_t random_value(int vars, int lits)
{
	int r = next() % (vars + lits + 2);
	if (r < vars)
		return 2 + 2 * r;
	if (r < vars + lits)
		return 3 + 2 * (r - vars);
	return r - vars - lits;
}

static void random_state(int mmax, int nmax)
{
	struct state s;
	int vars = 1 + next() % 8, lits = 1 + next() % 3;
	s.n = next() % (nmax + 1);
	s.m = next() % ((s.n < mmax ? s.n : mmax) + 1);
	s.k = 0;
	for (int v = 0; v < vars; v++)
		if (next() % 4 == 0)
			s.spills[s.k++] = v;
	for (int i = 0; i < s.m; i++)
		s.source[i] = random_value(vars, lits);
	int p[1024];
	for (int j = 0; j < s.n; j++)
		p[j] = j;
	for (int j = s.n - 1; j > 0; j--) {
		int r = next() % (j + 1), t = p[j];
		p[j] = p[r];
		p[r] = t;
	}
	for (int i = 0; i < s.m; i++)
		s.dest[i] = p[i];
	for (int j = 0; j < s.n; j++) {
		do
			s.target[j] = s.m && next() % 2 ? s.source[next() % s.m] : random_value(vars, lits);
		while (!available(&s, s.target[j]));
	}
	/* half of the bound targets hold the value of their source slot */
	for (int i = 0; i < s.m; i++)
		if (next() % 2)
			s.target[s.dest[i]] = s.source[i];
	print_state(&s);
}

/*
 * A state with 14 to 21 slots of few variables and n - m slots to dup, so that
 * copies are often at the maximum dup depth.
 */
static void deep_state(void)
{
	struct state s;
	int vars = 1 + next() % 4;
	s.m = 14 + next() % 8;
	s.n = s.m + 1 + next() % 6;
	s.k = 0;
	for (int i = 0; i < s.m; i++)
		s.source[i] = next() % 8 ? 2 + 2 * (next() % vars) : 3;
	int p[1024];
	for (int j = 0; j < s.n; j++)
		p[j] = j;
	for (int j = s.n - 1; j > 0; j--) {
		int r = next() % (j + 1), t = p[j];
		p[j] = p[r];
		p[r] = t;
	}
	for (int i = 0; i < s.m; i++)
		s.dest[i] = p[i];
	for (int j = 0; j < s.n; j++)
		s.target[j] = s.source[next() % s.m];
	for (int i = 0; i < s.m; i++)
		if (next() % 4)
			s.target[s.dest[i]] = s.source[i];
	print_state(&s);
}

/* a literal, a wildcard or a spilled variable */
static int pushable(const struct state *s, uint32_t v)
{
	return v == 0 || (v % 2 && v != 1) || in_spills(s, v);
}

/*
 * A state with 257 to 1024 slots. The source slots are bound for their own
 * offset, except near the top. In 3 of 4 states every value is pushable, so
 * that most states are ok. The other states may hold any value and bind any
 * source slot near its offset.
 */
static void big_state(void)
{
	struct state s;
	int vars = 1 + next() % 8, lits = 1 + next() % 3, any = next() % 4 == 0;
	s.n = 257 + next() % 768;
	s.m = next() % (s.n + 1);
	s.k = 0;
	for (int v = 0; v < vars; v++)
		if (next() % 8)
			s.spills[s.k++] = v;
	for (int i = 0; i < s.m; i++)
		do
			s.source[i] = random_value(vars, lits);
		while (!any && !pushable(&s, s.source[i]));
	int p[1024];
	for (int j = 0; j < s.n; j++)
		p[j] = j;
	for (int j = any || s.m < 12 ? 0 : s.m - 12; j + 1 < s.n; j++)
		if (next() % 16 == 0) {
			int r = j + 1 + next() % 8, t;
			if (r >= s.n)
				r = s.n - 1;
			t = p[j];
			p[j] = p[r];
			p[r] = t;
		}
	for (int i = 0; i < s.m; i++)
		s.dest[i] = p[i];
	for (int j = 0; j < s.n; j++)
		do
			s.target[j] = random_value(vars, lits);
		while (!available(&s, s.target[j]) || (!any && !pushable(&s, s.target[j])));
	for (int i = 0; i < s.m; i++)
		if (next() % 2)
			s.target[s.dest[i]] = s.source[i];
	print_state(&s);
}

static int gen(void)
{
	const uint32_t lits[] = { 3, 5 };
	const uint32_t mixed[] = { 0, 1, 2, 3 };
	exhaustive(3, 4, lits, 2);
	exhaustive(2, 3, mixed, 4);
	for (int r = 0; r < 3000; r++)
		random_state(12, 16);
	for (int r = 0; r < 3000; r++)
		random_state(30, 40);
	for (int r = 0; r < 200; r++)
		random_state(256, 256);
	for (int r = 0; r < 5000; r++)
		deep_state();
	for (int r = 0; r < 40; r++)
		big_state();
	return 0;
}

static int run(void)
{
	uint64_t m, n, k;
	while (scanf("%lu %lu", &m, &n) == 2) {
		uint64_t source[1024], target[1024], dest[1024], ops[2 * 6 * 1024];
		uint8_t spilled[1024] = { 0 };
		uint64_t blocked[2];
		for (uint64_t i = 0; i < m; i++)
			if (scanf("%lu", &source[i]) != 1)
				return 1;
		for (uint64_t j = 0; j < n; j++)
			if (scanf("%lu", &target[j]) != 1)
				return 1;
		for (uint64_t i = 0; i < m; i++)
			if (scanf("%lu", &dest[i]) != 1)
				return 1;
		if (scanf("%lu", &k) != 1)
			return 1;
		for (uint64_t i = 0; i < k; i++) {
			unsigned v;
			if (scanf("%u", &v) != 1)
				return 1;
			spilled[v] = 1;
		}
		int64_t j = build_bottom_up(m, n, source, target, dest, spilled, ops, blocked);
		if (j == -2) {
			printf("assertion\n");
			continue;
		}
		if (j < 0) {
			printf("blocked %lu %lu\n", blocked[0], blocked[1]);
			continue;
		}
		printf("ok");
		for (int64_t i = 0; i < j; i++)
			printf(" %c %lu", "sdp"[ops[2 * i]], ops[2 * i + 1]);
		printf("\n");
	}
	return 0;
}

int main(int argc, char **argv)
{
	if (argc == 2 && strcmp(argv[1], "gen") == 0)
		return gen();
	if (argc == 2 && strcmp(argv[1], "run") == 0)
		return run();
	fprintf(stderr, "usage: bbu_harness gen|run\n");
	return 2;
}
