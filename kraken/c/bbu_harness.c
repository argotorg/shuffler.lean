/*
 * bbu_harness gen: print buildBottomUp inputs, one per line as
 * "m n s1 .. sm t1 .. tn d1 .. dm k v1 .. vk" (see test/BbuPr31Main.lean).
 * bbu_harness run: read such lines and print the result of build_bottom_up for
 * each, as "ok OPS | STACK", "blocked offset excess OPS | STACK", "assertion" or
 * "invalid ...". An operation is "s depth", "d depth" or "p code" for a push or a
 * load. STACK is the codes of the slots of data after the operations.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* the StackSlot and ShuffleOp of build_bottom_up.cpp */
typedef struct {
	uint32_t payload;
	uint8_t kind;
	uint8_t valueOpcode;
} StackSlot;
enum { Value = 0, Junk = 1, FunctionCallReturnLabel = 2, FunctionReturnLabel = 3 };
enum { Const = 0, Phi = 1, Unreachable = 5 };
struct op {
	uint8_t kind;
	uint8_t depth;
	StackSlot slot;
};
enum { Swap = 0, Dup = 1, Pop = 2, Push = 3, Load = 4, Store = 5 };

int64_t build_bottom_up(uint64_t m, uint64_t n, StackSlot *data,
			const StackSlot *target, const uint64_t *dest,
			const uint8_t *spilled, struct op *ops, uint64_t *blocked);

/*
 * 0 is junk, 1 the function return label, 2 + 2 * i the variable i (a Phi), 3 + 2 * i
 * the literal i (a Const). The padding bytes get `pad`.
 */
static StackSlot slot_of(uint64_t v, uint8_t pad)
{
	StackSlot s;
	memset(&s, pad, sizeof s);
	s.payload = v < 2 ? 0 : (v - 2) / 2;
	s.kind = v == 0 ? Junk : v == 1 ? FunctionReturnLabel : Value;
	s.valueOpcode = v < 2 ? Unreachable : v % 2 ? Const : Phi;
	return s;
}

static uint64_t code_of(StackSlot s)
{
	if (s.kind == Junk)
		return 0;
	if (s.kind == FunctionReturnLabel)
		return 1;
	return 2 + 2 * (uint64_t)s.payload + (s.valueOpcode == Const);
}

static int slot_eq(StackSlot a, StackSlot b)
{
	return a.payload == b.payload && a.kind == b.kind && a.valueOpcode == b.valueOpcode;
}

/*
 * The rules of ShuffleOp and Stack::push: a swap or dup has a depth in 1..16 and
 * the slot of StackSlot::makeJunk; a push or load has depth 0, a load holds a
 * spilled variable and a push a literal or junk. There are no other kinds.
 */
static int op_ok(struct op o, const uint8_t *spilled)
{
	StackSlot const junk = { 0, Junk, Unreachable };
	int const variable = o.slot.kind == Value && o.slot.valueOpcode != Const;
	switch (o.kind) {
	case Swap:
	case Dup:
		return 1 <= o.depth && o.depth <= 16 && slot_eq(o.slot, junk);
	case Load:
		return o.depth == 0 && variable && spilled[o.slot.payload];
	case Push:
		return o.depth == 0 && !variable && o.slot.kind != FunctionReturnLabel;
	default:
		return 0;
	}
}

/*
 * Apply the ops to the m slots of `stack`, which has room for n slots, as
 * ShuffleTrace's apply does, and return the new size, or UINT64_MAX if an op
 * reaches below the bottom or above n. A dup with depth d copies the slot at
 * depth d - 1.
 */
static uint64_t replay(StackSlot *stack, uint64_t m, uint64_t n, const struct op *ops, int64_t j)
{
	for (int64_t i = 0; i < j; i++) {
		struct op const o = ops[i];
		if (o.kind == Swap ? o.depth >= m : m == n || (o.kind == Dup && o.depth > m))
			return UINT64_MAX;
		if (o.kind == Swap) {
			StackSlot const t = stack[m - 1];
			stack[m - 1] = stack[m - 1 - o.depth];
			stack[m - 1 - o.depth] = t;
		} else if (o.kind == Dup) {
			stack[m] = stack[m - o.depth];
			m++;
		} else {
			stack[m++] = o.slot;
		}
	}
	return m;
}

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

/* State.Valid.labels_bound: replace each function return label that no source slot is bound for with junk */
static void bind_labels(struct state *s)
{
	int bound[1024] = { 0 };
	for (int i = 0; i < s->m; i++)
		bound[s->dest[i]] = 1;
	for (int j = 0; j < s->n; j++)
		if (s->target[j] == 1 && !bound[j])
			s->target[j] = 0;
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

/*
 * Give the values from position i on (the sources, then the targets) each value:
 * junk, the return label, one of the `lits` literals so far or a new one, one of
 * the `vars` variables so far or a new one, which is spilled or not. Thus the
 * values are all values up to a renaming of the literals and the variables.
 */
static void all_values(struct state *s, int i, int lits, int vars)
{
	if (i == s->m + s->n) {
		all_dests(s, 0, 0);
		return;
	}
	uint32_t *v = i < s->m ? &s->source[i] : &s->target[i - s->m];
	*v = 0;
	all_values(s, i + 1, lits, vars);
	*v = 1;
	all_values(s, i + 1, lits, vars);
	for (int l = 0; l <= lits; l++) {
		*v = 3 + 2 * l;
		all_values(s, i + 1, l < lits ? lits : lits + 1, vars);
	}
	for (int x = 0; x < vars; x++) {
		*v = 2 + 2 * x;
		all_values(s, i + 1, lits, vars);
	}
	*v = 2 + 2 * vars;
	all_values(s, i + 1, lits, vars + 1);
	s->spills[s->k++] = vars;
	all_values(s, i + 1, lits, vars + 1);
	s->k--;
}

/* every input with m <= n <= nmax: all_values with every injection as dest */
static void all_small(int nmax)
{
	struct state s = { .k = 0 };
	for (s.n = 0; s.n <= nmax; s.n++)
		for (s.m = 0; s.m <= s.n; s.m++)
			all_values(&s, 0, 0, 0);
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

/* a random permutation of 0 .. n - 1 */
static void shuffle(int *p, int n)
{
	for (int j = 0; j < n; j++)
		p[j] = j;
	for (int j = n - 1; j > 0; j--) {
		int r = next() % (j + 1), t = p[j];
		p[j] = p[r];
		p[r] = t;
	}
}

/* In 7 of 8 states the function return labels are bound (State.Valid.labels_bound). */
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
	shuffle(p, s.n);
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
	if (next() % 8)
		bind_labels(&s);
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
	shuffle(p, s.n);
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

/*
 * A state with m = n <= nmax, so that buildBottomUp starts the final permutation
 * at the first offset that is not final. The values come from few variables and
 * literals, so that many slots are equal. Each slot is bound for its own offset,
 * except that the slots of a window of up to 20 offsets at the top get a random
 * permutation, some pairs of equal slots exchange their destinations, and in 1 of
 * 4 states one pair of any slots exchanges them.
 */
static void perm_state(int nmax)
{
	struct state s;
	int vars = 1 + next() % 4, lits = next() % 3;
	s.n = s.m = next() % (nmax + 1);
	s.k = 0;
	for (int i = 0; i < s.m; i++)
		s.source[i] = random_value(vars, lits);
	for (int i = 0; i < s.m; i++)
		s.dest[i] = i;
	int w = next() % 21, p[20];
	if (w > s.n)
		w = s.n;
	shuffle(p, w);
	for (int i = 0; i < w; i++)
		s.dest[s.n - w + i] = s.n - w + p[i];
	for (int r = next() % 8; s.n && r > 0; r--) {
		int a = next() % s.n, b = next() % s.n, t = s.dest[a];
		if (s.source[a] != s.source[b] && (r > 1 || next() % 4))
			continue;
		s.dest[a] = s.dest[b];
		s.dest[b] = t;
	}
	for (int i = 0; i < s.m; i++)
		s.target[s.dest[i]] = next() % 4 ? s.source[i] : 0;
	print_state(&s);
}

/*
 * Every input with n <= 3, the valid states with n <= 4 of two literals, and
 * random states. All random states are valid, except that some do not bind each
 * function return label. The PR31 model takes about 0.2 s for a random state of
 * size 1024 and 4 s for a big state, so their counts are small.
 */
static int gen(void)
{
	const uint32_t lits[] = { 3, 5 };
	all_small(3);
	exhaustive(3, 4, lits, 2);
	for (int r = 0; r < 40000; r++)
		random_state(12, 16);
	for (int r = 0; r < 30000; r++)
		random_state(30, 40);
	for (int r = 0; r < 200; r++)
		random_state(256, 256);
	for (int r = 0; r < 500; r++)
		random_state(1024, 1024);
	for (int r = 0; r < 20000; r++)
		deep_state();
	for (int r = 0; r < 10000; r++)
		perm_state(40);
	for (int r = 0; r < 300; r++)
		perm_state(1024);
	for (int r = 0; r < 40; r++)
		big_state();
	return 0;
}

/*
 * Run build_bottom_up on slots with padding 0 and on slots with random padding,
 * and print "invalid ..." if
 * - the results differ,
 * - build_bottom_up writes data[n],
 * - an operation breaks op_ok,
 * - the ops reach below the bottom or above n slots, or end with other than n
 *   slots on ok,
 * - data does not hold the source after the ops, or
 * - on ok, if each source slot is bound for junk or its own value, a slot of
 *   data differs from a target slot that is not junk.
 */
static int run(void)
{
	uint64_t m, n, k;
	static uint64_t source[1024], target[1024], dest[1024];
	static StackSlot data[2][1025], targetSlots[2][1024], replayed[1024];
	static struct op ops[2][6 * 1024];
	StackSlot guard;
	memset(&guard, 0xa5, sizeof guard);
	while (scanf("%lu %lu", &m, &n) == 2) {
		uint8_t spilled[1024] = { 0 };
		uint64_t blocked[2][2];
		int64_t j[2];
		for (uint64_t i = 0; i < m; i++)
			if (scanf("%lu", &source[i]) != 1)
				return 1;
		for (uint64_t i = 0; i < n; i++)
			if (scanf("%lu", &target[i]) != 1)
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
		int overrun = 0;
		for (int r = 0; r < 2; r++) {
			for (uint64_t i = 0; i < m; i++)
				data[r][i] = slot_of(source[i], r ? next() : 0);
			data[r][n] = guard;
			for (uint64_t i = 0; i < n; i++)
				targetSlots[r][i] = slot_of(target[i], r ? next() : 0);
			memset(blocked[r], 0xa5, sizeof blocked[r]);
			j[r] = build_bottom_up(m, n, data[r], targetSlots[r], dest, spilled, ops[r], blocked[r]);
			overrun |= memcmp(&data[r][n], &guard, sizeof guard) != 0;
		}
		if (overrun) {
			printf("invalid: data[n] is written\n");
			continue;
		}
		if (j[0] != j[1] || (j[0] >= 0 && memcmp(blocked[0], blocked[1], sizeof blocked[0]))) {
			printf("invalid: the padding changes the result\n");
			continue;
		}
		if (j[0] == -2) {
			printf("assertion\n");
			continue;
		}
		if (j[0] < 0 || j[0] > (int64_t)(6 * n)) {
			printf("invalid: the result is %ld\n", j[0]);
			continue;
		}
		int64_t bad = -1;
		for (int64_t i = 0; i < j[0] && bad < 0; i++)
			if (!op_ok(ops[0][i], spilled) || ops[0][i].kind != ops[1][i].kind
			    || ops[0][i].depth != ops[1][i].depth || !slot_eq(ops[0][i].slot, ops[1][i].slot))
				bad = i;
		if (bad >= 0) {
			printf("invalid: operation %ld\n", bad);
			continue;
		}
		for (uint64_t i = 0; i < m; i++)
			replayed[i] = slot_of(source[i], 0);
		uint64_t const size = replay(replayed, m, n, ops[0], j[0]);
		/* the excess of a block is positive, so 0 means not blocked */
		int const isBlocked = blocked[0][1] != 0;
		if (size == UINT64_MAX || (!isBlocked && size != n)) {
			printf("invalid: the ops do not give n slots\n");
			continue;
		}
		if (!isBlocked && blocked[0][0] != 0) {
			printf("invalid: the offset of a result that is not blocked is %lu\n", blocked[0][0]);
			continue;
		}
		/* as from MappingBuilder: each source slot is bound for junk or its own value */
		int bound_equal = !isBlocked;
		for (uint64_t i = 0; i < m; i++)
			bound_equal &= target[dest[i]] == 0 || target[dest[i]] == source[i];
		for (uint64_t i = 0; i < size && bad < 0; i++)
			if (!slot_eq(data[0][i], replayed[i]) || !slot_eq(data[1][i], replayed[i])
			    || (bound_equal && target[i] != 0 && !slot_eq(data[0][i], targetSlots[0][i])))
				bad = i;
		if (bad >= 0) {
			printf("invalid: data slot %ld\n", bad);
			continue;
		}
		if (isBlocked)
			printf("blocked %lu %lu", blocked[0][0], blocked[0][1]);
		else
			printf("ok");
		for (int64_t i = 0; i < j[0]; i++) {
			struct op const o = ops[0][i];
			if (o.kind == Push || o.kind == Load)
				printf(" p %lu", code_of(o.slot));
			else
				printf(" %c %u", "sd"[o.kind], o.depth);
		}
		printf(" |");
		for (uint64_t i = 0; i < size; i++)
			printf(" %lu", code_of(data[0][i]));
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
