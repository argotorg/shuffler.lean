#include <stdint.h>

/*
 * Shuffler.Emission.buildBottomUp. Each function mirrors a part of the Lean
 * code and is a separate unit of the Kraken proof. The functions keep the Lean
 * checks that depend on other functions, and return ASSERTION if one fails.
 */

#define MAX_SWAP_DEPTH 16
#define MAX_DUP_DEPTH 15
#define UNIT __attribute__((noinline, noclone))

#define BLOCKED (-1)
#define ASSERTION (-2)
#define FINISH (-3)

/* an operation and its depth or value */
enum { SWAP, DUP, PUSH };
struct op {
	uint64_t kind, arg;
};

int64_t permute(uint64_t n, uint16_t *perm, uint8_t *trace, uint16_t *blocked);

/*
 * Values are numbers: 0 is a wildcard, 1 a function return label, 2 + 2 id a
 * variable and 3 + 2 id a literal. dest[i] is the target offset of stack[i].
 */
struct st {
	uint64_t len, pending, nops, n;
	const uint64_t *target;
	const uint8_t *spilled;
	struct op *ops;
	uint64_t *blocked;
	uint64_t stack[1024], dest[1024];
};

static int is_free(uint64_t v)
{
	return v == 0 || (v & 1 && v != 1);
}

static int is_spilled(const struct st *s, uint64_t v)
{
	return v >= 2 && !(v & 1) && s->spilled[(v - 2) / 2];
}

/* the excess is positive at every call */
static int64_t block(struct st *s, uint64_t pos, uint64_t excess)
{
	s->blocked[0] = pos;
	s->blocked[1] = excess;
	return BLOCKED;
}

/* State.positionOf: the position of the slot bound for d, or -1 */
UNIT static int64_t position_of(const struct st *s, uint64_t d)
{
	for (uint64_t i = 0; i < s->len; i++)
		if (s->dest[i] == d)
			return i;
	return -1;
}

/* Stack.shallowestCopyPosition: the last position that holds v, or -1 */
UNIT static int64_t shallowest_copy(const struct st *s, uint64_t v)
{
	for (uint64_t i = s->len; i > 0; i--)
		if (s->stack[i - 1] == v)
			return i - 1;
	return -1;
}

/* State.push and State.dup: add v bound for d on top, with the operation op */
UNIT static int64_t add(struct st *s, uint64_t v, uint64_t d, uint64_t kind, uint64_t arg)
{
	if (position_of(s, d) >= 0)
		return ASSERTION;
	s->ops[s->nops].kind = kind;
	s->ops[s->nops].arg = arg;
	s->nops++;
	s->stack[s->len] = v;
	s->dest[s->len] = d;
	s->len++;
	return 0;
}

static void swap_destinations(struct st *s, uint64_t a, uint64_t b)
{
	uint64_t t = s->dest[a];
	s->dest[a] = s->dest[b];
	s->dest[b] = t;
}

/* State.swapWith */
UNIT static int64_t swap_with(struct st *s, uint64_t pos)
{
	if (pos >= s->len || s->dest[pos] == pos)
		return ASSERTION;
	uint64_t top = s->len - 1, depth = top - pos;
	if (depth < 1 || depth > MAX_SWAP_DEPTH)
		return ASSERTION;
	s->ops[s->nops].kind = SWAP;
	s->ops[s->nops].arg = depth;
	s->nops++;
	uint64_t t = s->stack[pos];
	s->stack[pos] = s->stack[top];
	s->stack[top] = t;
	swap_destinations(s, pos, top);
	return 0;
}

/* State.produce, for d < n */
UNIT static int64_t produce(struct st *s, uint64_t d)
{
	uint64_t v = s->target[d];
	int64_t copy = shallowest_copy(s, v);
	int64_t r;
	if (v == 0)
		r = add(s, v, d, PUSH, v);
	else if (copy >= 0 && s->len - 1 - copy <= MAX_DUP_DEPTH)
		r = add(s, v, d, DUP, s->len - copy);
	else if (is_free(v) || is_spilled(s, v))
		r = add(s, v, d, PUSH, v);
	else if (copy >= 0)
		return block(s, copy, s->len - 1 - copy - MAX_DUP_DEPTH);
	else
		return ASSERTION;
	if (r < 0)
		return r;
	if (position_of(s, d) != (int64_t)s->len - 1)
		return ASSERTION;
	if (s->pending != 0)
		s->pending--;
	return 0;
}

/* State.generate */
UNIT static int64_t generate(struct st *s, uint64_t d)
{
	if (d >= s->n)
		return ASSERTION;
	int64_t r = produce(s, d);
	if (r < 0)
		return r;
	if (d + 1 < s->len && s->dest[d] != d) {
		uint64_t top = s->len - 1;
		if (s->stack[d] == s->stack[top])
			swap_destinations(s, d, top);
		else if (top - d <= MAX_SWAP_DEPTH)
			return swap_with(s, d);
	}
	return 0;
}

/*
 * The urgentToDup scan of buildBottomUp.loop: the first offset at or above t
 * that is urgent, n if there is none, or BLOCKED.
 */
UNIT static int64_t urgent(struct st *s, uint64_t t)
{
	int64_t u = s->n;
	for (uint64_t d = t; d < s->n; d++) {
		if (position_of(s, d) >= 0)
			continue;
		uint64_t v = s->target[d];
		if (is_free(v) || is_spilled(s, v))
			continue;
		int64_t copy = shallowest_copy(s, v);
		if (copy < 0)
			continue;
		uint64_t depth = s->len - 1 - copy;
		if (depth > MAX_DUP_DEPTH)
			return block(s, copy, depth - MAX_DUP_DEPTH);
		if (depth == MAX_DUP_DEPTH && (uint64_t)copy != t && u == (int64_t)s->n)
			u = d;
	}
	return u;
}

/*
 * The boundForTarget branch of buildBottomUp.loop, for the slot b bound for t:
 * 0 if t is done, 1 if the slot for t is on top, or an error.
 */
UNIT static int64_t take_bound(struct st *s, uint64_t t, uint64_t b)
{
	if (b < t)
		return ASSERTION;
	uint64_t pos = b;
	if (s->stack[t] == s->stack[b])
		pos = t;
	else
		for (uint64_t c = s->len - 1; c > b; c--)
			if (s->stack[c] == s->stack[b] && s->dest[c] != c) {
				pos = c;
				break;
			}
	swap_destinations(s, pos, b);
	if (pos == t)
		return 0;
	if (pos != s->len - 1) {
		uint64_t depth = s->len - 1 - pos;
		if (depth > MAX_SWAP_DEPTH)
			return block(s, pos, depth - MAX_SWAP_DEPTH);
		int64_t r = swap_with(s, pos);
		if (r < 0)
			return r;
	}
	return 1;
}

/*
 * One iteration of buildBottomUp.loop at t < n: the next t, FINISH if all
 * slots are generated, or an error.
 */
UNIT static int64_t step(struct st *s, uint64_t t)
{
	if (t < s->len && s->dest[t] == t)
		return t + 1;
	if (s->pending == 0)
		return FINISH;
	int64_t u = urgent(s, t);
	if (u < 0)
		return u;
	if ((uint64_t)u != s->n && (uint64_t)u != t && s->len < t + MAX_SWAP_DEPTH) {
		int64_t r = generate(s, u);
		return r < 0 ? r : (int64_t)t;
	}
	uint64_t top = s->len;
	if ((uint64_t)u == s->n && top > t && top < s->n && position_of(s, top) < 0 &&
	    top < t + MAX_SWAP_DEPTH) {
		int64_t r = generate(s, top);
		return r < 0 ? r : (int64_t)t;
	}
	int64_t b = position_of(s, t);
	if (b >= 0) {
		int64_t r = take_bound(s, t, b);
		if (r < 0)
			return r;
		if (r == 0)
			return t + 1;
	} else {
		int64_t r = generate(s, t);
		if (r < 0)
			return r;
		if (t < s->len && s->dest[t] == t)
			return t + 1;
	}
	if (t >= s->len || s->dest[t] == t)
		return ASSERTION;
	if (t != s->len - 1) {
		uint64_t depth = s->len - 1 - t;
		if (depth > MAX_SWAP_DEPTH)
			return block(s, t, depth - MAX_SWAP_DEPTH);
		int64_t r = swap_with(s, t);
		if (r < 0)
			return r;
	}
	return t + 1;
}

/* the final permutation; len = n and dest is a permutation */
UNIT static int64_t finish(struct st *s)
{
	uint16_t perm[1024];
	uint8_t trace[2048];
	uint16_t blocked[2];
	for (uint64_t i = 0; i < s->len; i++)
		perm[i] = s->dest[i];
	int64_t k = permute(s->len, perm, trace, blocked);
	if (k < 0)
		return block(s, blocked[0], blocked[1]);
	for (int64_t i = 0; i < k; i++) {
		s->ops[s->nops].kind = SWAP;
		s->ops[s->nops].arg = trace[i];
		s->nops++;
	}
	return s->nops;
}

/*
 * Build the target bottom-up from the source stack, as Shuffler.Emission.buildBottomUp.
 * dest[i] is the target offset of source slot i and spilled[id] is 1 if
 * variable id is spilled. Write the operations to ops and return their number,
 * write the blocked offset and excess and return BLOCKED, or return ASSERTION.
 *
 * m <= n <= 1024, dest holds distinct offsets below n, every variable id in
 * target is an index of spilled, and ops has room for 6n entries.
 */
int64_t build_bottom_up(uint64_t m, uint64_t n, const uint64_t *source,
			const uint64_t *target, const uint64_t *dest,
			const uint8_t *spilled, struct op *ops, uint64_t *blocked)
{
	struct st s;
	s.len = m;
	s.pending = n - m;
	s.nops = 0;
	s.n = n;
	s.target = target;
	s.spilled = spilled;
	s.ops = ops;
	s.blocked = blocked;
	for (uint64_t i = 0; i < m; i++) {
		s.stack[i] = source[i];
		s.dest[i] = dest[i];
	}
	for (uint64_t t = 0; t < n;) {
		int64_t r = step(&s, t);
		if (r == FINISH) {
			if (s.len != n)
				return ASSERTION;
			return finish(&s);
		}
		if (r < 0)
			return r;
		t = r;
	}
	return s.len == n ? (int64_t)s.nops : ASSERTION;
}
