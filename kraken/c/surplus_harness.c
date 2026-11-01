/*
 * surplus_harness: read "surplus" cases of Fuzz/Oracle.lean, one per line as
 * "surplus;STACK;TARGET;DESTS;VARS" (Fuzz/surplus_cases.sh), and print the result of remove_surplus
 * for each, in the format of the oracle: "ok;STACK;OPS;DESTS", "blocked OFFSET EXCESS;STACK;OPS;DESTS"
 * or "err". A slot is v<id> (a Phi), l<id> (a Const), _ (junk) or R (the function return label); a
 * destination is an offset or "-" (NONE). STACK is the slots below the height, OPS the operations
 * and DESTS the destination of each slot of STACK. It prints "bad input" for a line that it cannot
 * read and "invalid ..." if remove_surplus writes a slot, an operation or a destination above its
 * bound, the height is above m, or an operation is not a pop or a swap.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* the types in shuffler/StackSlot.h and shuffler/ShuffleTrace.h */
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
enum { Swap = 0, Pop = 2 };
enum { N = 1024 };

int64_t remove_surplus(uint64_t m, uint64_t n, StackSlot *data, const StackSlot *target, uint64_t *dest,
		       const uint8_t *spilled, uint64_t idCount, struct op *ops, uint64_t *blocked,
		       uint64_t *height);

/* the fields of a line, split at ';' in place */
static int split(char *line, char **fields, int k)
{
	int i = 0;
	fields[i++] = line;
	for (char *c = line; *c; c++)
		if (*c == ';') {
			if (i == k)
				return 0;
			*c = 0;
			fields[i++] = c + 1;
		}
	return i == k;
}

/* the next word of *s, or NULL at the end */
static char *word(char **s)
{
	while (**s == ' ')
		(*s)++;
	if (!**s)
		return NULL;
	char *w = *s;
	while (**s && **s != ' ')
		(*s)++;
	if (**s)
		*(*s)++ = 0;
	return w;
}

static int number(const char *w, uint64_t *v)
{
	char *end;
	if (*w < '0' || *w > '9')
		return 0;
	*v = strtoull(w, &end, 10);
	return *end == 0;
}

static int slot_of(const char *w, StackSlot *s)
{
	uint64_t id;
	memset(s, 0, sizeof *s);
	if (strcmp(w, "_") == 0) {
		s->kind = Junk;
		s->valueOpcode = Unreachable;
		return 1;
	}
	if (strcmp(w, "R") == 0) {
		s->kind = FunctionReturnLabel;
		s->valueOpcode = Unreachable;
		return 1;
	}
	if ((w[0] != 'v' && w[0] != 'l') || !number(w + 1, &id) || id > UINT32_MAX)
		return 0;
	s->payload = (uint32_t)id;
	s->kind = Value;
	s->valueOpcode = w[0] == 'v' ? Phi : Const;
	return 1;
}

static void print_slot(StackSlot s)
{
	if (s.kind == Junk)
		printf("_");
	else if (s.kind == FunctionReturnLabel)
		printf("R");
	else
		printf("%c%u", s.valueOpcode == Const ? 'l' : 'v', s.payload);
}

static void print_offset(uint64_t d)
{
	if (d == UINT64_MAX)
		printf("-");
	else
		printf("%lu", d);
}

/* the slots of s, at most N */
static int slots(char *s, StackSlot *out, uint64_t *k)
{
	*k = 0;
	for (char *w; (w = word(&s));)
		if (*k == N || !slot_of(w, &out[(*k)++]))
			return 0;
	return 1;
}

static int is_guard_slot(StackSlot s)
{
	return s.payload == 0xa5a5a5a5u && s.kind == 0xa5 && s.valueOpcode == 0xa5;
}

static int run_line(char *line)
{
	static StackSlot data[N + 1], target[N];
	static uint64_t dest[N + 1];
	static struct op ops[2 * N + 1];
	static uint8_t spilled[N];
	char *f[5], *s, *w;
	uint64_t m, n, k = 0, v, blocked[2] = { 0xeeee, 0xeeee }, height = 0xa5a5;
	memset(data, 0xa5, sizeof data);
	memset(dest, 0xa5, sizeof dest);
	memset(ops, 0xa5, sizeof ops);
	memset(spilled, 0, sizeof spilled);
	if (!split(line, f, 5) || strcmp(f[0], "surplus") != 0 || !slots(f[1], data, &m) || !slots(f[2], target, &n))
		return 0;
	for (s = f[3]; (w = word(&s)); k++)
		if (k == m || !(strcmp(w, "-") == 0 ? (dest[k] = UINT64_MAX, 1) : number(w, &dest[k])))
			return 0;
	if (k != m)
		return 0;
	for (s = f[4]; (w = word(&s));) {
		if (!number(w, &v) || v >= N)
			return 0;
		spilled[v] = 1;
	}
	int64_t const r = remove_surplus(m, n, data, target, dest, spilled, N, ops, blocked, &height);
	if (r == -2) {
		printf("err\n");
		return 1;
	}
	if (r < 0 || (uint64_t)r > 2 * m || height > m) {
		printf("invalid: the result is %ld, the height %lu\n", r, height);
		return 1;
	}
	if (!is_guard_slot(data[m]) || dest[m] != 0xa5a5a5a5a5a5a5a5u || ops[r].kind != 0xa5) {
		printf("invalid: an entry above the bound is written\n");
		return 1;
	}
	for (int64_t i = 0; i < r; i++)
		if (!((ops[i].kind == Pop && ops[i].depth == 0) || ops[i].kind == Swap) || ops[i].slot.kind != Junk) {
			printf("invalid: operation %ld\n", i);
			return 1;
		}
	if (blocked[0] == 0 && blocked[1] == 0)
		printf("ok;");
	else
		printf("blocked %lu %lu;", blocked[0], blocked[1]);
	for (uint64_t i = 0; i < height; i++) {
		if (i)
			putchar(' ');
		print_slot(data[i]);
	}
	printf(";");
	for (int64_t i = 0; i < r; i++) {
		if (i)
			putchar(' ');
		if (ops[i].kind == Pop)
			printf("POP");
		else
			printf("SWAP%u", ops[i].depth);
	}
	printf(";");
	for (uint64_t i = 0; i < height; i++) {
		if (i)
			putchar(' ');
		print_offset(dest[i]);
	}
	printf("\n");
	return 1;
}

int main(void)
{
	static char line[1 << 16];
	while (fgets(line, sizeof line, stdin)) {
		line[strcspn(line, "\n")] = 0;
		if (!run_line(line))
			printf("bad input\n");
	}
	return 0;
}
