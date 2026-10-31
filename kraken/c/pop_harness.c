/*
 * pop_harness: read "pop" cases of Fuzz/Oracle.lean, one per line as
 * "pop;STACK;TARGET;DESTS;VARS;COUNT" (Fuzz/pop_cases.sh), and print the result of emission_pop
 * for each, in the format of the oracle: "ok;STACK;OPS;DESTS;SOURCES;PEND" or "err". A slot is
 * v<id> (a Phi), l<id> (a Const), _ (junk) or R (the function return label); a destination or
 * position is an offset or "-" (NONE). STACK is the slots below m - COUNT, OPS the operations,
 * DESTS m_destinationOf of each slot of STACK, SOURCES m_positionOf of each target offset and
 * PEND m_pendingGenerations. It prints "bad input" for a line that it cannot read and
 * "invalid ..." if emission_pop writes an entry above m - COUNT or n, or an operation is not a pop.
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
enum { Pop = 2 };
enum { N = 1024 };

int64_t emission_pop(uint64_t m, uint64_t n, StackSlot *data, const StackSlot *target,
		     const uint64_t *dest, const uint8_t *spilled, uint64_t count, struct op *ops,
		     uint64_t *destinationOf, uint64_t *positionOf, uint64_t *pending);

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

static int run_line(char *line)
{
	static StackSlot data[N], target[N];
	static uint64_t dest[N], destinationOf[N + 1], positionOf[N + 1];
	static struct op ops[N + 2];
	uint8_t spilled[N] = { 0 };
	char *f[6], *s, *w;
	uint64_t m, n, k = 0, count, v, pending = 0xa5a5;
	if (!split(line, f, 6) || strcmp(f[0], "pop") != 0 || !slots(f[1], data, &m) || !slots(f[2], target, &n))
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
	if (!number(f[5], &count) || count > m + 1)
		return 0;
	memset(destinationOf, 0xa5, sizeof destinationOf);
	memset(positionOf, 0xa5, sizeof positionOf);
	int64_t const r = emission_pop(m, n, data, target, dest, spilled, count, ops, destinationOf, positionOf,
				       &pending);
	if (r == -2) {
		printf("err\n");
		return 1;
	}
	if (r != (int64_t)count) {
		printf("invalid: the result is %ld\n", r);
		return 1;
	}
	if (destinationOf[m - count] != 0xa5a5a5a5a5a5a5a5u || positionOf[n] != 0xa5a5a5a5a5a5a5a5u) {
		printf("invalid: an entry above the size is written\n");
		return 1;
	}
	for (uint64_t i = 0; i < count; i++)
		if (ops[i].kind != Pop || ops[i].depth != 0 || ops[i].slot.kind != Junk) {
			printf("invalid: operation %lu\n", i);
			return 1;
		}
	printf("ok;");
	for (uint64_t i = 0; i < m - count; i++) {
		if (i)
			putchar(' ');
		print_slot(data[i]);
	}
	printf(";");
	for (uint64_t i = 0; i < count; i++)
		printf(i ? " %s" : "%s", "POP");
	printf(";");
	for (uint64_t i = 0; i < m - count; i++) {
		if (i)
			putchar(' ');
		print_offset(destinationOf[i]);
	}
	printf(";");
	for (uint64_t j = 0; j < n; j++) {
		if (j)
			putchar(' ');
		print_offset(positionOf[j]);
	}
	printf(";%lu\n", pending);
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
