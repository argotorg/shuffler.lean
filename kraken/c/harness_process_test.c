#include "harness_process.h"
#include <sys/mman.h>

struct sample {
	struct call_outcome outcome;
	int write;
};

static int64_t returns(void *input)
{
	((struct sample *)input)->write = 7;
	return -2;
}

static int64_t exits_one(void *input)
{
	((struct sample *)input)->write = 11;
	exit(1);
}

static int64_t exits_two(void *input)
{
	((struct sample *)input)->write = 13;
	exit(2);
}

int main(void)
{
	struct sample *s = mmap(NULL, sizeof *s, PROT_READ | PROT_WRITE,
		MAP_SHARED | MAP_ANONYMOUS, -1, 0);
	if (s == MAP_FAILED)
		return 1;
	int const normal = call_in_child(returns, s, &s->outcome) &&
		s->outcome.returned && s->outcome.exit_status == 0 &&
		s->outcome.value == -2 && s->write == 7;
	int const assertion = call_in_child(exits_one, s, &s->outcome) &&
		!s->outcome.returned && s->outcome.exit_status == 1 && s->write == 11;
	int const other_exit = !call_in_child(exits_two, s, &s->outcome) &&
		!s->outcome.returned && s->outcome.exit_status == 2 && s->write == 13;
	munmap(s, sizeof *s);
	return normal && assertion && other_exit ? 0 : 1;
}
