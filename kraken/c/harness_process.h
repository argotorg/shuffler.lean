#ifndef HARNESS_PROCESS_H
#define HARNESS_PROCESS_H

#include <errno.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>

/* Each input runs in a child so exit(1) does not stop the input stream. */
static inline int run_in_child(int (*operation)(void *), void *input, const char *assertion)
{
	if (fflush(NULL) != 0)
		return 0;
	pid_t const child = fork();
	if (child < 0) {
		perror("fork");
		return 0;
	}
	if (child == 0) {
		if (!operation(input))
			puts("bad input");
		_Exit(fflush(stdout) == 0 ? 0 : 2);
	}
	int status;
	while (waitpid(child, &status, 0) < 0)
		if (errno != EINTR) {
			perror("waitpid");
			return 0;
		}
	if (WIFEXITED(status) && WEXITSTATUS(status) == 0)
		return 1;
	if (WIFEXITED(status) && WEXITSTATUS(status) == 1)
		return puts(assertion) >= 0;
	fputs("invalid: child process failed\n", stderr);
	return 0;
}

struct call_outcome {
	int returned;
	int exit_status;
	int64_t value;
};

/* The outcome and all output buffers must be in shared memory. */
static inline int call_in_child(int64_t (*operation)(void *), void *input, struct call_outcome *out)
{
	*out = (struct call_outcome){ 0 };
	if (fflush(NULL) != 0)
		return 0;
	pid_t const child = fork();
	if (child < 0) {
		perror("fork");
		return 0;
	}
	if (child == 0) {
		out->value = operation(input);
		out->returned = 1;
		_Exit(0);
	}
	int status;
	while (waitpid(child, &status, 0) < 0)
		if (errno != EINTR) {
			perror("waitpid");
			return 0;
		}
	if (WIFEXITED(status)) {
		out->exit_status = WEXITSTATUS(status);
		if ((out->returned && out->exit_status == 0) || (!out->returned && out->exit_status == 1))
			return 1;
	}
	fputs("invalid: child process failed\n", stderr);
	return 0;
}

#endif
