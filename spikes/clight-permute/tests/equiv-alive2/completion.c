/* SPDX-License-Identifier: GPL-3.0-or-later */
#include <klee/klee.h>

int checked_main(void);

int main(void)
{
    int result = checked_main();
    unsigned char completed;
    /* Each normal terminal witness must contain this final object. */
    klee_make_symbolic(&completed, sizeof(completed), "checks_completed");
    return result;
}
