/* SPDX-License-Identifier: GPL-3.0-or-later */
#include <klee/klee.h>
#include "observation.h"

void observe_core(struct Observation *, const unsigned *);
void observe_oracle(struct Observation *, const unsigned *);

int main(void)
{
    unsigned symbols[EQUIV_GROUP_COUNT];
    const unsigned groups[EQUIV_N] = EQUIV_VALUE_GROUPS;
    unsigned values[EQUIV_N];
    struct Observation core, oracle;
    klee_make_symbolic(symbols, sizeof(symbols), "symbols");
    for (unsigned i = 0; i < EQUIV_N; ++i)
        values[i] = symbols[groups[i]];
    observe_core(&core, values);
    observe_oracle(&oracle, values);
    klee_assert(core.status == oracle.status);
    klee_assert(core.count == oracle.count);
    klee_assert(core.count <= 2U * EQUIV_N);
    klee_assert(core.blocked_offset == oracle.blocked_offset);
    klee_assert(core.blocked_excess == oracle.blocked_excess);
    for (unsigned i = 0; i < EQUIV_N; ++i)
        klee_assert(core.data[i] == oracle.data[i]);
    for (unsigned i = 0; i < core.count; ++i)
        klee_assert(core.trace[i] == oracle.trace[i]);
    return 0;
}
