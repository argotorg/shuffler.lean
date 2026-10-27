/* SPDX-License-Identifier: GPL-3.0-or-later */
#ifndef PERMUTE_ALIVE2_OBSERVATION_H
#define PERMUTE_ALIVE2_OBSERVATION_H
struct Observation {
    unsigned status;
    unsigned data[EQUIV_N];
    unsigned count;
    unsigned blocked_offset;
    unsigned blocked_excess;
    unsigned trace[2U * EQUIV_N];
};
#endif
