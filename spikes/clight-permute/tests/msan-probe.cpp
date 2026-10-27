// SPDX-License-Identifier: GPL-3.0-or-later
// This separate program must fail under MSan. It is never linked into Permute.
#include <vector>

__attribute__((noinline)) static unsigned load(const unsigned *p) { return *p; }

int main(int argc, char **) {
    unsigned *p = new unsigned;
    if (argc > 1)
        *p = 123U; // Initialized control run, separate from the failing probe.
    std::vector<unsigned> values;
    values.push_back(load(p));
    unsigned value = values.front();
    delete p;
    return value == 123U ? 0 : 1;
}
