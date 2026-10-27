// SPDX-License-Identifier: GPL-3.0-or-later
// The algorithm and stack operations come from hash-checked upstream files.
#include "test.h"

#include <range/v3/algorithm/set_algorithm.hpp>
#include <range/v3/algorithm/sort.hpp>
#include <range/v3/algorithm/stable_sort.hpp>
#include <range/v3/range/conversion.hpp>
#include <range/v3/view/chunk_by.hpp>
#include <range/v3/view/iota.hpp>
#include <range/v3/view/reverse.hpp>
#include <range/v3/view/transform.hpp>

#include <algorithm>
#include <cassert>
#include <compare>
#include <cstddef>
#include <iterator>
#include <limits>
#include <optional>
#include <utility>
#include <vector>

#define yulAssert(condition, ...) assert(condition)

namespace {
// Test values are equality/order-preserving unsigned IDs, not solc objects.
using StackData = std::vector<unsigned>;
#include "solc_types.inc"
using Destination = std::optional<StackOffset>;
#include "solc_mapping.inc"

// Only the swap depth is observable through the test interface.
struct ShuffleOp {
    std::size_t depth;
    static ShuffleOp swap(StackDepth depth) { return {depth.value}; }
};
using ShuffleTrace = std::vector<ShuffleOp>;

class Stack {
public:
    using Data = StackData;
    using Depth = StackDepth;
    using Offset = StackOffset;
    Stack(Data& data, ShuffleTrace* trace, std::size_t reach):
        m_data(&data), m_trace(trace), m_reachableStackDepth(reach) {}
#include "solc_stack_helpers.inc"
private:
    Data* m_data;
    ShuffleTrace* m_trace;
    std::size_t m_reachableStackDepth;
};

std::size_t constexpr empty = std::numeric_limits<std::size_t>::max();

class Emission {
public:
    struct Blocked { StackOffset offset; std::size_t excess; };
    Emission(unsigned n, unsigned const* data, unsigned const* permutation):
        m_data(data, data + n), m_mapping(n, n) {
        for (unsigned i = 0; i < n; ++i)
            m_mapping.bind(StackOffset{i}, StackOffset{permutation[i]});
    }
#include "solc_permute.inc"
#include "solc_emission_helpers.inc"
    std::size_t const m_maxSwapDepth = 16;
    StackData m_data;
    Mapping m_mapping;
    ShuffleTrace m_trace;
    Stack m_stack{m_data, &m_trace, m_maxSwapDepth};
};
}

extern "C" unsigned solc_permute(unsigned n, unsigned* data,
    unsigned const* permutation, unsigned* trace, unsigned* out) {
    assert(n > 0 && n <= TEST_LIMIT);
    Emission emission(n, data, permutation);
    auto blocked = emission.permute(
        std::vector<std::size_t>(permutation, permutation + n));
    assert(emission.m_trace.size() <= 2U * n);
    std::copy(emission.m_data.begin(), emission.m_data.end(), data);
    for (std::size_t i = 0; i < emission.m_trace.size(); ++i)
        trace[i] = static_cast<unsigned>(emission.m_trace[i].depth);
    out[0] = static_cast<unsigned>(emission.m_trace.size());
    out[1] = blocked ? static_cast<unsigned>(blocked->offset.value) : 0U;
    out[2] = blocked ? static_cast<unsigned>(blocked->excess) : 0U;
    return blocked ? 1U : 0U;
}
