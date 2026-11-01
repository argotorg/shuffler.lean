#pragma once

#include <cstdint>

/// InstOpcode (SSACFGTypes.h): only the opcodes used by the freestanding shuffler
enum class InstOpcode : std::uint8_t { Const = 0, Unreachable = 5 };
