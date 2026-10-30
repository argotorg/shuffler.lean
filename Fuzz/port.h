// The kraken/c port in the differential fuzzer: runs the compiled port (kraken/c/*.S) on a case line of
// Fuzz/Oracle.lean and prints its result in the result format of Fuzz/Oracle.lean.
#pragma once

#include <optional>
#include <string>

namespace port
{

/// The result of the port on a case, and the part of the model result that the port gives
struct Check
{
	std::string port;
	std::string model;
};

/// Runs the port on the case `_line`, whose model result is `_model`. Nullopt if the port has no unit for the kind
/// of the case. Throws std::invalid_argument if the case is not in the domain of the unit.
std::optional<Check> check(std::string const& _line, std::string const& _model);

}
