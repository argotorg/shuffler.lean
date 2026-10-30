// The kraken/c port in the differential fuzzer. Each unit of the port has one entry in `units`: the kind of its
// cases, a runner that converts a case to the C interface of the port and its result to the result format of
// Fuzz/Oracle.lean, and the part of the model result that the C interface gives.
//
// The port is linked as the asm of kraken/c (the files that the Kraken proofs read), not compiled again.

#include "port.h"
#include "text.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

using fuzztext::join;
using fuzztext::parseNat;
using fuzztext::split;
using fuzztext::words;

namespace
{

/// StackSlot of kraken/c/build_bottom_up.cpp
struct Slot
{
	std::uint32_t payload;
	std::uint8_t kind;
	std::uint8_t valueOpcode;
	/// build_bottom_up does not read them
	std::uint8_t padding[2];
};
static_assert(sizeof(Slot) == 8 && offsetof(Slot, kind) == 4 && offsetof(Slot, valueOpcode) == 5);

enum SlotKind : std::uint8_t { Value = 0, Junk = 1, FunctionCallReturnLabel = 2, FunctionReturnLabel = 3 };
/// InstOpcode: a literal is a Const; a variable gets Phi, which is not Const
enum Opcode : std::uint8_t { Const = 0, Phi = 1, Unreachable = 5 };

/// ShuffleOp of kraken/c/build_bottom_up.cpp
struct Op
{
	std::uint8_t kind;
	std::uint8_t depth;
	/// the guard check of runBuildBottomUp compares whole entries, so the padding is a member
	std::uint8_t padding[2];
	Slot slot;
};
static_assert(sizeof(Op) == 12 && offsetof(Op, depth) == 1 && offsetof(Op, padding) == 2 && offsetof(Op, slot) == 4);

enum OpKind : std::uint8_t { Swap = 0, Dup = 1, Pop = 2, Push = 3, Load = 4, Store = 5 };

/// The port does not read the padding bytes, so they get a value that the encoding does not use
std::uint8_t constexpr padding = 0xa5;

/// "v" n is the variable n, "l" n the literal n, "_" junk and "R" the function return label
Slot parseSlot(std::string const& _token)
{
	if (_token == "_")
		return {0, Junk, Unreachable, {padding, padding}};
	if (_token == "R")
		return {0, FunctionReturnLabel, Unreachable, {padding, padding}};
	if (_token.size() > 1 && (_token[0] == 'v' || _token[0] == 'l'))
		return {parseNat(_token.substr(1)), Value, _token[0] == 'l' ? Const : Phi, {padding, padding}};
	throw std::invalid_argument("not a slot: " + _token);
}

std::vector<Slot> parseStack(std::string const& _s)
{
	std::vector<Slot> stack;
	for (std::string const& token: words(_s))
		stack.push_back(parseSlot(token));
	return stack;
}

/// The inverse of parseSlot; a slot that parseSlot does not give is shown in angle brackets, so that it differs
/// from each model result
std::string showSlot(Slot const _slot)
{
	if (_slot.kind == Junk && _slot.payload == 0 && _slot.valueOpcode == Unreachable)
		return "_";
	if (_slot.kind == FunctionReturnLabel && _slot.payload == 0 && _slot.valueOpcode == Unreachable)
		return "R";
	if (_slot.kind == Value && (_slot.valueOpcode == Const || _slot.valueOpcode == Phi))
		return (_slot.valueOpcode == Const ? "l" : "v") + std::to_string(_slot.payload);
	return "<slot " + std::to_string(_slot.kind) + " " + std::to_string(_slot.valueOpcode) + " " +
		std::to_string(_slot.payload) + ">";
}

std::string showStack(std::vector<Slot> const& _stack)
{
	std::vector<std::string> names;
	for (Slot const& slot: _stack)
		names.push_back(showSlot(slot));
	return join(names);
}

/// The operations in the format of Fuzz/Oracle.lean; an operation that the port must not give is shown in angle
/// brackets
std::string showOps(std::vector<Op> const& _ops)
{
	std::vector<std::string> result;
	for (Op const& op: _ops)
		switch (op.kind)
		{
		case Swap: result.push_back("SWAP" + std::to_string(op.depth)); break;
		case Dup: result.push_back("DUP" + std::to_string(op.depth)); break;
		case Push: result.push_back("PUSH:" + showSlot(op.slot)); break;
		case Load: result.push_back("LOAD:" + showSlot(op.slot)); break;
		default: result.push_back("<op " + std::to_string(op.kind) + ">"); break;
		}
	return join(result);
}

/// The fields of a model result before its last field: a state result without its destinations
std::string withoutLastField(std::string const& _model)
{
	std::size_t const last = _model.rfind(';');
	return last == std::string::npos ? _model : _model.substr(0, last);
}

}

extern "C" std::int64_t build_bottom_up(
	std::uint64_t m,
	std::uint64_t n,
	Slot* data,
	Slot const* target,
	std::uint64_t const* dest,
	std::uint8_t const* spilled,
	Op* ops,
	std::uint64_t* blocked
);

namespace
{

/// The maximal stack size of build_bottom_up (the EVM stack limit)
std::size_t constexpr maxStackSize = 1024;

/// A case "bottomup;" stack ";" target ";" dests ";" vars, in the domain of build_bottom_up: every slot has a
/// destination, the destinations are distinct and below the target size, and the target has at most
/// maxStackSize slots.
/// The result is "ok" or "blocked OFFSET EXCESS", the final stack and the operations, or "err".
std::string runBuildBottomUp(std::vector<std::string> const& _fields)
{
	if (_fields.size() != 4)
		throw std::invalid_argument("not a state");
	std::vector<Slot> const source = parseStack(_fields[0]);
	std::vector<Slot> const target = parseStack(_fields[1]);
	std::size_t const m = source.size();
	std::size_t const n = target.size();
	if (n > maxStackSize)
		throw std::invalid_argument("more target slots than the stack limit");
	std::vector<std::string> const destWords = words(_fields[2]);
	if (destWords.size() != m)
		throw std::invalid_argument("not one destination per slot: " + _fields[2]);
	std::vector<std::uint64_t> dest;
	std::vector<bool> bound(n);
	for (std::string const& word: destWords)
	{
		std::uint32_t const d = parseNat(word);
		if (d >= n || bound[d])
			throw std::invalid_argument("destination out of the target or bound twice: " + word);
		bound[d] = true;
		dest.push_back(d);
	}
	std::vector<std::uint32_t> spills;
	for (std::string const& word: words(_fields[3]))
		spills.push_back(parseNat(word));
	// spilled[id] for each variable id of the case
	std::uint32_t maxId = 0;
	for (std::vector<Slot> const* slots: {&source, &target})
		for (Slot const& slot: *slots)
			if (slot.kind == Value && slot.valueOpcode == Phi)
				maxId = std::max(maxId, slot.payload);
	for (std::uint32_t const id: spills)
		maxId = std::max(maxId, id);
	std::vector<std::uint8_t> spilled(std::size_t{maxId} + 1);
	for (std::uint32_t const id: spills)
		spilled[id] = 1;

	// build_bottom_up writes at most n slots and 6 n operations. A guard area after each buffer must stay as it is.
	std::size_t constexpr guard = 16;
	Slot const guardSlot{0xdeadbeef, 0xee, 0xee, {0xee, 0xee}};
	Op const guardOp{0xee, 0xee, {0xee, 0xee}, guardSlot};
	std::vector<Slot> data(n + guard, guardSlot);
	std::copy(source.begin(), source.end(), data.begin());
	std::vector<Op> ops(6 * n + guard, guardOp);
	std::uint64_t blocked[2] = {0xeeee, 0xeeee};
	std::int64_t const count =
		build_bottom_up(m, n, data.data(), target.data(), dest.data(), spilled.data(), ops.data(), blocked);
	auto const intact = [](auto const& _buffer, std::size_t const _from, auto const& _value) {
		return std::all_of(_buffer.begin() + static_cast<std::ptrdiff_t>(_from), _buffer.end(), [&](auto const& _x) {
			return std::memcmp(&_x, &_value, sizeof _x) == 0;
		});
	};
	if (!intact(data, n, guardSlot) || !intact(ops, 6 * n, guardOp))
		return "<port wrote past a buffer>";
	if (count == -2)
		return "err";
	if (count < 0 || static_cast<std::uint64_t>(count) > 6 * n)
		return "<port result " + std::to_string(count) + ">";
	ops.resize(static_cast<std::size_t>(count));
	// each operation but a swap pushes one slot
	std::size_t const size = m + static_cast<std::size_t>(std::count_if(ops.begin(), ops.end(), [](Op const& _op) {
		return _op.kind != Swap;
	}));
	if (size > n)
		return "<port stack of " + std::to_string(size) + " slots>";
	data.resize(size);
	// "ok" is 0 and 0, a block has a positive excess
	std::string const status =
		blocked[1] != 0 ? "blocked " + std::to_string(blocked[0]) + " " + std::to_string(blocked[1]) :
		blocked[0] == 0 ? "ok" :
		"<port blocked " + std::to_string(blocked[0]) + " 0>";
	return status + ";" + showStack(data) + ";" + showOps(ops);
}

/// A unit of the port
struct Unit
{
	/// The kind of its cases, the first field of a case line
	std::string_view kind;
	/// Its result on the fields of a case after the kind
	std::string (*run)(std::vector<std::string> const&);
	/// The part of a model result that it gives
	std::string (*view)(std::string const&);
};

/// The units of the port. A kind without an entry is checked against solc only.
Unit constexpr units[] = {
	// the C interface does not give the destinations
	{"bottomup", runBuildBottomUp, withoutLastField},
};

}

std::optional<port::Check> port::check(std::string const& _line, std::string const& _model)
{
	std::vector<std::string> fields = split(_line, ';');
	for (Unit const& unit: units)
		if (!fields.empty() && fields[0] == unit.kind)
		{
			fields.erase(fields.begin());
			return Check{unit.run(fields), unit.view(_model)};
		}
	return std::nullopt;
}
