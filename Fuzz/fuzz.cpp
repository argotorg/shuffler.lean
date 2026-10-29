// Differential fuzzer for buildMapping, removeSurplus, permute, permuteAtLowestHeight, buildBottomUp,
// Emission.run and Planner.run: decodes each fuzzer input into one case, runs the C++ shuffler and the
// Lean model (through the Lean C FFI) on it, and on the first difference prints "case <tab> c++ <tab> lean"
// to stderr and aborts. The case and result format is documented in Fuzz/Oracle.lean.
//
// The C++ shuffler lives in an anonymous namespace and the Emission steps are private, so this file
// includes Shuffler.cpp and is compiled with -fno-access-control.

#include <libyul/backends/evm/ssa/stack/Shuffler.cpp>

#include <libyul/backends/evm/ssa/InstructionStore.h>

#include <lean/lean.h>

#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using namespace solidity;
using namespace solidity::yul::ssa;

extern "C" void lean_initialize();
extern "C" lean_object* initialize_shuffler_x2dlean_Fuzz_Oracle(uint8_t _builtin);
extern "C" lean_object* shuffler_lean_run(lean_object* _line);

namespace
{

// The Lean model fixes these depths: MAX_SWAP_DEPTH and MAX_DUP_DEPTH in Shuffler/Basic.lean
std::size_t constexpr maxSwapDepth = 16;
std::size_t constexpr maxDupDepth = 15;

// --- the Lean model ---

void initializeLean()
{
	lean_initialize();
	lean_set_panic_messages(false);
	lean_object* const result = initialize_shuffler_x2dlean_Fuzz_Oracle(1);
	if (!lean_io_result_is_ok(result))
	{
		lean_io_result_show_error(result);
		throw std::runtime_error("Lean initialization failed");
	}
	lean_dec_ref(result);
	lean_io_mark_end_initialization();
}

std::string runLean(std::string const& _line)
{
	lean_object* const result = shuffler_lean_run(lean_mk_string(_line.c_str()));
	std::string text = lean_string_cstr(result);
	lean_dec_ref(result);
	return text;
}

// --- the C++ original ---

std::vector<std::string> split(std::string const& _s, char const _sep)
{
	std::vector<std::string> parts;
	std::stringstream stream(_s);
	for (std::string part; std::getline(stream, part, _sep);)
		parts.push_back(part);
	if (!_s.empty() && _s.back() == _sep)
		parts.emplace_back();
	return parts;
}

std::vector<std::string> words(std::string const& _s)
{
	std::vector<std::string> result;
	std::stringstream stream(_s);
	for (std::string word; stream >> word;)
		result.push_back(word);
	return result;
}

std::string join(std::vector<std::string> const& _words)
{
	std::string result;
	for (std::size_t i = 0; i < _words.size(); ++i)
		result += (i > 0 ? " " : "") + _words[i];
	return result;
}

std::uint32_t parseNat(std::string const& _s)
{
	if (_s.empty() || _s.find_first_not_of("0123456789") != std::string::npos)
		throw std::invalid_argument("not a number: " + _s);
	return static_cast<std::uint32_t>(std::stoul(_s));
}

std::string showOffset(std::optional<StackOffset> const& _offset)
{
	return _offset ? std::to_string(_offset->value) : "-";
}

/// Interns slot names: equal names give equal slots
class Slots
{
public:
	StackSlot parse(std::string const& _token)
	{
		StackSlot const slot = make(_token);
		m_names.emplace(slot, _token);
		return slot;
	}

	StackData parseStack(std::string const& _s)
	{
		StackData stack;
		for (std::string const& token: words(_s))
			stack.push_back(parse(token));
		return stack;
	}

	std::string show(StackSlot const& _slot) const { return m_names.at(_slot); }

	std::string showStack(StackData const& _stack) const
	{
		std::vector<std::string> names;
		for (StackSlot const& slot: _stack)
			names.push_back(show(slot));
		return join(names);
	}

	std::string showTrace(ShuffleTrace const& _trace) const
	{
		std::vector<std::string> ops;
		for (ShuffleOp const& op: _trace)
			switch (op.kind)
			{
			case ShuffleOp::Kind::Swap: ops.push_back("SWAP" + std::to_string(op.depth)); break;
			case ShuffleOp::Kind::Dup: ops.push_back("DUP" + std::to_string(op.depth)); break;
			case ShuffleOp::Kind::Pop: ops.push_back("POP"); break;
			case ShuffleOp::Kind::Push: ops.push_back("PUSH:" + show(op.slot)); break;
			case ShuffleOp::Kind::Load: ops.push_back("LOAD:" + show(op.slot)); break;
			case ShuffleOp::Kind::Store: ops.push_back("STORE:" + show(op.slot)); break;
			}
		return join(ops);
	}

	/// The numbers of the parsed variables that are in `_spills`, ascending
	std::vector<std::string> spilledVars(spill::SpillSet const& _spills) const
	{
		std::vector<std::string> result;
		for (auto const& [n, slot]: m_vars)
			if (_spills.isSpilled(slot.value()))
				result.push_back(std::to_string(n));
		return result;
	}

private:
	StackSlot make(std::string const& _token)
	{
		if (_token == "_")
			return StackSlot::makeJunk();
		if (_token == "R")
			return StackSlot::makeFunctionReturnLabel(0);
		if (_token.size() > 1 && _token[0] == 'v')
		{
			std::uint32_t const n = parseNat(_token.substr(1));
			if (!m_vars.contains(n))
				m_vars.emplace(n, StackSlot::makeValue(m_store, m_store.appendBuiltinCall({0}, {}, {})));
			return m_vars.at(n);
		}
		if (_token.size() > 1 && _token[0] == 'l')
			return StackSlot::makeValue(m_store, m_store.appendLiteral({0}, u256(parseNat(_token.substr(1)))).first);
		throw std::invalid_argument("not a slot: " + _token);
	}

	InstructionStore m_store;
	std::map<std::uint32_t, StackSlot> m_vars;
	std::map<StackSlot, std::string> m_names;
};

/// Binds stack offset i to the i-th destination
Mapping parseMapping(std::string const& _s, std::size_t const _stackSize, std::size_t const _targetSize)
{
	std::vector<std::string> const dests = words(_s);
	if (dests.size() != _stackSize)
		throw std::invalid_argument("not one destination per offset: " + _s);
	Mapping mapping(_stackSize, _targetSize);
	for (std::size_t i = 0; i < dests.size(); ++i)
		if (dests[i] != "-")
			mapping.bind(StackOffset{i}, StackOffset{parseNat(dests[i])});
	return mapping;
}

std::string showBit(bool const _b)
{
	return _b ? "1" : "0";
}

/// The status, stack, trace and mapping of a state step, also when it is blocked
std::string showState(
	Slots const& _slots,
	std::optional<Emission::Blocked> const& _blocked,
	ShuffleTrace const& _trace,
	StackData const& _data,
	Mapping const& _mapping
)
{
	std::string const status = _blocked ?
		"blocked " + std::to_string(_blocked->offset.value) + " " + std::to_string(_blocked->excess) :
		"ok";
	std::vector<std::string> dests;
	for (std::size_t i = 0; i < _data.size(); ++i)
		dests.push_back(showOffset(_mapping.destinationOf(StackOffset{i})));
	return status + ";" + _slots.showStack(_data) + ";" + _slots.showTrace(_trace) + ";" + join(dests);
}

std::string showState(Slots const& _slots, std::optional<Emission::Blocked> const& _blocked, Emission const& _emission)
{
	return showState(_slots, _blocked, _emission.m_trace, _emission.m_data, _emission.m_mapping);
}

MappingBuilder::WildcardSlotsStrategy parseStrategy(std::string const& _s)
{
	return _s == "T" ? MappingBuilder::WildcardSlotsStrategy::Take : MappingBuilder::WildcardSlotsStrategy::Leave;
}

spill::SpillSet parseSpills(Slots& _slots, std::string const& _s)
{
	spill::SpillSet spills;
	for (std::string const& var: words(_s))
		spills.add(_slots.parse("v" + var).value());
	return spills;
}

std::string runBuildMapping(Slots& _slots, std::vector<std::string> const& _fields)
{
	StackData const source = _slots.parseStack(_fields.at(2));
	StackData const target = _slots.parseStack(_fields.at(3));
	std::vector<std::uint8_t> dropped;
	for (std::string const& word: words(_fields.at(4)))
		dropped.push_back(static_cast<std::uint8_t>(parseNat(word)));
	MappingBuilder builder(source, target, dropped, parseStrategy(_fields.at(1)));
	std::string const result = "ok " + showBit(builder.sawWildcardCopy()) + ";";
	Mapping const mapping = std::move(builder).release();
	std::vector<std::string> sources;
	for (std::size_t j = 0; j < target.size(); ++j)
		sources.push_back(showOffset(mapping.positionOf(StackOffset{j})));
	return result + join(sources);
}

std::string runOnState(Slots& _slots, std::vector<std::string> const& _fields)
{
	std::string const& kind = _fields.at(0);
	StackData const stack = _slots.parseStack(_fields.at(1));
	StackData const target = _slots.parseStack(_fields.at(2));
	Mapping const mapping = parseMapping(_fields.at(3), stack.size(), target.size());
	spill::SpillSet const spills = parseSpills(_slots, _fields.at(4));
	Emission emission(stack, target, mapping, spills, maxSwapDepth, maxDupDepth);
	if (kind == "emit")
	{
		Emission::Result const result = std::move(emission).run();
		return showState(_slots, result.blocked, result.trace, result.data, result.mapping);
	}
	std::optional<Emission::Blocked> const blocked =
		kind == "surplus" ? emission.removeSurplus() :
		kind == "lowest" ? emission.permuteAtLowestHeight() :
		emission.buildBottomUp();
	return showState(_slots, blocked, emission);
}

std::string runPermute(Slots& _slots, std::vector<std::string> const& _fields)
{
	StackData const stack = _slots.parseStack(_fields.at(1));
	Mapping const mapping = parseMapping(_fields.at(2), stack.size(), stack.size());
	// the target is the permuted stack, so that the mapping binds every slot to its destination
	StackData target(stack.size(), StackSlot::makeJunk());
	std::vector<std::size_t> permutation;
	for (std::size_t i = 0; i < stack.size(); ++i)
	{
		std::size_t const dest = mapping.destinationOf(StackOffset{i}).value().value;
		target[dest] = stack[i];
		permutation.push_back(dest);
	}
	spill::SpillSet const spills;
	Emission emission(stack, target, mapping, spills, maxSwapDepth, maxDupDepth);
	// the Lean permute succeeds on an empty stack; the C++ one is never called on one
	if (stack.empty())
		return showState(_slots, std::nullopt, emission);
	return showState(_slots, emission.permute(permutation), emission);
}

std::string runPlanner(Slots& _slots, std::vector<std::string> const& _fields)
{
	StackData const source = _slots.parseStack(_fields.at(3));
	StackData const target = _slots.parseStack(_fields.at(4));
	Planner planner(
		source,
		target,
		parseSpills(_slots, _fields.at(5)),
		_fields.at(2) == "1",
		parseStrategy(_fields.at(1)),
		maxSwapDepth
	);
	bool const success = planner.run();
	std::vector<std::string> dropped;
	for (std::uint8_t const d: planner.m_dropped)
		dropped.push_back(std::to_string(d));
	std::string const head = "ok " + showBit(success) + ";" + showBit(planner.sawWildcardCopy()) + ";" +
		join(_slots.spilledVars(planner.m_spills)) + ";" + join(dropped);
	if (!success)
		return head;
	std::vector<std::string> sources;
	for (std::size_t j = 0; j < target.size(); ++j)
		sources.push_back(showOffset(planner.m_plan->positionOf(StackOffset{j})));
	return head + ";" + _slots.showStack(planner.m_result->data) + ";" + _slots.showTrace(planner.m_result->trace) +
		";" + join(sources);
}

std::string runCpp(Slots& _slots, std::string const& _line)
{
	std::vector<std::string> const fields = split(_line, ';');
	std::string const& kind = fields.at(0);
	try
	{
		if (kind == "map" && fields.size() == 5)
			return runBuildMapping(_slots, fields);
		if ((kind == "surplus" || kind == "lowest" || kind == "bottomup" || kind == "emit") && fields.size() == 5)
			return runOnState(_slots, fields);
		if (kind == "permute" && fields.size() == 3)
			return runPermute(_slots, fields);
		if (kind == "plan" && fields.size() == 6)
			return runPlanner(_slots, fields);
	}
	catch (yul::YulAssertion const&)
	{
		return "err";
	}
	throw std::invalid_argument("not a case: " + _line);
}

// --- the case generator ---

/// Draws choices from the fuzzer input; once the input is used up, every choice is the lowest one
class Input
{
public:
	Input(std::uint8_t const* _data, std::size_t const _size): m_data(_data), m_size(_size) {}

	/// A number in [_lo, _hi], from one input byte per 8 bits of range
	std::size_t pick(std::size_t const _lo, std::size_t const _hi)
	{
		std::size_t value = 0;
		for (std::size_t range = _hi - _lo; range > 0 && m_size > 0; range >>= 8, ++m_data, --m_size)
			value = (value << 8) | *m_data;
		return _lo + value % (_hi - _lo + 1);
	}

	bool chance(std::size_t const _outOf) { return pick(0, _outOf - 1) == 0; }

private:
	std::uint8_t const* m_data;
	std::size_t m_size;
};

/// Most stacks are small, so that equal slots, wildcards and drops collide often
std::size_t stackSize(Input& _in)
{
	std::size_t const limits[] = {3, 6, 12, 24, 40};
	return _in.pick(0, limits[_in.pick(0, 4)]);
}

/// Drawn like a stack size, so that deep stacks can have distinct slots
std::size_t varCount(Input& _in)
{
	return 1 + stackSize(_in);
}

std::string slot(Input& _in, std::size_t const _numVars)
{
	switch (_in.pick(0, 9))
	{
	case 0: return "_";
	case 1: return _in.chance(4) ? "R" : "_";
	case 2: case 3: return "l" + std::to_string(_in.pick(0, 2));
	default: return "v" + std::to_string(_in.pick(0, _numVars - 1));
	}
}

/// A quarter of the stacks that fit in the variables have distinct slots: random slots on a deep stack
/// are almost never distinct
std::vector<std::string> slots(Input& _in, std::size_t const _size, std::size_t const _numVars)
{
	if (_size <= _numVars && _in.chance(4))
	{
		std::vector<std::string> vars;
		for (std::size_t v = 0; v < _numVars; ++v)
			vars.push_back("v" + std::to_string(v));
		// the first `_size` steps of Fisher-Yates
		for (std::size_t i = 0; i < _size; ++i)
			std::swap(vars[i], vars[_in.pick(i, _numVars - 1)]);
		vars.resize(_size);
		return vars;
	}
	std::vector<std::string> result;
	for (std::size_t i = 0; i < _size; ++i)
		result.push_back(slot(_in, _numVars));
	return result;
}

/// Half of the target slots are copies of source slots, so that most demands have a copy
std::vector<std::string> targetFor(Input& _in, std::vector<std::string> const& _source, std::size_t const _numVars)
{
	std::vector<std::string> target;
	for (std::size_t i = stackSize(_in); i > 0; --i)
		target.push_back(!_source.empty() && _in.chance(2) ? _source[_in.pick(0, _source.size() - 1)] : slot(_in, _numVars));
	return target;
}

std::string strategy(Input& _in)
{
	return _in.chance(2) ? "L" : "T";
}

std::string mapCase(Input& _in)
{
	std::size_t const numVars = varCount(_in);
	std::vector<std::string> const source = slots(_in, stackSize(_in), numVars);
	std::vector<std::string> const target = targetFor(_in, source, numVars);
	std::vector<std::string> dropped;
	for (std::size_t i = 0; i < source.size(); ++i)
		dropped.push_back(std::vector<std::string>{"0", "0", "0", "0", "0", "1", "255"}[_in.pick(0, 6)]);
	return "map;" + strategy(_in) + ";" + join(source) + ";" + join(target) + ";" + join(dropped);
}

/// Most target variables that are not on the source stack are spilled, so that most plans can start
std::string planCase(Input& _in)
{
	std::size_t const numVars = varCount(_in);
	std::vector<std::string> const source = slots(_in, stackSize(_in), numVars);
	std::vector<std::string> const target = targetFor(_in, source, numVars);
	std::vector<bool> spilled(numVars);
	for (std::size_t v = 0; v < numVars; ++v)
		spilled[v] = _in.chance(4);
	for (std::string const& slot: target)
		if (slot[0] == 'v' && !ranges::contains(source, slot) && !_in.chance(8))
			spilled[parseNat(slot.substr(1))] = true;
	std::vector<std::string> vars;
	for (std::size_t v = 0; v < numVars; ++v)
		if (spilled[v])
			vars.push_back(std::to_string(v));
	return "plan;" + strategy(_in) + ";" + (_in.chance(2) ? "1" : "0") + ";" + join(source) + ";" + join(target) + ";" +
		join(vars);
}

/// A stack, target, mapping and spill set. For "surplus" and "emit" some slots have no destination. For
/// "lowest" and "bottomup" every slot has one. The state is `Valid`, as buildBottomUp requires, for "emit" after
/// removeSurplus.
std::string stateCase(Input& _in, std::string const& _kind)
{
	bool const surplus = _kind == "surplus" || _kind == "emit";
	std::size_t const numVars = varCount(_in);
	std::vector<std::string> target = slots(_in, stackSize(_in), numVars);
	std::vector<std::size_t> free;
	for (std::size_t j = 0; j < target.size(); ++j)
		free.push_back(j);
	std::vector<std::string> stack;
	std::vector<std::string> dests;
	for (std::size_t i = surplus ? stackSize(_in) : _in.pick(0, target.size()); i > 0; --i)
		if (free.empty() || (surplus && _in.chance(3)))
		{
			stack.push_back(slot(_in, numVars));
			dests.push_back("-");
		}
		else
		{
			std::size_t const k = _in.pick(0, free.size() - 1);
			std::size_t const dest = free[k];
			free.erase(free.begin() + static_cast<std::ptrdiff_t>(k));
			// a slot bound for a wildcard can be anything, any other slot is the slot it is bound for
			stack.push_back(target[dest] == "_" ? slot(_in, numVars) : target[dest]);
			dests.push_back(std::to_string(dest));
		}
	std::vector<bool> spilled(numVars);
	for (std::size_t v = 0; v < numVars; ++v)
		spilled[v] = _in.chance(4);
	// removeSurplus pops the slots without a destination, so only the bound slots are copies to DUP
	std::vector<std::string> bound;
	for (std::size_t i = 0; i < stack.size(); ++i)
		if (dests[i] != "-")
			bound.push_back(stack[i]);
	// a variable to generate that has no bound copy has to be spilled, a return label can't be generated and
	// `Valid` needs every target return label bound
	for (std::size_t const j: free)
		if (target[j] == "R")
		{
			if (_kind != "surplus" || !ranges::contains(stack, target[j]))
				target[j] = "_";
		}
		else if (target[j][0] == 'v' && !ranges::contains(bound, target[j]))
			spilled[parseNat(target[j].substr(1))] = true;
	std::vector<std::string> vars;
	for (std::size_t v = 0; v < numVars; ++v)
		if (spilled[v])
			vars.push_back(std::to_string(v));
	return _kind + ";" + join(stack) + ";" + join(target) + ";" + join(dests) + ";" + join(vars);
}

std::string permuteCase(Input& _in)
{
	std::vector<std::string> const stack = slots(_in, stackSize(_in), varCount(_in));
	std::vector<std::string> dests;
	for (std::size_t i = 0; i < stack.size(); ++i)
		dests.push_back(std::to_string(i));
	// Fisher-Yates
	for (std::size_t i = 0; i + 1 < dests.size(); ++i)
		std::swap(dests[i], dests[_in.pick(i, dests.size() - 1)]);
	return "permute;" + join(stack) + ";" + join(dests);
}

std::string makeCase(Input& _in)
{
	switch (_in.pick(0, 6))
	{
	case 0: return mapCase(_in);
	case 1: return stateCase(_in, "surplus");
	case 2: return permuteCase(_in);
	case 3: return stateCase(_in, "lowest");
	case 4: return stateCase(_in, "emit");
	case 5: return planCase(_in);
	default: return stateCase(_in, "bottomup");
	}
}

}

extern "C" int LLVMFuzzerInitialize(int*, char***)
{
	initializeLean();
	return 0;
}

extern "C" int LLVMFuzzerTestOneInput(std::uint8_t const* _data, std::size_t const _size)
{
	Input input(_data, _size);
	std::string const line = makeCase(input);
	Slots slots;
	std::string const cpp = runCpp(slots, line);
	std::string const lean = runLean(line);
	if (cpp != lean)
	{
		std::cerr << line << '\t' << cpp << '\t' << lean << '\n';
		std::abort();
	}
	return 0;
}
