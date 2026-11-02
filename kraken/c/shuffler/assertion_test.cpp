// Each assertion case must end the process with exit status 1.
#include "stack/Shuffler.cpp"

#include <string_view>

// The entries in test_wrappers.S use the same C++ data layout.
extern "C" std::int64_t emission_pop(std::uint64_t, std::uint64_t, StackSlot*, StackSlot const*,
	Optional<StackOffset> const*, std::uint8_t const*, std::uint64_t, ShuffleOp*,
	Optional<StackOffset>*, Optional<StackOffset>*, std::uint64_t*);
extern "C" std::int64_t spill_set(std::uint64_t, std::uint8_t*, StackSlot const*, std::uint64_t,
	StackSlot const*, std::uint64_t, std::uint8_t*);
extern "C" std::int64_t emit(std::uint64_t, std::uint64_t, StackSlot*, StackSlot const*,
	Optional<StackOffset>*, std::uint8_t const*, std::uint64_t, ShuffleOp*, std::uint64_t*, std::uint64_t*);

int main(int argc, char** argv)
{
	if (argc != 2)
		return 2;
	std::string_view const name{argv[1]};
	StackSlot data[2]{};
	StackSlot const variable{0, StackSlot::Kind::Value, InstOpcode{1}};
	StackSlot const target[]{variable};
	ShuffleOp ops[4]{};
	std::uint8_t spilled[]{0};
	Optional<StackOffset> dest[]{std::nullopt, std::nullopt};
	Optional<StackOffset> positions[]{std::nullopt, std::nullopt};
	std::uint64_t pending = 0;
	std::uint64_t blocked[2]{};
	if (name == "empty-stack")
	{
		Stack stack{data, 0, ops};
		static_cast<void>(stack.pop());
	}
	else if (name == "duplicate-spill")
	{
		spilled[0] = 1;
		SpillSet spills{spilled};
		static_cast<void>(spills.add(variable));
	}
	else if (name == "nonvariable-spill")
	{
		SpillSet spills{spilled};
		static_cast<void>(spills.add(StackSlot::makeJunk()));
	}
	else if (name == "unavailable-target")
	{
		Mapping planned{0, 1};
		Emission emission{Stack{data, 0, ops}, target, 1, planned, spilled};
		static_cast<void>(emission.run());
	}
	else if (name == "success")
	{
		Stack stack{data, 1, ops};
		return stack.pop() == Status::Done && stack.size() == 0 && stack.traceSize() == 1 ? 0 : 3;
	}
	else if (name == "inconsistent-plan" || name == "consistent-plan")
	{
		StackSlot const resolveTarget[]{StackSlot::makeJunk(), StackSlot::makeJunk()};
		std::uint8_t dropped[2]{};
		Mapping planned{2, 2};
		planned.bind(StackOffset{0}, StackOffset{0});
		if (name == "inconsistent-plan")
		{
			// Leave positionOf(0) bound to a source slot that has no destination.
			planned.bind(StackOffset{0}, StackOffset{1});
			planned.swapDestinations(StackOffset{0}, StackOffset{1});
		}
		Mapping current{2, 2};
		current.bind(StackOffset{1}, StackOffset{0});
		Planner planner{data, 2, resolveTarget, 2, SpillSet{spilled}, false, dropped};
		return planner.resolve(planned, Emission::Blocked{StackOffset{0}, 1}, current, 2) ==
			Resolution::Dropped && dropped[0] == 1 ? 0 : 3;
	}
	else if (name == "assembly-empty-stack")
		static_cast<void>(emission_pop(0, 0, data, target, dest, spilled, 1, ops, dest, positions, &pending));
	else if (name == "assembly-duplicate-spill")
	{
		spilled[0] = 1;
		static_cast<void>(spill_set(1, spilled, target, 1, target, 0, spilled));
	}
	else if (name == "assembly-nonvariable-spill")
		static_cast<void>(spill_set(1, spilled, data, 1, target, 0, spilled));
	else if (name == "assembly-unavailable-target")
		static_cast<void>(emit(0, 1, data, target, dest, spilled, 1, ops, blocked, &pending));
	else if (name == "assembly-success")
		return emission_pop(1, 0, data, target, dest, spilled, 1, ops, dest, positions, &pending) == 1 &&
			ops[0].kind == ShuffleOp::Kind::Pop && pending == 0 ? 0 : 3;
	else
		return 2;
	return 0;
}
