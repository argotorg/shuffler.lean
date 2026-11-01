#pragma once

#include "../Freestanding.h"

namespace
{

/// spill/SpillSet.h's SpillSet, the Lean model's SpillSet (a Finset VarId), in a caller's buffer: the variable id is
/// spilled if m_spilled[id] is not 0. The buffer has a byte for each variable id of the caller.
///
/// An aggregate: with a user-provided constructor, g++ -O1 changes the asm of build_bottom_up and emission_pop.
struct SpillSet
{
	/// SpillSet.is_spilled: Shuffler.cpp's free isSpilled and SpillSet::isSpilled. Only a variable can be spilled.
	constexpr bool isSpilled(StackSlot const _slot) const { return isVariable(_slot) && m_spilled[_slot.payload] != 0; }

	/// SpillSet.add: spills the variable `_slot`. SpillSet::add takes a variable id; Shuffler.cpp's Planner checks
	/// that the slot is a variable before it calls add.
	Status add(StackSlot _slot);

	std::uint8_t* m_spilled;
};

[[gnu::used]] UNIT Status SpillSet::add(StackSlot const _slot)
{
	yulAssert(isVariable(_slot), "spill candidate must be a variable");  // Lean
	yulAssert(m_spilled[_slot.payload] == 0, "can't spill a value twice");
	m_spilled[_slot.payload] = 1;
	return Status::Done;
}

}
