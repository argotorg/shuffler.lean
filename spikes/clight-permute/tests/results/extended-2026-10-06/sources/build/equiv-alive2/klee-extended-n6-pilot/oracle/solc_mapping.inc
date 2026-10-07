/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

class Mapping
{
public:
	Mapping(std::size_t const _stackSize, std::size_t const _targetSize):
		m_destinationOf(_stackSize),
		m_positionOf(_targetSize)
	{}

	/// Height of the stack the mapping is kept for
	std::size_t stackSize() const { return m_destinationOf.size(); }

	/// The destination of the slot at `_pos`, or none for a surplus slot
	Destination const& destinationOf(StackOffset const _pos) const { return m_destinationOf[_pos.value]; }

	/// The position of the slot bound for `_destination`, or none if no slot is bound for it
	std::optional<StackOffset> positionOf(StackOffset const _destination) const
	{
		return m_positionOf[_destination.value];
	}

	/// Binds the slot at `_pos` for `_destination`; the slot may not have a destination yet and no slot may be
	/// bound for the destination yet
	void bind(StackOffset const _pos, StackOffset const _destination)
	{
		yulAssert(!m_destinationOf[_pos.value].has_value(), "slot already has a destination");
		yulAssert(!m_positionOf[_destination.value].has_value(), "destination already bound to a slot");
		m_destinationOf[_pos.value] = _destination;
		m_positionOf[_destination.value] = _pos;
	}

	/// Exchanges the destinations of the slots at `_a` and `_b`
	void swapDestinations(StackOffset const _a, StackOffset const _b)
	{
		std::swap(m_destinationOf[_a.value], m_destinationOf[_b.value]);
		if (Destination const& destination = m_destinationOf[_a.value])
			m_positionOf[destination->value] = _a;
		if (Destination const& destination = m_destinationOf[_b.value])
			m_positionOf[destination->value] = _b;
	}

	/// Forgets the top slot's destination, if any
	void pop()
	{
		if (Destination const& destination = m_destinationOf.back())
			m_positionOf[destination->value].reset();
		m_destinationOf.pop_back();
	}

	/// Binds the freshly pushed top slot for `_destination`, which no slot may be bound for yet
	void push(StackOffset const _destination)
	{
		m_destinationOf.emplace_back();
		bind(StackOffset{m_destinationOf.size() - 1}, _destination);
	}

	/// Hands out the destination-indexed side, ending the mapping's life
	[[nodiscard]] std::vector<std::optional<StackOffset>> release() && { return std::move(m_positionOf); }

private:
	std::vector<Destination> m_destinationOf;
	std::vector<std::optional<StackOffset>> m_positionOf;
};
