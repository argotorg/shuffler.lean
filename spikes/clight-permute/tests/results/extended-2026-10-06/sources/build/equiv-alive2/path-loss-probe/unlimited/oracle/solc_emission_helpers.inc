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

	Destination const& destinationOf(StackOffset const _pos) const
	{
		return m_mapping.destinationOf(_pos);
	}

	bool isFinal(StackOffset const _pos) const
	{
		return destinationOf(_pos) == _pos;
	}

	StackDepth depthOf(StackOffset const _pos) const
	{
		return m_stack.offsetToDepth(_pos);
	}

	bool isSwapReachable(StackOffset const _pos) const
	{
		return !m_stack.isBeyondSwapRange(depthOf(_pos));
	}

	void swapWith(StackOffset const _pos)
	{
		yulAssert(!isFinal(_pos), "swapping a final slot out of place");
		m_stack.swap(_pos);
		m_mapping.swapDestinations(_pos, StackOffset{m_data.size() - 1});
	}

	[[nodiscard]] Blocked block(StackOffset const _position, std::size_t const _excess) const
	{
		yulAssert(_excess > 0);
		return Blocked{_position, _excess};
	}

	[[nodiscard]] Blocked blockSwapUnreachable(StackOffset const _position) const
	{
		return block(_position, depthOf(_position).value - m_maxSwapDepth);
	}
