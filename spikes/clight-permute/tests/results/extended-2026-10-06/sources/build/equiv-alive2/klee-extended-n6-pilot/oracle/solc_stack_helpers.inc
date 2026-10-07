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

	void swap(Offset const& _offset)
	{
		yulAssert(isValidSwapTarget(_offset), "Stack too deep");
		std::swap((*m_data)[_offset.value], m_data->back());
		if (m_trace)
			m_trace->push_back(ShuffleOp::swap(offsetToDepth(_offset)));
	}

	bool isValidSwapTarget(Offset const& _offset) const noexcept { return isValidSwapTarget(offsetToDepth(_offset)); }

	bool isValidSwapTarget(Depth const& _depth) const noexcept { return _depth < size() && 1 <= _depth.value && _depth.value <= m_reachableStackDepth; }

	bool isBeyondSwapRange(Depth const& _depth) const noexcept { return _depth > m_reachableStackDepth; }

	size_t size() const noexcept { return m_data->size(); }

	Depth offsetToDepth(Offset const& _offset) const
	{
		yulAssert(_offset < size(), "Offset out of range");
		return Depth{size() - _offset.value - 1};
	}
