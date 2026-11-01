#pragma once

#include "Freestanding.h"
#include "ShuffleTrace.h"

namespace
{

/// Stack.h's Stack: the working stack in a caller's buffer, with the trace of the operations on it
class Stack
{
public:
	Stack(StackSlot* const _data, std::size_t const _size, ShuffleOp* const _trace):
		m_data(_data), m_size(_size), m_trace(_trace)
	{}

	std::size_t size() const { return m_size; }
	std::size_t traceSize() const { return m_traceSize; }
	StackSlot const& operator[](StackOffset const _offset) const { return m_data[_offset.value]; }
	StackSlot const& top() const { return m_data[m_size - 1]; }
	StackOffset topOffset() const { return StackOffset{m_size - 1}; }
	StackDepth offsetToDepth(StackOffset const _offset) const { return StackDepth{m_size - 1 - _offset.value}; }

	void swap(StackOffset const _offset)
	{
		StackSlot const slot = m_data[_offset.value];
		m_data[_offset.value] = top();
		m_data[m_size - 1] = slot;
		record(ShuffleOp::swap(offsetToDepth(_offset)));
	}

	/// A non-literal value can only be pushed by a reload of its spill
	void push(StackSlot const _slot)
	{
		m_data[m_size++] = _slot;
		record(_slot.isValue() && !_slot.isLiteralValue() ? ShuffleOp::load(_slot) : ShuffleOp::push(_slot));
	}

	void dup(StackOffset const _offset)
	{
		record(ShuffleOp::dup(StackDepth{offsetToDepth(_offset).value + 1}));
		m_data[m_size] = m_data[_offset.value];
		m_size++;
	}

	Status pop()
	{
		yulAssert(m_size != 0);
		--m_size;
		record(ShuffleOp::pop());
		return Status::Done;
	}

private:
	void record(ShuffleOp const _op) { m_trace[m_traceSize++] = _op; }

	StackSlot* m_data;
	std::size_t m_size;
	ShuffleOp* m_trace;
	std::size_t m_traceSize = 0;
};

}
