#pragma once

// Run production calls in a child. Keep their exit status and buffer writes.
#include <cerrno>
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <initializer_list>
#include <new>
#include <optional>
#include <type_traits>
#include <vector>

#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

namespace process_test
{

struct Buffer
{
	void* data;
	std::size_t size;
	std::function<void()> beforeSave = [] {};
};

template<class T>
Buffer buffer(T& value)
{
	static_assert(std::is_trivially_copyable_v<T>);
	return {&value, sizeof(value)};
}

template<class T>
Buffer buffer(std::vector<T>& values)
{
	static_assert(std::is_trivially_copyable_v<T>);
	return {values.data(), values.size() * sizeof(T)};
}

template<class T, class Read>
Buffer sample(T& value, Read const& read)
{
	auto result = buffer(value);
	result.beforeSave = [&value, read] { value = read(); };
	return result;
}

struct Result
{
	std::optional<std::int64_t> returned;
	int exitStatus;
};

struct Snapshot
{
	std::initializer_list<Buffer> buffers;
	unsigned char* bytes;

	void save() const
	{
		auto* out = bytes;
		for (auto const& b: buffers)
		{
			b.beforeSave();
			if (b.size)
				std::memcpy(out, b.data, b.size);
			out += b.size;
		}
	}
};

template<class F>
Result call(F const& operation, std::initializer_list<Buffer> const buffers = {})
{
	struct Header { bool returned; std::int64_t value; };
	std::size_t size = sizeof(Header);
	for (auto const& b: buffers)
		size += b.size;
	void* const memory = mmap(nullptr, size, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
	if (memory == MAP_FAILED)
	{
		std::perror("mmap");
		std::abort();
	}
	auto* const header = ::new (memory) Header{};
	Snapshot snapshot{buffers, reinterpret_cast<unsigned char*>(header + 1)};
	std::fflush(nullptr);
	pid_t const child = fork();
	if (child < 0)
	{
		std::perror("fork");
		std::abort();
	}
	if (child == 0)
	{
		// exit(1) runs this callback without unwinding the call's stack.
		if (on_exit([](int, void* p) { static_cast<Snapshot const*>(p)->save(); },
			&snapshot) != 0)
			std::_Exit(125);
		header->value = static_cast<std::int64_t>(operation());
		header->returned = true;
		snapshot.save();
		std::_Exit(0);
	}
	int status;
	while (waitpid(child, &status, 0) < 0)
		if (errno != EINTR)
		{
			std::perror("waitpid");
			std::abort();
		}
	int const exitStatus = WIFEXITED(status) ? WEXITSTATUS(status) : -WTERMSIG(status);
	if (exitStatus == 0 || exitStatus == 1)
	{
		auto const* in = snapshot.bytes;
		for (auto const& b: buffers)
		{
			if (b.size)
				std::memcpy(b.data, in, b.size);
			in += b.size;
		}
	}
	Result const result{header->returned ? std::optional{header->value} : std::nullopt, exitStatus};
	munmap(memory, size);
	return result;
}

}
