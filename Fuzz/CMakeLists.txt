cmake_minimum_required(VERSION 3.13)
project(shuffler-fuzz C CXX ASM)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Set by build.sh: the Lean toolchain, the C files of the Lean model and the object files of its imports
set(LEAN_PREFIX "" CACHE PATH "Lean toolchain prefix")
set(LEAN_SOURCES "" CACHE FILEPATH "File that lists one Lean C file per line")
set(LEAN_OBJECTS "" CACHE FILEPATH "File that lists one Lean object file per line")
file(STRINGS "${LEAN_SOURCES}" lean_sources)
file(STRINGS "${LEAN_OBJECTS}" lean_objects)

add_subdirectory(../solidity solidity EXCLUDE_FROM_ALL)

# The kraken/c port: its units in port.cpp, and the asm that the Kraken proofs read. A new unit adds its
# entry in port.cpp (and its .S file here, if it is not in build_bottom_up.S).
set(port_asm ${CMAKE_CURRENT_SOURCE_DIR}/../kraken/c/build_bottom_up.S)
# GNU as assembles the asm, as for kraken/c/bbu_harness
set_source_files_properties(${port_asm} PROPERTIES COMPILE_OPTIONS "-fno-integrated-as")
add_library(port STATIC port.cpp ${port_asm})

# The tests of port.cpp against fixed model results. It needs no solc and no Lean.
add_executable(port_test port_test.cpp)
target_link_libraries(port_test PRIVATE port)

set_source_files_properties(${lean_objects} PROPERTIES EXTERNAL_OBJECT TRUE GENERATED TRUE)
# the flags Lake compiles Lean C files with
set_source_files_properties(${lean_sources} PROPERTIES COMPILE_OPTIONS
	"-fstack-clash-protection;-ffp-contract=off;-fvisibility=hidden;-O3;-DNDEBUG;-DLEAN_EXPORTING")
# fuzz.cpp calls the private Emission steps; lines.cpp includes fuzz.cpp
set_source_files_properties(fuzz.cpp lines.cpp PROPERTIES COMPILE_OPTIONS "-fno-access-control")

# fuzz: the fuzzer. lines: the checks of the fuzzer on the case lines of stdin.
add_executable(fuzz fuzz.cpp ${lean_sources} ${lean_objects})
target_compile_options(fuzz PRIVATE -fsanitize=fuzzer)
target_link_options(fuzz PRIVATE -fsanitize=fuzzer)
add_executable(lines lines.cpp ${lean_sources} ${lean_objects})
foreach(target fuzz lines)
	# libleanshared exports the _Unwind_* functions of its own libunwind. libgcc_s must come first in the
	# symbol lookup order, else C++ exceptions mix both unwinders and some reach std::terminate.
	target_link_options(${target} PRIVATE "LINKER:--push-state,--no-as-needed,-lgcc_s,--pop-state")
	target_include_directories(${target} SYSTEM PRIVATE "${LEAN_PREFIX}/include")
	target_link_directories(${target} PRIVATE "${LEAN_PREFIX}/lib/lean")
	target_link_libraries(${target} PRIVATE port yul Lake_shared leanshared)
	set_target_properties(${target} PROPERTIES BUILD_RPATH "${LEAN_PREFIX}/lib/lean")
endforeach()
