cmake_minimum_required(VERSION 3.13)
project(shuffler-fuzz C CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Set by build.sh: the Lean toolchain, the C files of the Lean model and the object files of its imports
set(LEAN_PREFIX "" CACHE PATH "Lean toolchain prefix")
set(LEAN_SOURCES "" CACHE FILEPATH "File that lists one Lean C file per line")
set(LEAN_OBJECTS "" CACHE FILEPATH "File that lists one Lean object file per line")
file(STRINGS "${LEAN_SOURCES}" lean_sources)
file(STRINGS "${LEAN_OBJECTS}" lean_objects)

add_subdirectory(../solidity solidity EXCLUDE_FROM_ALL)

add_executable(fuzz fuzz.cpp ${lean_sources} ${lean_objects})
set_source_files_properties(${lean_objects} PROPERTIES EXTERNAL_OBJECT TRUE GENERATED TRUE)
# the flags Lake compiles Lean C files with
set_source_files_properties(${lean_sources} PROPERTIES COMPILE_OPTIONS
	"-fstack-clash-protection;-ffp-contract=off;-fvisibility=hidden;-O3;-DNDEBUG;-DLEAN_EXPORTING")
# fuzz.cpp calls the private Emission steps
set_source_files_properties(fuzz.cpp PROPERTIES COMPILE_OPTIONS "-fno-access-control")
target_compile_options(fuzz PRIVATE -fsanitize=fuzzer)
target_link_options(fuzz PRIVATE -fsanitize=fuzzer)
# libleanshared exports the _Unwind_* functions of its own libunwind. libgcc_s must come first in the
# symbol lookup order, else C++ exceptions mix both unwinders and some reach std::terminate.
target_link_options(fuzz PRIVATE "LINKER:--push-state,--no-as-needed,-lgcc_s,--pop-state")
target_include_directories(fuzz SYSTEM PRIVATE "${LEAN_PREFIX}/include")
target_link_directories(fuzz PRIVATE "${LEAN_PREFIX}/lib/lean")
target_link_libraries(fuzz PRIVATE yul Lake_shared leanshared)
set_target_properties(fuzz PROPERTIES BUILD_RPATH "${LEAN_PREFIX}/lib/lean")
