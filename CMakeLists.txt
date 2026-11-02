cmake_minimum_required(VERSION 3.20)
project(shuffler-lean LANGUAGES CXX ASM)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# Include compiler-wrapper system paths in compile_commands.json for clangd.
foreach(path IN LISTS CMAKE_CXX_IMPLICIT_INCLUDE_DIRECTORIES)
  add_compile_options("-isystem${path}")
endforeach()

include(CTest)
add_subdirectory(kraken/c)
