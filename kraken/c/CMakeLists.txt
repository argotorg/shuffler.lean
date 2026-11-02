add_library(shuffler STATIC shuffler/test_wrappers.cpp)

# The proofs use GCC output, including its instruction choices and function order.
set(SHUFFLER_ASM_CXX "g++" CACHE FILEPATH "GCC 15.3.0 compiler for the assembly proofs")
set(shuffler_assembly "${CMAKE_CURRENT_BINARY_DIR}/build_bottom_up.S")
add_custom_command(
  OUTPUT "${shuffler_assembly}"
  COMMAND bash "${CMAKE_CURRENT_SOURCE_DIR}/generate_assembly.sh"
    "${SHUFFLER_ASM_CXX}" "${shuffler_assembly}"
  WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
  DEPENDS generate_assembly.sh labels.awk
    shuffler/test_wrappers.cpp shuffler/stack/Shuffler.cpp
    shuffler/SSACFGTypes.h shuffler/StackSlot.h shuffler/ShuffleTrace.h
    shuffler/Stack.h shuffler/spill/SpillSet.h shuffler/Freestanding.h
  VERBATIM)
add_custom_target(shuffler_assembly DEPENDS "${shuffler_assembly}")

if(BUILD_TESTING)
  # The recorded binary layout uses GCC for the C test programs.
  find_program(SHUFFLER_TEST_CC gcc REQUIRED)
  foreach(name bbu_harness pop_harness surplus_harness lowest_harness)
    add_custom_command(
      OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/${name}"
      COMMAND "${SHUFFLER_TEST_CC}" -O1 -no-pie
        -o "${CMAKE_CURRENT_BINARY_DIR}/${name}"
        "${CMAKE_CURRENT_SOURCE_DIR}/${name}.c" "${shuffler_assembly}"
      DEPENDS "${name}.c" harness_process.h "${shuffler_assembly}"
      VERBATIM)
    add_custom_target(shuffler_${name} ALL DEPENDS "${CMAKE_CURRENT_BINARY_DIR}/${name}")
  endforeach()

  add_custom_command(
    OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/harness_process_test"
    COMMAND "${SHUFFLER_TEST_CC}" -O1 -Wall -Wextra
      -o "${CMAKE_CURRENT_BINARY_DIR}/harness_process_test"
      "${CMAKE_CURRENT_SOURCE_DIR}/harness_process_test.c"
    DEPENDS harness_process_test.c harness_process.h
    VERBATIM)
  add_custom_target(shuffler_harness_process_test ALL
    DEPENDS "${CMAKE_CURRENT_BINARY_DIR}/harness_process_test")

  add_executable(shuffler_assertion_test shuffler/assertion_test.cpp "${shuffler_assembly}")
  target_compile_options(shuffler_assertion_test PRIVATE -O1 -Wall -Wextra)
  target_link_options(shuffler_assertion_test PRIVATE -no-pie)
  add_test(NAME shuffler_assertions COMMAND bash
    "${CMAKE_CURRENT_SOURCE_DIR}/../test/assertions_test.sh" "${CMAKE_BINARY_DIR}")

  add_executable(shuffler_unit_test shuffler/unit_test.cpp)
  target_compile_options(shuffler_unit_test PRIVATE
    -O1 -g -Wall -Wextra -fsanitize=address,undefined -fno-sanitize-recover=all)
  target_link_options(shuffler_unit_test PRIVATE -fsanitize=address,undefined)
  add_test(NAME shuffler_unit_test COMMAND shuffler_unit_test)
  set_tests_properties(shuffler_unit_test PROPERTIES
    ENVIRONMENT "ASAN_OPTIONS=detect_leaks=0:quarantine_size_mb=8")
endif()
