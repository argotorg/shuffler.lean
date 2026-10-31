# The flags turn off the hardening that the nix gcc wrapper adds (frame pointer,
# register zeroing, CET, stack probes), and `.ident`, which the Kraken directive
# filter keeps.
CFLAGS_ASM = -O1 -fno-ident -fno-asynchronous-unwind-tables -fcf-protection=none \
	-fomit-frame-pointer -fzero-call-used-regs=skip -fno-stack-protector -fno-pic \
	-fno-stack-clash-protection
# build_bottom_up.cpp is freestanding: no exceptions, RTTI, guard variables or C++ library.
CXXFLAGS_ASM = $(CFLAGS_ASM) -std=c++20 -ffreestanding -fno-exceptions -fno-rtti \
	-fno-threadsafe-statics -nostdlib++

all: permute.S harness build_bottom_up.S bbu_harness pop_harness surplus_harness lowest_harness unit_test

permute.S: permute.c
	$(CC) $(CFLAGS_ASM) -S $< -o $@

# The labels get the prefix .LB (sed), then the names .LB.NAME.K (labels.awk): K counts the labels
# of the function NAME, so a label name depends only on its own function. bbu/NAME.S holds the
# function NAME. NAME is the g++ (Itanium) name, for example
# _ZN12_GLOBAL__N_18Emission7produceE11StackOffset, or build_bottom_up, which is extern "C".
build_bottom_up.S: build_bottom_up.cpp labels.awk
	$(CXX) $(CXXFLAGS_ASM) -S $< -o - | sed 's/^\.L\([0-9]\)/.LB\1/; s/\(	j[a-z]*	\)\.L\([0-9]\)/\1.LB\2/' \
		| awk -f labels.awk > $@
	rm -rf bbu && mkdir bbu
	awk '/^[a-zA-Z_][a-zA-Z0-9_]*:$$/ { f = "bbu/" substr($$0, 1, length($$0) - 1) ".S" } f { print > f } /^\t\.size/ { f = "" }' $@

harness: harness.c permute.S
	$(CC) -O1 -o $@ harness.c permute.S

bbu_harness: bbu_harness.c build_bottom_up.S
	$(CC) -O1 -no-pie -o $@ bbu_harness.c build_bottom_up.S

pop_harness: pop_harness.c build_bottom_up.S
	$(CC) -O1 -no-pie -o $@ pop_harness.c build_bottom_up.S

surplus_harness: surplus_harness.c build_bottom_up.S
	$(CC) -O1 -no-pie -o $@ surplus_harness.c build_bottom_up.S

lowest_harness: lowest_harness.c build_bottom_up.S
	$(CC) -O1 -no-pie -o $@ lowest_harness.c build_bottom_up.S

# The unit tests, hosted and with the sanitizers. They include build_bottom_up.cpp. Run them with
# ASAN_OPTIONS=detect_leaks=0 where LeakSanitizer cannot run (under ptrace).
unit_test: unit_test.cpp build_bottom_up.cpp
	$(CXX) -std=c++20 -O1 -g -Wall -Wextra -fsanitize=address,undefined -fno-sanitize-recover=all -o $@ unit_test.cpp

clean:
	rm -f harness bbu_harness pop_harness surplus_harness lowest_harness unit_test

.DELETE_ON_ERROR:

.PHONY: all clean
