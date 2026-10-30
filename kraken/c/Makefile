# The flags turn off the hardening that the nix gcc wrapper adds (frame pointer,
# register zeroing, CET, stack probes), and `.ident`, which the Kraken directive
# filter keeps.
CFLAGS_ASM = -O1 -fno-ident -fno-asynchronous-unwind-tables -fcf-protection=none \
	-fomit-frame-pointer -fzero-call-used-regs=skip -fno-stack-protector -fno-pic \
	-fno-stack-clash-protection
# build_bottom_up.cpp is freestanding: no exceptions, RTTI, guard variables or C++ library.
CXXFLAGS_ASM = $(CFLAGS_ASM) -std=c++20 -ffreestanding -fno-exceptions -fno-rtti \
	-fno-threadsafe-statics -nostdlib++

all: permute.S harness build_bottom_up.S bbu_harness

permute.S: permute.c
	$(CC) $(CFLAGS_ASM) -S $< -o $@

# The labels get the prefix .LB: the proofs use the .LB names. bbu/NAME.S holds the
# function NAME. NAME is the g++ (Itanium) name, for example
# _ZN12_GLOBAL__N_18Emission7produceE11StackOffset, or build_bottom_up, which is extern "C".
build_bottom_up.S: build_bottom_up.cpp
	$(CXX) $(CXXFLAGS_ASM) -S $< -o - | sed 's/^\.L\([0-9]\)/.LB\1/; s/\(	j[a-z]*	\)\.L\([0-9]\)/\1.LB\2/' > $@
	rm -rf bbu && mkdir bbu
	awk '/^[a-zA-Z_][a-zA-Z0-9_]*:$$/ { f = "bbu/" substr($$0, 1, length($$0) - 1) ".S" } f { print > f } /^\t\.size/ { f = "" }' $@

harness: harness.c permute.S
	$(CC) -O1 -o $@ harness.c permute.S

bbu_harness: bbu_harness.c build_bottom_up.S
	$(CC) -O1 -no-pie -o $@ bbu_harness.c build_bottom_up.S

clean:
	rm -f harness bbu_harness

.PHONY: all clean
