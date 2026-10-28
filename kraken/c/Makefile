# The flags turn off the hardening that the nix gcc wrapper adds (frame pointer,
# register zeroing, CET), and `.ident`, which the Kraken directive filter keeps.
CFLAGS_ASM = -O1 -fno-ident -fno-asynchronous-unwind-tables -fcf-protection=none \
	-fomit-frame-pointer -fzero-call-used-regs=skip -fno-stack-protector -fno-pic

all: permute.S harness

permute.S: permute.c
	$(CC) $(CFLAGS_ASM) -S $< -o $@

harness: harness.c permute.S
	$(CC) -O1 -o $@ harness.c permute.S

clean:
	rm -f harness

.PHONY: all clean
