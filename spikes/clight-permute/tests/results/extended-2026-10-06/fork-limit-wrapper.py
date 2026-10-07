#!/nix/store/d64q19q1xjdwfhqx6czvrjgrhq0n3lcc-python3-3.14.7/bin/python3
import os, sys
extra=[] if sys.argv[1:]==['--version'] else ['--max-forks=0', '--rng-initial-seed=1']
os.execv('/nix/store/ym6fyvc1y5ng7bpzigmg5db313w4mr88-klee-git-9a36a6782b814fe1fa37439652b875114faa0e20/bin/klee', ['/nix/store/ym6fyvc1y5ng7bpzigmg5db313w4mr88-klee-git-9a36a6782b814fe1fa37439652b875114faa0e20/bin/klee']+extra+sys.argv[1:])
