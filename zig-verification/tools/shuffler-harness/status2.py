#!/usr/bin/env python3
"""Vectors of the class `status2-spill` (K3n): runs of the compiled `shuffle` that end in status 2 and
leave a spill byte changed (`spills_after != spills`). The review K3m found 25 of them in 40,000 random cases;
the files of `native.py` have none.

    python3 -I tools/shuffler-harness/status2.py gen [OUTFILE]    write Lift/Shuffler/Test/data/native-status2.jsonl

Trial i uses `random.Random("<SEED>:status2-spill:<i>")`, with SEED of `native.py`; the parameters of a trial
come from that generator. The trials run in order until COUNT trials give the status 2 with a changed spill byte;
each is a vector, and the header records the number of trials. Build: the committed `shuffler.s` is linked with
`gcc -shared -nostdlib` in SHUFFLER_WORK (default /tmp/shuffler-harness-status2); no Zig is needed. The hash of
`shuffler.s` is in the header."""
import os, sys, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
os.environ.setdefault('SHUFFLER_WORK', '/tmp/shuffler-harness-status2')
import native as N

COUNT = 30
NAME = 'status2-spill'
FILE = 'native-status2.jsonl'


def build():
    os.makedirs(N.WORK, exist_ok=True)
    src = os.path.join(N.ROOT, N.ASM_SRC)
    text = open(src).read()
    open(N.WORK + '/shuf.s', 'w').write('\n'.join(l for l in text.split('\n') if not l.strip().startswith('.hidden')))
    subprocess.run(['gcc', '-shared', '-nostdlib', '-o', N.WORK + '/shuf.so', N.WORK + '/shuf.s'], check=True, cwd=N.WORK)
    return N.sha256(src)


def trial(i):
    rnd = N.rnd_of(NAME, i)
    return N.rand_case(rnd, maxsz=rnd.choice([8, 16, 30]), nvars=rnd.choice([3, 6, 12]), bad=rnd.choice([0.0, 0.02, 0.1]),
                       reach=rnd.choice([2, 2, 3, 4, 5]), spill_rate=0.1, wild=rnd.choice([0.0, 0.2]), allowed=True,
                       odd=rnd.choice([0.0, 0.05]))


def generate():
    N.build = build
    nat = N.Native()
    rows, i = [], 0
    while len(rows) < COUNT:
        x = trial(i)
        y = nat.run(x)
        if y['status'] == 2 and y['spills_after'] != x['spills']:
            rows.append({'id': f'{NAME}/{len(rows)}', 'class': NAME, **x, **y})
        i += 1
        assert i < 1000000, 'too few hits'
    head = N.header(nat, FILE, len(rows), {'class': NAME, 'trials': i})
    return '\n'.join([N.dumps(head)] + [N.dumps(r) for r in rows]) + '\n', i


if __name__ == '__main__':
    if len(sys.argv) in (2, 3) and sys.argv[1] == 'gen':
        text, trials = generate()
        out = sys.argv[2] if len(sys.argv) == 3 else os.path.join(N.DATA, FILE)
        open(out, 'w').write(text)
        print(out, len(text), 'bytes;', COUNT, 'vectors in', trials, 'trials')
    else:
        sys.exit(__doc__)
