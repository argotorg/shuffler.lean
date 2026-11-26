#!/usr/bin/env python3
"""Native harness (K3b) of the compiled Zig function `solidity_shuffler_shuffle`.

    python3 -I tools/shuffler-harness/native.py gen [OUTDIR]     write Lift/Shuffler/Test/data/native-*.jsonl
    python3 -I tools/shuffler-harness/native.py selfcheck        run the self-check (see README.md)

Build (into WORK, default /tmp/shuffler-harness; no file of the repository changes): the committed compile command
of Lift/LLVM/data/shuffler/src/README.md (zig 0.17.1, ZIG overrides the path) makes shuffler.bc and shuffler.s; the
script stops unless shuffler.s is byte-equal to Lift/LLVM/data/shuffler/shuffler.s; `gcc -shared -nostdlib` links
it (the `.hidden` lines removed) into shuf.so. The functions are called through ctypes with the 96-byte record
`Shuffle` of types.json. Each case runs twice, with a zero workspace and with a workspace of random bytes (and
random bytes in the padding of the record); the script stops if the two results differ.
Inputs: seeded (SEED); the generator of each class is below."""
import ctypes, hashlib, json, os, random, subprocess, sys, time

SEED = 20261119
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
WORK = os.environ.get('SHUFFLER_WORK', '/tmp/shuffler-harness')
ZIG = os.environ.get('ZIG', 'zig')
ZIG_SRC = 'Lift/LLVM/data/shuffler/src/shuffler.zig'
ASM_SRC = 'Lift/LLVM/data/shuffler/shuffler.s'
DATA = os.path.join(ROOT, 'Lift/Shuffler/Test/data')
WS = 357672          # solidity_shuffler_workspaceSize
MAXN = 1024
NONE = (1 << 64) - 1
M64 = (1 << 64) - 1


# ---------------------------------------------------------------- build and call

def sha256(path):
    with open(path, 'rb') as source:
        return hashlib.sha256(source.read()).hexdigest()


def build():
    version = subprocess.check_output([ZIG, 'version'], text=True).strip()
    if version != '0.17.1':
        raise RuntimeError('Zig 0.17.1 is required; got ' + version)
    os.makedirs(WORK, exist_ok=True)
    env = dict(os.environ, ZIG_GLOBAL_CACHE_DIR=WORK + '/zig-cache', ZIG_LOCAL_CACHE_DIR=WORK + '/zig-local')
    bc, s = WORK + '/shuffler.bc', WORK + '/shuffler.s'
    flags = ['-target', 'x86_64-linux-none', '-mcpu=baseline']
    subprocess.run([ZIG, 'build-obj', os.path.join(ROOT, ZIG_SRC), *flags, '-O', 'ReleaseSmall', '-fPIC', '-fstrip',
                    '-fsingle-threaded', '-fomit-frame-pointer', '-fno-unwind-tables', '-fno-stack-check',
                    '-fno-stack-protector', '-fno-builtin', '-fno-compiler-rt', '-fno-ubsan-rt', '-fno-emit-bin',
                    '-femit-llvm-bc=' + bc], check=True, env=env, cwd=WORK)
    subprocess.run([ZIG, 'cc', *flags, '-S', '-O2', '-Xclang', '-disable-llvm-passes', '-fPIC', '-fno-verbose-asm',
                    '-fno-addrsig', '-Wno-override-module', '-Wno-unused-command-line-argument', bc, '-o', s],
                   check=True, env=env, cwd=WORK)
    assert sha256(s) == sha256(os.path.join(ROOT, ASM_SRC)), 'the build of the Zig source is not the committed shuffler.s'
    text = open(s).read()
    open(WORK + '/shuf.s', 'w').write('\n'.join(l for l in text.split('\n') if not l.strip().startswith('.hidden')))
    subprocess.run(['gcc', '-shared', '-nostdlib', '-o', WORK + '/shuf.so', WORK + '/shuf.s'], check=True, cwd=WORK)
    return sha256(s)


class Native:
    def __init__(self):
        self.asm_sha = build()
        lib = ctypes.CDLL(WORK + '/shuf.so')
        self.fn = lib.solidity_shuffler_shuffle
        self.fn.argtypes = [ctypes.c_void_p]
        self.fn.restype = ctypes.c_uint32
        assert lib.solidity_shuffler_workspaceSize() == WS
        assert lib.solidity_shuffler_workspaceAlignment() == 8
        self.ws = (ctypes.c_uint64 * (WS // 8))()
        self.noise = random.Random('noise')

    def call(self, x, garbage):
        """One call. `x` has source, target (lists of u64), spills (list of bytes), reach, allowed. Output: dict."""
        if garbage:
            ctypes.memmove(self.ws, self.noise.randbytes(WS), WS)
        else:
            ctypes.memset(self.ws, 0, WS)
        S = (ctypes.c_uint64 * max(1, len(x['source'])))(*x['source'])
        T = (ctypes.c_uint64 * max(1, len(x['target'])))(*x['target'])
        SP = (ctypes.c_uint8 * len(x['spills']))(*x['spills'])
        rec = (ctypes.c_uint64 * 12)()
        if garbage:   # the padding of the record and the output fields are not inputs
            for i in (8, 9, 10, 11):
                rec[i] = self.noise.getrandbits(64)
        rec[0], rec[1] = ctypes.addressof(S), len(x['source'])
        rec[2], rec[3] = ctypes.addressof(T), len(x['target'])
        rec[4], rec[5] = ctypes.addressof(SP), ctypes.addressof(self.ws)
        rec[6] = x['reach']
        rec[7] = int(x['allowed']) | (self.noise.getrandbits(56) << 8 if garbage else 0)
        status = self.fn(ctypes.addressof(rec))
        out = {'status': status}
        if status == 0:
            n = len(x['target'])
            lo, hi = ctypes.addressof(self.ws), ctypes.addressof(self.ws) + WS
            assert rec[10] <= 10240 and all(lo <= p and p + sz <= hi for p, sz in
                                            ((rec[8], 8 * n), (rec[9], 12 * rec[10]), (rec[11], 8 * n))), 'output outside the workspace'
            out['stack'] = list((ctypes.c_uint64 * max(1, n)).from_address(rec[8]))[:n]
            raw = ctypes.string_at(rec[9], 12 * rec[10])
            out['trace'] = [[raw[12 * i], raw[12 * i + 1], int.from_bytes(raw[12 * i + 4:12 * i + 12], 'little')]
                            for i in range(rec[10])]
            out['sources'] = [None if w == NONE else w for w in
                              list((ctypes.c_uint64 * max(1, n)).from_address(rec[11]))[:n]]
        out['spills_after'] = list(SP)
        return out

    def run(self, x):
        a, b = self.call(x, False), self.call(x, True)
        assert a == b, ('workspace dependence', x)
        return a


# ---------------------------------------------------------------- slots

def slot(payload, kind, op, pad=0):
    return payload | kind << 32 | op << 40 | pad << 48


def eqkey(w): return w & ((1 << 48) - 1)           # `eql`: the padding is dropped
def kind(w): return (w >> 32) & 0xff
def opc(w): return (w >> 40) & 0xff
def is_var(w): return kind(w) == 0 and opc(w) != 0


class Gen:
    """The slots of one case. Identities (id, opcode, payload) are fixed per case so that equal slots occur."""
    def __init__(self, rnd, nvars, bigids=False, padall=False, odd=0.0):
        self.rnd, self.odd, self.padall = rnd, odd, padall
        self.ids = sorted(rnd.sample(range(1000), nvars)) if bigids else list(range(nvars))
        self.nspills = (max(self.ids) + 1 if self.ids else 1) + rnd.randrange(3)
        self.op = {i: (3 if rnd.random() < 0.5 else rnd.randrange(1, 256)) for i in self.ids}
        self.lits = [rnd.getrandbits(32) if rnd.random() < 0.5 else rnd.randrange(4) for _ in range(3)]
        self.calls = [(rnd.getrandbits(32) if rnd.random() < 0.3 else rnd.randrange(3), rnd.randrange(256)) for _ in range(2)]
        self.labels = [(rnd.getrandbits(32) if rnd.random() < 0.3 else rnd.randrange(3), rnd.randrange(256)) for _ in range(2)]

    def pad(self):
        return self.rnd.getrandbits(16) if self.padall or self.rnd.random() < 0.5 else 0

    def var(self, i=None):
        i = self.rnd.choice(self.ids) if i is None else i
        return slot(i, 0, self.op[i], self.pad())

    def lit(self): return slot(self.rnd.choice(self.lits), 0, 0, self.pad())
    def junk(self): return slot(self.rnd.getrandbits(32) if self.rnd.random() < 0.2 else 0, 1, self.rnd.randrange(256), self.pad())
    def call(self): p, o = self.rnd.choice(self.calls); return slot(p, 2, o, self.pad())
    def label(self): p, o = self.rnd.choice(self.labels); return slot(p, 3, o, self.pad())

    def oddkind(self):
        return slot(self.rnd.getrandbits(32), self.rnd.randrange(4, 256), self.rnd.randrange(256), self.pad())

    def spills(self, rate):
        rnd = self.rnd
        return [rnd.choice([1, 7, 255]) if rnd.random() < rate else 0 for _ in range(self.nspills)]


def source_slots(g, n, wv=9):
    out = []
    for _ in range(n):
        k = g.rnd.randrange(16)
        out.append(g.oddkind() if g.odd and g.rnd.random() < g.odd else
                   g.var() if k < wv else g.lit() if k <= 10 else g.junk() if k <= 12 else g.call() if k <= 14 else g.label())
    return out


def target_slots(g, n, source, spills, bad=0.0, wild=0.0, force_bad=False):
    """A target that meets the contract (each variable on the source or spilled, the labels counted), except that
    `bad` is the probability that an unavailable variable stays, and `force_bad` puts one such variable in."""
    rnd = g.rnd
    avail = {eqkey(s) for s in source}
    labels = {}
    for s in source:
        if kind(s) == 3: labels[eqkey(s)] = labels.get(eqkey(s), 0) + 1
    out = []
    for _ in range(n):
        k = rnd.randrange(16)
        if rnd.random() < wild: out.append(g.junk()); continue
        if k < 9:
            c = rnd.choice(source) if source and rnd.random() < 0.5 else g.var()
            ok = is_var(c) and (c & 0xffffffff < len(spills) and spills[c & 0xffffffff] != 0 or eqkey(c) in avail)
            out.append(c if ok or rnd.random() < bad else g.junk())
        elif k <= 10: out.append(g.lit())
        elif k <= 12: out.append(g.junk())
        elif k <= 14: out.append(g.call())
        else:
            c = g.label()
            if labels.get(eqkey(c), 0) > 0 or rnd.random() < bad:
                labels[eqkey(c)] = labels.get(eqkey(c), 0) - 1
                out.append(c)
            else:
                out.append(g.junk())
    if force_bad and out:
        # a variable id that is not on the source and not spilled (a fresh id; the spill buffer has a byte for it)
        i = rnd.randrange(len(out))
        fresh = [j for j in g.ids if eqkey(slot(j, 0, g.op[j])) not in {eqkey(s) for s in source} and not spills[j]]
        out[i] = g.var(rnd.choice(fresh)) if fresh else out[i]
    return out


def mix_reach(rnd):
    return rnd.choice([2, 3, 4, 5, 6, 15, 16, 16, 16, 17, 255, 256, M64])


def case(g, source, target, spills, reach, allowed):
    return {'source': source, 'target': target, 'spills': spills, 'reach': reach, 'allowed': allowed}


def rand_case(rnd, maxsz=24, nvars=6, bad=0.0, reach=16, bigids=False, padall=False, odd=0.0, spill_rate=0.125,
              wild=0.0, wv=9, src_n=None, tgt_n=None, force_bad=False, allowed=None):
    g = Gen(rnd, nvars, bigids, padall, odd)
    source = source_slots(g, rnd.randint(0, maxsz) if src_n is None else src_n, wv)
    spills = g.spills(spill_rate)
    target = target_slots(g, rnd.randint(0, maxsz) if tgt_n is None else tgt_n, source, spills, bad, wild, force_bad)
    return case(g, source, target, spills, reach() if callable(reach) else reach,
                rnd.random() < 0.5 if allowed is None else allowed)


def perm_case(rnd, n, reach, allowed, spill_rate=0.0, dup=False, padall=False):
    """n variables on the source, the target a permutation of them (a part of them, with copies, if `dup`)."""
    g = Gen(rnd, max(1, n), padall=padall)
    source = [g.var(i) for i in range(n)] if not dup else [g.var(rnd.randrange(max(1, n // 2))) for _ in range(n)]
    target = source[:]
    rnd.shuffle(target)
    if dup: target = [rnd.choice(source) for _ in range(rnd.randint(0, n))] if source else []
    return case(g, source, target, g.spills(spill_rate), reach, allowed)


# ---------------------------------------------------------------- the classes

def rnd_of(name, i):
    return random.Random(f'{SEED}:{name}:{i}')


def reach_class(name, r, count, mkreach=None):
    cs = []
    for i in range(count):
        rnd = rnd_of(name, i)
        if i % 4 == 0:
            cs.append(perm_case(rnd, rnd.randint(2, 30), r, rnd.random() < 0.5, spill_rate=0.1, dup=rnd.random() < 0.3))
        else:
            cs.append(rand_case(rnd, maxsz=40, nvars=rnd.choice([6, 20, 40]), bad=0.01, reach=r))
    return cs


def size_class(n):
    """Sizes n (and 1025 above the limit). Exactly n slots on the source and on the target where it makes sense."""
    name = f'size-{n}'
    cs, R = [], lambda k: rnd_of(name, k)
    ident = Gen(R(0), n)
    src = [ident.var(i) for i in range(n)]
    cs.append(case(ident, src, src[:], [0] * ident.nspills, 16, False))                       # in place
    cs.append(case(ident, src, src[::-1], [0] * ident.nspills, 16, False))                    # reversed, no spilling
    cs.append(case(ident, src, src[::-1], [0] * ident.nspills, 16, True))                     # reversed, spilling
    cs.append(case(ident, src, src[::-1], [0] * ident.nspills, n if n > 2 else 2, True))      # reversed, reach n
    cs.append(case(ident, src, src[::-1], [0] * ident.nspills, M64, False))                   # reversed, reach 2^64-1
    cs.append(case(ident, [], [ident.lit() for _ in range(n)], [0] * ident.nspills, 16, False))  # literals from nothing
    cs.append(case(ident, src, [], [0] * ident.nspills, 16, False))                           # to the empty stack
    cs.append(case(ident, [], [ident.junk() for _ in range(n)], [0] * ident.nspills, 16, True))  # junk from nothing
    for k in range(1, 4 if n >= 1024 else 9):
        rnd = R(k)
        cs.append(rand_case(rnd, nvars=rnd.choice([3, 6, 20, 64]) if n >= 16 else 3, src_n=n, tgt_n=n,
                            reach=mix_reach(rnd) if k % 2 else 16, allowed=k % 3 != 0, bad=0.0, wild=0.1 * (k % 3)))
    if n >= 1024:
        rnd = R(50)
        cs.append(perm_case(rnd, n, 16, True, dup=False))
        cs.append(perm_case(rnd, n, 1024, True, dup=True))
    return name, cs


def size_over():
    name, cs = 'size-1025', []
    for k in range(6):
        rnd = rnd_of(name, k)
        g = Gen(rnd, 6)
        n = 1025 + (k >= 4) * rnd.randrange(1, 40)
        big = [g.var() for _ in range(n)]
        small = [g.var() for _ in range(rnd.randrange(0, 20))]
        if k % 3 == 0: cs.append(case(g, big, small, g.spills(0.1), 16, True))
        elif k % 3 == 1: cs.append(case(g, small, big, g.spills(0.9), 16, False))
        else: cs.append(case(g, big, big[:], g.spills(0.0), 16, True))
    return name, cs


def blocked_search(count, name='blocked'):
    """Random deep stacks with a small reach until `count` cases give Blocked (status 1). Returns cases, tries."""
    cs, tries, nat, first = [], 0, Native.instance, 0
    i = 0
    while len(cs) < count:
        rnd = rnd_of(name, i); i += 1
        n = rnd.randint(3, 20)
        c = perm_case(rnd, n, rnd.choice([2, 3, 4, 5, 6]), rnd.random() < 0.3, dup=rnd.random() < 0.2)
        tries += 1
        if nat.run(c)['status'] == 1:
            first = first or tries
            cs.append(c)
        assert tries < 100000, 'no Blocked found'
    return cs, tries, first


def wildcard_class(name='wildcard', count=60):
    cs = []
    for i in range(count):
        rnd = rnd_of(name, i)
        cs.append(rand_case(rnd, maxsz=rnd.choice([10, 24, 50]), nvars=rnd.choice([2, 3, 6]), reach=rnd.choice([2, 3, 16]),
                            wild=rnd.choice([0.3, 0.5, 0.7]), wv=rnd.choice([9, 13]), spill_rate=rnd.choice([0.0, 0.3])))
    return cs


def unavailable_class(name='unavailable', count=60):
    """A target variable that is not on the source and not spilled (2 of 3), a target return label that the source
    does not have (1 of 3). Each case breaks the contract at one place, so the status is 2."""
    cs = []
    for i in range(count):
        rnd = rnd_of(name, i)
        c = rand_case(rnd, maxsz=30, nvars=rnd.choice([6, 12]), spill_rate=0.2)
        g = Gen(rnd_of(name + '-g', i), 1)
        if i % 3 == 2:
            c['source'] = [s for s in c['source'] if kind(s) != 3]
            c['target'].insert(rnd.randint(0, len(c['target'])), slot(rnd.randrange(3), 3, 5, rnd.getrandbits(16)))
        else:
            v = rnd.randrange(len(c['spills']))
            c['source'] = [s for s in c['source'] if not (is_var(s) and s & 0xffffffff == v)]
            c['spills'][v] = 0
            c['target'].insert(rnd.randint(0, len(c['target'])), slot(v, 0, 3, rnd.getrandbits(16)))
        cs.append(c)
    return cs


def duplicated_class(name='duplicated', count=60):
    cs = []
    for i in range(count):
        rnd = rnd_of(name, i)
        cs.append(rand_case(rnd, maxsz=30, nvars=rnd.choice([1, 2, 3]), reach=rnd.choice([2, 3, 16]), wv=13,
                            spill_rate=rnd.choice([0.0, 0.5])))
    return cs


def padding_class(name='padding', count=60):
    cs = []
    for i in range(count):
        rnd = rnd_of(name, i)
        cs.append(rand_case(rnd, maxsz=30, nvars=rnd.choice([3, 6, 20]), reach=mix_reach(rnd), padall=True, bad=0.01))
    return cs


def spill_class(name='spill-bytes', count=60):
    cs = []
    for i in range(count):
        rnd = rnd_of(name, i)
        c = rand_case(rnd, maxsz=24, nvars=rnd.choice([6, 12]), reach=rnd.choice([2, 3, 4, 16]), spill_rate=0.6, allowed=i % 2 == 0)
        cs.append(c)
    return cs


def empty_class():
    cs = []
    rnd = rnd_of('empty', 0)
    g = Gen(rnd, 6)
    cs.append(case(g, [], [], [0] * 8, 16, False))
    cs.append(case(g, [], [], [0] * 8, 16, True))
    cs.append(case(g, [], [], [1] * 8, 2, True))
    cs.append(case(g, [], [], [0], M64, False))
    cs.append(case(g, [g.var(), g.junk(), g.lit()], [], g.spills(0.5), 16, False))        # empty target
    cs.append(case(g, [], [g.lit(), g.junk(), g.call()], g.spills(0.5), 16, False))       # empty source
    cs.append(case(g, [g.var(0)], [], g.spills(0.0), 2, True))
    cs.append(case(g, [], [g.var(0)], [1] * g.nspills, 16, True))                          # a spilled variable from nothing
    return cs


# ---------------------------------------------------------------- the whole set

def inputs():
    out = []   # (file, class, input)
    def add(f, cls, cs):
        out.extend((f, cls, c) for c in cs)
    R = 'native-random.jsonl'
    B = 'native-boundary.jsonl'
    G = 'native-big.jsonl'
    add(R, 'random-small', [rand_case(rnd_of('random-small', i), reach=16, padall=False) for i in range(300)])
    add(R, 'random-mixed', [rand_case(rnd_of('random-mixed', i), maxsz=70, nvars=rnd_of('rv', i).choice([6, 20, 50]),
                                      bad=0.01, reach=mix_reach(rnd_of('rr', i))) for i in range(300)])
    add(R, 'random-bigids', [rand_case(rnd_of('random-bigids', i), maxsz=30, nvars=rnd_of('bv', i).choice([4, 12, 30]),
                                       bigids=True, reach=mix_reach(rnd_of('br', i))) for i in range(60)])
    add(R, 'random-oddkind', [rand_case(rnd_of('random-oddkind', i), maxsz=30, nvars=6, odd=0.03, bad=0.0,
                                        reach=mix_reach(rnd_of('or', i))) for i in range(60)])
    add(B, 'empty', empty_class())
    for n in (1, 2, 16, 17):
        name, cs = size_class(n)
        add(B, name, cs)
    for r in (0, 1, 2, 15, 16, 17, M64):
        name = 'reach-max' if r == M64 else f'reach-{r}'
        add(B, name, reach_class(name, r, 40))
    add(B, 'wildcard', wildcard_class())
    add(B, 'unavailable', unavailable_class())
    add(B, 'duplicated', duplicated_class())
    add(B, 'padding', padding_class())
    add(B, 'spill-bytes', spill_class())
    name, cs = size_class(1024); add(G, name, cs)
    name, cs = size_over(); add(G, name, cs)
    return out


def header(nat, f, n, extra):
    with open(os.path.join(ROOT, 'SOURCE-MANIFEST.json')) as source:
        manifest = json.load(source)
    return {'header': True, 'file': f, 'cases': n, 'seed': SEED, 'harness': 'tools/shuffler-harness/native.py',
            'zig_source': ZIG_SRC, 'zig_sha256': sha256(os.path.join(ROOT, ZIG_SRC)),
            'zig_commit': manifest['soliditySource']['commit'], 'asm_sha256': nat.asm_sha,
            'zig_version': '0.17.1', 'format': 'tools/shuffler-harness/README.md', **extra}


def dumps(o):
    return json.dumps(o, separators=(',', ':'))


def generate():
    """All files as {name: text}, and the statistics."""
    nat = Native.instance = Native()
    files, stats = {}, {'by_class': {}, 'tries_blocked': None, 'first_blocked_try': None, 'max_trace': 0, 'over_capacity': 0, 'blocked_random': 0}
    ins = inputs()
    bl, tries, first = blocked_search(40)
    stats['tries_blocked'], stats['first_blocked_try'] = tries, first
    ins += [('native-boundary.jsonl', 'blocked', c) for c in bl]
    names = sorted({f for f, _, _ in ins})
    counters = {}
    for f in names:
        lines = []
        for fi, cls, x in ins:
            if fi != f: continue
            k = counters[cls] = counters.get(cls, -1) + 1
            y = nat.run(x)
            row = {'id': f'{cls}/{k}', 'class': cls, **x, **y}
            lines.append(dumps(row))
            s = stats['by_class'].setdefault(cls, {0: 0, 1: 0, 2: 0, 'n': 0})
            s[y['status']] += 1; s['n'] += 1
            if y['status'] == 0:
                stats['max_trace'] = max(stats['max_trace'], len(y['trace']))
                stats['over_capacity'] += len(y['trace']) > 10240
        files[f] = '\n'.join([dumps(header(nat, f, len(lines), {'blocked_search_tries': tries, 'blocked_first_try': first} if f == 'native-boundary.jsonl' else {}))] + lines) + '\n'
    return files, stats


def report(stats):
    tot = {0: 0, 1: 0, 2: 0, 'n': 0}
    for cls, s in stats['by_class'].items():
        print(f'{cls:16} n={s["n"]:4}  done={s[0]:4} blocked={s[1]:3} assertion={s[2]:3}')
        for k in tot: tot[k] += s[k]
    print(f'total n={tot["n"]} done={tot[0]} blocked={tot[1]} assertion(status 2)={tot[2]}; largest trace {stats["max_trace"]};'
          f' traces over 10240: {stats["over_capacity"]}; blocked search: first at try {stats["first_blocked_try"]}, 40 after {stats["tries_blocked"]} tries')


def main_gen(outdir):
    t = time.time()
    files, stats = generate()
    os.makedirs(outdir, exist_ok=True)
    for f, text in files.items():
        open(os.path.join(outdir, f), 'w').write(text)
        print(f, len(text), 'bytes')
    report(stats)
    print('time %.1f s' % (time.time() - t))


def selfcheck():
    files, stats = generate()
    nat = Native.instance
    # 1. the same input twice gives the same output
    rows = [json.loads(l) for l in files['native-random.jsonl'].split('\n')[1:] if l]
    xs = [{k: r[k] for k in ('source', 'target', 'spills', 'reach', 'allowed')} for r in rows]
    again = sum(nat.run(x) == {k: r[k] for k in r if k in ('status', 'stack', 'trace', 'sources', 'spills_after')}
                for x, r in zip(xs, rows))
    assert again == len(xs), 'a rerun differs'
    print('rerun: %d of %d outputs equal' % (again, len(xs)))
    # 2. a changed input changes the output: the harness reads the native outputs
    def changed(f):
        return sum(nat.run(f(x)) != nat.run(x) for x in xs)
    c_reach1 = changed(lambda x: {**x, 'reach': 1})
    c_reach2 = changed(lambda x: {**x, 'reach': 2})
    c_allowed = changed(lambda x: {**x, 'allowed': not x['allowed']})
    c_swap = changed(lambda x: {**x, 'target': x['target'][::-1]})
    print('changed outputs of %d: reach 1 %d, reach 2 %d, spilling flipped %d, target reversed %d' %
          (len(xs), c_reach1, c_reach2, c_allowed, c_swap))
    assert all(nat.run({**x, 'reach': 1})['status'] == 2 for x in xs), 'reach 1 must give status 2'
    assert c_reach2 > 0 and c_allowed > 0 and c_swap > 0
    # 3. the vectors regenerate byte for byte from the committed files
    for f, text in files.items():
        old = open(os.path.join(DATA, f)).read()
        assert old == text, f'{f} differs from the committed file'
        print(f, 'equals the committed file')
    print('selfcheck passed')


if __name__ == '__main__':
    if len(sys.argv) >= 2 and sys.argv[1] == 'gen':
        main_gen(sys.argv[2] if len(sys.argv) > 2 else DATA)
    elif len(sys.argv) == 2 and sys.argv[1] == 'selfcheck':
        selfcheck()
    else:
        sys.exit(__doc__)
