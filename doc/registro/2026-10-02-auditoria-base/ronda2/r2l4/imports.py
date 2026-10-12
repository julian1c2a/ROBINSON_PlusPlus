import os, re, sys, collections

SEP = os.sep


def load(root, prefixdirs):
    mods = {}
    for prefixdir in prefixdirs:
        base = os.path.join(root, prefixdir)
        if os.path.isfile(base + '.lean'):
            files = [base + '.lean']
        else:
            files = []
        for dp, dn, fn in os.walk(base):
            if 'cuarentena' in dp or '.lake' in dp:
                continue
            for f in fn:
                if f.endswith('.lean'):
                    files.append(os.path.join(dp, f))
        for p in files:
            rel = os.path.relpath(p, root).replace(SEP, '/')
            m = rel[:-5].replace('/', '.')
            txt = open(p, encoding='utf-8').read()
            imps = re.findall(r'^import\s+(\S+)', txt, re.M)
            mods[m] = imps
    return mods


def closure(mods, m, memo):
    if m in memo:
        return memo[m]
    memo[m] = set()
    s = set()
    for i in mods.get(m, []):
        s.add(i)
        if i in mods:
            s |= closure(mods, i, memo)
    memo[m] = s
    return s


if __name__ == '__main__':
    root = sys.argv[1]
    prefs = sys.argv[2].split(',')
    bad = set(sys.argv[3].split(','))
    verbose = len(sys.argv) > 4
    mods = load(root, prefs)
    memo = {}
    dep = [m for m in mods if (closure(mods, m, memo) & bad) or m in bad]
    print('modulos:', len(mods), ' con la capa en su clausura:', len(dep))
    c = collections.Counter()
    for m in mods:
        for i in set(mods[m]) & bad:
            c[i] += 1
    print('importaciones directas:', dict(c))
    if verbose:
        for m in sorted(dep):
            print('  ', m, sorted(set(mods[m]) & bad))
