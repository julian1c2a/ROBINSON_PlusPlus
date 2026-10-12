import os, re, sys

def strip_comments(txt):
    out = []
    i = 0
    n = len(txt)
    depth = 0
    in_str = False
    while i < n:
        c = txt[i]
        if depth == 0 and not in_str and txt.startswith('--', i):
            j = txt.find('\n', i)
            if j == -1:
                break
            i = j
            continue
        if not in_str and txt.startswith('/-', i):
            depth += 1
            i += 2
            continue
        if depth > 0 and txt.startswith('-/', i):
            depth -= 1
            i += 2
            continue
        if depth > 0:
            if c == '\n':
                out.append('\n')
            i += 1
            continue
        if c == '"':
            in_str = not in_str
        out.append(c)
        i += 1
    return ''.join(out)

root = sys.argv[1]
files = sys.argv[2:]
frozen = set(open(os.path.join(root, 'frozen_files.txt'), encoding='utf-8').read().split())
locked = set(open(os.path.join(root, 'locked_files.txt'), encoding='utf-8').read().split())
tot = {'String': 0, 'lit': 0, 'decode': 0}
rows = []
for f in files:
    p = os.path.join(root, f)
    txt = strip_comments(open(p, encoding='utf-8').read())
    lines = txt.split('\n')
    s = sum(1 for l in lines if re.search(r'\bString\b', l))
    lit = sum(len(re.findall(r'"(?:[^"\\]|\\.)*"', l)) for l in lines if not l.strip().startswith('#print') and 'set_option' not in l)
    dec = sum(1 for l in lines if re.search(r'toList|utf8|String\.(mk|data|get|front|back|drop|take|append|length|push|ofList|decEq|toNat|ofByteArray)|\.bytes|ByteArray', l))
    sig = sum(1 for l in lines if re.search(r'(:\s*String\b|String\s*→|→\s*String\b|\(\w+\s*:\s*String\))', l))
    st = 'FROZEN' if f in frozen else ('locked' if f in locked else 'free')
    if s or lit or dec:
        rows.append((f, st, s, sig, lit, dec))
    tot['String'] += s
    tot['lit'] += lit
    tot['decode'] += dec
for r in sorted(rows, key=lambda r: (r[1] != 'FROZEN', r[0])):
    print('%-38s %-6s String=%-3d firma=%-3d literales=%-3d decodif=%-3d' % r)
print('TOTAL', tot, 'ficheros con algo:', len(rows), 'congelados con String en codigo:', sum(1 for r in rows if r[1] == 'FROZEN' and r[2] > 0))
