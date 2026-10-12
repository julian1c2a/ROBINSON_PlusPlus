import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from imports import load, closure

root = sys.argv[1]
targets = sys.argv[2].split(',')
mods = load(root, ['FOL', 'TheoryFramework', 'FOL.lean', 'TheoryFramework.lean'])
frozen = set(l.strip()[:-5].replace('/', '.') for l in open(os.path.join(root, 'frozen_files.txt'), encoding='utf-8') if l.strip())
locked = set(l.strip()[:-5].replace('/', '.') for l in open(os.path.join(root, 'locked_files.txt'), encoding='utf-8') if l.strip().endswith('.lean'))
memo = {}
cl = set(targets)
for t in targets:
    cl |= closure(mods, t, memo)
cl = sorted(m for m in cl if m.startswith('FOL') or m.startswith('TheoryFramework'))
fr = [m for m in cl if m in frozen]
lk = [m for m in cl if m in locked and m not in frozen]
fe = [m for m in cl if m not in locked and m not in frozen]
print('clausura de', targets, ':', len(cl), 'modulos')
print('  congelados (%d):' % len(fr), ' '.join(x.replace('FOL.', '') for x in fr))
print('  bloqueados (%d):' % len(lk), ' '.join(x.replace('FOL.', '') for x in lk))
print('  libres (%d):' % len(fe), ' '.join(x.replace('FOL.', '') for x in fe))
print('  contiene MetaRules:', 'FOL.MetaRules' in cl, ' Theorems.Eq:', 'FOL.Theorems.Eq' in cl, ' DecEq:', 'FOL.DecEq' in cl)
