import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from imports import load, closure

fol_root = sys.argv[1]
rpp_root = sys.argv[2]
fol = load(fol_root, ['FOL', 'TheoryFramework', 'FOL.lean', 'TheoryFramework.lean'])
rpp = load(rpp_root, ['ROBINSON_PlusPlus'])
allm = dict(fol)
allm.update(rpp)
memo = {}
tool = {'FOL.Tactics', 'FOL.Deduction', 'FOL.Theorems.Impl', 'FOL.Theorems.Neg',
        'FOL.Theorems.Derived', 'FOL.Theorems.Quantifiers', 'FOL.MetaRules', 'FOL.Core'}
n = len(rpp)
with_lean = [m for m in rpp if 'Lean' in closure(allm, m, memo)]
with_tactics = [m for m in rpp if 'FOL.Tactics' in closure(allm, m, memo)]
with_meta = [m for m in rpp if 'FOL.MetaRules' in closure(allm, m, memo)]
print('modulos RPP:', n)
print('  con `Lean` en la clausura (via FOL.Tactics):', len(with_lean))
print('  con FOL.Tactics en la clausura:', len(with_tactics))
print('  con FOL.MetaRules en la clausura:', len(with_meta))
for t in ['ROBINSON_PlusPlus.Meta.GodelTwoPrf', 'ROBINSON_PlusPlus.Meta.Hilbert', 'ROBINSON_PlusPlus.Minimal.Axioms']:
    c = closure(allm, t, memo)
    print(' ', t, ': Lean' if 'Lean' in c else ': sin Lean', '| MetaRules' if 'FOL.MetaRules' in c else '| sin MetaRules',
          '| herramienta FOL:', sorted(x.replace('FOL.', '') for x in c & tool))
print('sin Lean:', sorted(m for m in rpp if m not in with_lean))
direct_tactic_users = [m for m in rpp if 'FOL.Tactics' in rpp[m]]
print('importan FOL.Tactics directamente:', len(direct_tactic_users))
