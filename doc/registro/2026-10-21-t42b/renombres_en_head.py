# renombres_en_head.py — T42b: cuántas apariciones de los seis nombres obsoletos había en HEAD (antes de migrar), en el
# ámbito de migra_deprecados.py: en RPP, ROBINSON_PlusPlus/ y ROBINSON_PlusPlus.lean y los 11 sondeos de control
# (sondeos/CONTROLES.txt); en FOL, FOL/, FOL.lean, TheoryFramework/ y TheoryFramework.lean, MENOS los módulos CONGELADOS
# de FOL (frozen_files.txt: inmutables sin un «thaw», que decide el propietario). Es el número de renombres.
# Y los que quedan FUERA de ese ámbito (los congelados, los sondeos que no son de control, scripts, cuarentena…).
import collections, os, re, subprocess, sys
sys.stdout.reconfigure(encoding='utf-8')
B = os.path.dirname(os.path.abspath(__file__))
VIEJOS = ['if_pos', 'if_neg', 'dif_pos', 'dif_neg', 'if_true', 'if_false']
PAT = re.compile(r"(?<![A-Za-z0-9_'.])(if_pos|if_neg|dif_pos|dif_neg|if_true|if_false)(?![A-Za-z0-9_'!?])")
def git(R, *a):
    return subprocess.run(['git', '-C', R] + list(a), capture_output=True, check=True).stdout.decode('utf-8')
R_RPP = os.path.join(B, 'ROBINSON_PlusPlus')
R_FOL = os.path.join(B, 'FOL')
controles = [l.split('#')[0].strip() for l in git(R_RPP, 'show', 'HEAD:sondeos/CONTROLES.txt').split('\n')]
controles = ['sondeos/' + c for c in controles if c]
congelados = {l.strip() for l in git(R_FOL, 'show', 'HEAD:frozen_files.txt').split('\n') if l.strip()}
def en_ambito(repo, f):
    if repo == 'RPP':
        return f.startswith('ROBINSON_PlusPlus/') or f == 'ROBINSON_PlusPlus.lean' or f in controles
    if f in congelados:
        return False
    return f.startswith('FOL/') or f == 'FOL.lean' or f.startswith('TheoryFramework/') or f == 'TheoryFramework.lean'
dentro = collections.Counter(); fuera = collections.Counter(); por_nombre = collections.Counter()
fich_dentro = collections.Counter()
for repo, R in (('FOL', R_FOL), ('RPP', R_RPP)):
    for f in git(R, 'ls-files', '*.lean').split():
        n = PAT.findall(git(R, 'show', 'HEAD:' + f))
        if not n:
            continue
        z = '%s %s' % (repo, f.split('/')[0] if '/' in f else f)
        if en_ambito(repo, f):
            dentro[z] += len(n); fich_dentro[z] += 1
            for x in n:
                por_nombre[x] += 1
        else:
            fuera[repo + ' ' + f + (' 🧊' if repo == 'FOL' and f in congelados else '')] += len(n)
print('== en el ámbito de la migración (renombrados), en HEAD:')
for z in sorted(dentro):
    print('  %-32s %4d en %3d ficheros' % (z, dentro[z], fich_dentro[z]))
print('  total: %d en %d ficheros' % (sum(dentro.values()), sum(fich_dentro.values())))
for k in VIEJOS:
    print('    %-9s %4d' % (k, por_nombre[k]))
print('== FUERA del ámbito (sin tocar: compilan, con aviso, porque v4.35.0 los conserva obsoletos; 🧊 = congelado de FOL):')
for z in sorted(fuera):
    print('  %-66s %4d' % (z, fuera[z]))
print('  total: %d en %d ficheros (de ellos, congelados: %d en %d)' % (
    sum(fuera.values()), len(fuera), sum(v for k, v in fuera.items() if k.endswith('🧊')),
    sum(1 for k in fuera if k.endswith('🧊'))))
