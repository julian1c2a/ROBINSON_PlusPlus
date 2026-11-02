# -*- coding: utf-8 -*-
"""Regenera DEPENDENCIES.md desde las líneas `import` reales de ROBINSON_PlusPlus.

Uso:  python3 gen-dependencies.py            (escribe DEPENDENCIES.md)
      python3 gen-dependencies.py --check    (sale con 1 si DEPENDENCIES.md no es lo que se generaría)

Nació el 2026-11-02 (T30, ADR-238), portado de `../FOL/gen-dependencies.py` (2026-09-26). El DEPENDENCIES.md a mano
describía desde ADR-115 un árbol de 131 módulos que ya no existía (Block1–8; sus hojas y su nodo más profundo, falsos)
y no nombraba 18 de los de entonces. Un grafo que se escribe a mano se pudre con el árbol; éste se CALCULA, y la CI
comprueba con `--check` que lo versionado es lo que se generaría.
"""
import io, os, re, sys, datetime

ROOT = os.path.dirname(os.path.abspath(__file__))
os.chdir(ROOT)
LIB = 'ROBINSON_PlusPlus'

def rd(p):
    return io.open(p, encoding='utf-8').read()

def imports_de(src):
    return re.findall(r'^\s*import\s+([A-Za-z0-9_.]+)', src, re.M)

# El dominio, como el de [L] y [A] de `check-doc-sync.bash`: TODOS los .lean bajo `ROBINSON_PlusPlus/<capa>/`, a cualquier
# profundidad (lo que compila `globs := #[.andSubmodules `ROBINSON_PlusPlus]`). Los barriles —`ROBINSON_PlusPlus.lean` y
# los `.lean` sueltos de `ROBINSON_PlusPlus/` (hoy `Meta.lean`)— no cuentan como módulos: van en su propia sección.
files = sorted(os.path.join(d, f).replace(os.sep, '/') for d, _, fs in os.walk(LIB) for f in fs
               if f.endswith('.lean') and os.path.join(d, f).replace(os.sep, '/').count('/') >= 2)
barrel_files = [LIB + '.lean'] + sorted(LIB + '/' + f for f in os.listdir(LIB) if f.endswith('.lean'))

def mod(path):
    return path[:-5].replace('/', '.')

mods = [mod(f) for f in files]
MODSET = set(mods)
BARRELSET = {mod(b) for b in barrel_files}
imports = {}
ext_imports = {}
for f in files:
    imps = imports_de(rd(f))
    imports[mod(f)] = sorted(i for i in imps if i in MODSET)
    ext_imports[mod(f)] = sorted(i for i in imps if i not in MODSET and i not in BARRELSET)
    bad = sorted(i for i in imps if i in BARRELSET)
    if bad:
        raise SystemExit(f'{f} importa un barril ({", ".join(bad)}): el grafo de módulos no lo contempla')

imported_by = {m: [] for m in mods}
for m, deps in imports.items():
    for d in deps:
        imported_by[d].append(m)

# nivel = longitud del camino de imports más largo hasta una raíz (un módulo que no importa ninguno de RPP)
level = {}
def lv(m, stack=()):
    if m in level:
        return level[m]
    if m in stack:
        raise SystemExit('ciclo de imports en ' + ' -> '.join(stack + (m,)))
    level[m] = 0 if not imports[m] else 1 + max(lv(d, stack + (m,)) for d in imports[m])
    return level[m]
sys.setrecursionlimit(10000)
for m in mods:
    lv(m)

barrels = {}
for b in barrel_files:
    if os.path.exists(b):
        barrels[b] = imports_de(rd(b))

n_edges = sum(len(v) for v in imports.values())
capas = ('Minimal', 'Meta', 'Full')
n_capa = {c: sum(1 for f in files if f.startswith(f'{LIB}/{c}/')) for c in capas}
otras = sorted({f.split('/')[1] for f in files} - set(capas))
if otras:
    raise SystemExit(f'módulos fuera de las capas {capas}: {otras} ([L] de check-doc-sync.bash también lo dice)')
today = datetime.date.today().isoformat() if '--date' not in sys.argv else sys.argv[sys.argv.index('--date') + 1]

def short(m):
    return m[len(LIB) + 1:] if m.startswith(LIB + '.') else m

def nodo(m):
    return short(m).replace('.', '_')

out = []
w = out.append
w('# Diagrama de Dependencias — ROBINSON_PlusPlus')
w('')
w(f'**Last updated:** {today} — GENERADO por `python3 gen-dependencies.py` desde las líneas `import`; no se edita a mano.')
w('**Autor**: Julián Calderón Almendros')
w('')
w('> ⚠️ Este fichero se **calcula** (T30, ADR‑238). Para actualizarlo: `python3 gen-dependencies.py`; para comprobar')
w('> que está al día: `python3 gen-dependencies.py --check`, que corre en la CI de RPP. El DEPENDENCIES.md escrito a mano')
w('> se sustituyó el 2026‑11‑02: desde ADR‑115 describía un árbol de 131 módulos que ya no existía. Está, tal cual, en la')
w('> historia de git (`git show 6cdd2dd:DEPENDENCIES.md`).')
w('')
w('## Cifras')
w('')
w(f'* **{len(mods)} módulos activos** (Minimal {n_capa["Minimal"]} + Meta {n_capa["Meta"]} + Full {n_capa["Full"]}), '
  f'**{n_edges} aristas** `import` entre ellos, profundidad máxima **{max(level.values())}**. Sin ciclos.')
w('* 1 `lean_lib`, `ROBINSON_PlusPlus`, con `globs := #[.andSubmodules …]`: el build compila el barril')
w('  y TODO su directorio (T15, ADR‑163). Que todo módulo esté además en el cierre de imports del barril lo comprueba [L]')
w('  de `check-doc-sync.bash`, y la cifra de módulos activos de arriba la compara [A] con la suya.')
ext = sorted({i for v in ext_imports.values() for i in v} | {i for v in barrels.values() for i in v
                                                             if i not in MODSET and i not in BARRELSET})
ext_por = {i: sum(1 for m in mods if i in ext_imports[m]) for i in ext}
ext_fol = [i for i in ext if i.split('.')[0] == 'FOL']
ext_otros = [i for i in ext if i not in ext_fol]
w('* Imports externos de FOL, el único `require`: ' + ', '.join(f'`{i}` ({ext_por[i]})' for i in ext_fol)
  + ' —entre paréntesis, cuántos módulos lo importan directamente; los barriles, aparte—. De fuera de FOL: '
  + (', '.join(f'`{i}` ({ext_por[i]})' for i in ext_otros) if ext_otros else 'ninguno') + '.')
w('')
w('## Por niveles (camino de imports más largo hasta una raíz)')
w('')
for L in range(max(level.values()) + 1):
    ms = sorted(m for m in mods if level[m] == L)
    w(f'* **{L}** — ' + ', '.join('`' + short(m) + '`' for m in ms))
w('')
w('## Grafo')
w('')
w('`A --> B` se lee «`A` importa `B`» (de abajo arriba: las raíces, arriba). Sólo las aristas entre módulos de RPP.')
w('')
w('```mermaid')
w('graph BT')
for m in sorted(mods):
    for d in imports[m]:
        w(f'    {nodo(m)}["{short(m)}"] --> {nodo(d)}["{short(d)}"]')
for m in sorted(mods):
    if not imports[m] and not imported_by[m]:
        w(f'    {nodo(m)}["{short(m)}"]')
w('```')
w('')
w('## Tabla')
w('')
w('| módulo | nivel | importa | lo importan |')
w('|---|---|---|---|')
for m in sorted(mods, key=lambda x: (level[x], x)):
    imp = ', '.join('`' + short(d) + '`' for d in imports[m]) or '—'
    if ext_imports[m]:
        imp += ' · externo: ' + ', '.join('`' + i + '`' for i in ext_imports[m])
    by = ', '.join('`' + short(d) + '`' for d in sorted(imported_by[m])) or '—'
    w(f'| `{short(m)}` | {level[m]} | {imp} | {by} |')
w('')
w('## Barriles')
w('')
for b, imps in barrels.items():
    dentro = [i for i in imps if i in MODSET or i in BARRELSET]
    fuera = [i for i in imps if i not in MODSET and i not in BARRELSET]
    w(f'* `{b}` importa {len(imps)}: ' + ', '.join('`' + short(i) + '`' for i in dentro)
      + ('; externos: ' + ', '.join('`' + i + '`' for i in fuera) if fuera else '') + '.')
w('')
text = '\n'.join(out) + '\n'

if '--check' in sys.argv:
    cur = rd('DEPENDENCIES.md') if os.path.exists('DEPENDENCIES.md') else ''
    strip = lambda s: re.sub(r'^\*\*Last updated:\*\*.*$', '', s, flags=re.M)
    if strip(cur) != strip(text):
        print('DEPENDENCIES.md NO está al día: python3 gen-dependencies.py')
        sys.exit(1)
    print('DEPENDENCIES.md al día')
    sys.exit(0)
io.open('DEPENDENCIES.md', 'w', encoding='utf-8', newline='\n').write(text)
print(f'DEPENDENCIES.md: {len(mods)} módulos, {n_edges} aristas, profundidad {max(level.values())}')
