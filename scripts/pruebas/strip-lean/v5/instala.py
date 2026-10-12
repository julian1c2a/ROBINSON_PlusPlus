# instala.py — copia la v3 de strip-lean.awk a los dos repos: el CÓDIGO idéntico, la cabecera de cada uno.
import io, os
HERE = os.path.dirname(os.path.abspath(__file__))
src = io.open(os.path.join(HERE, 'strip-lean.awk'), encoding='utf-8', newline='').read()
fol_hdr = ("# 🔑 Una definición delicada vive en UN sitio: la usan `check-sorry.bash`, `check-axioms.bash` y\n"
           "# los bloques [A] y [B] de `check-doc-sync.bash`. El CÓDIGO es idéntico al de\n"
           "# `../ROBINSON_PlusPlus/strip-lean.awk` (sólo cambian estas líneas de cabecera), y\n"
           "# `check-doc-sync.bash` de RPP lo comprueba.\n")
rpp_hdr = ("# 🔑 Una definición delicada vive en UN sitio: la usan `check-sorry.bash` y los bloques [A] y [B]\n"
           "# de `check-doc-sync.bash`, aquí y en FOL. El CÓDIGO es idéntico al de `../FOL/strip-lean.awk`\n"
           "# (sólo cambian estas líneas de cabecera), y `check-doc-sync.bash` lo comprueba: si las dos copias\n"
           "# se separan, o falta la de FOL, es rojo.\n")
assert src.count(fol_hdr) == 1
fol = src
rpp = src.replace(fol_hdr, rpp_hdr).replace('v1 (2026-10-03, ADR-116 de RPP)', 'v1 (2026-10-03, ADR-116)')
for path, txt in (('E:/dropbox/github/lean4/FOL/strip-lean.awk', fol),
                  ('E:/dropbox/github/lean4/ROBINSON_PlusPlus/strip-lean.awk', rpp)):
    io.open(path, 'w', encoding='utf-8', newline='').write(txt)
    print('escrito', path, len(txt.encode('utf-8')), 'bytes')
code = lambda t: [l for l in t.split('\n') if not l.startswith('#')]
assert code(fol) == code(rpp), 'el código difiere'
print('código idéntico:', len(code(fol)), 'líneas')
