#!/bin/bash
# t13: [A2] (VERBATIM) no mira dos de las cifras que [A] sí mira en la cabecera: «Meta (N +» y «N en `cuarentena/`»; y,
# como [A], sólo la PRIMERA cifra de cada línea. Repositorio de juguete (la base = el propio commit, con su tabla vacía).
H=$(cd "$(dirname "$0")" && pwd); T=$H/t13_repo; rm -rf "$T"; mkdir -p "$T/doc/control"; cd "$T"
git init -q .; git config user.email t@t; git config user.name t
{ for i in $(seq 1 100); do echo "cabecera $i"; done
  echo 'Hoy: 7 módulos en `cuarentena/` y Meta (99 + 3 barriles).'
  echo 'Hoy: el build tiene 133 jobs; el de la semana pasada, también; README: 120 jobs.'; } > X.md
echo '# etiqueta	documento	cifra	líneas' > doc/control/a2-deuda.tsv; git add -A; git commit -qm base
DOCS=X.md QUAR=0 META=112 B_BASE_REF=$(git rev-parse HEAD) bash "$H/harness.bash" "$T" A2 | grep -E '❌|✓ ning|FAIL='
