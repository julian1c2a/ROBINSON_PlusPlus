#!/bin/bash
# t5b: [A2] VERBATIM con la tabla en CRLF, con BOM, con columnas raras; una entrada que sale de la base y vuelve; y el
# traslado de deuda entre documentos. Repositorio de juguete en el scratchpad.
H=$(cd "$(dirname "$0")" && pwd); T=$H/t5b_repo; rm -rf "$T"; mkdir -p "$T/doc/control"; cd "$T"
git init -q .; git config user.email t@t; git config user.name t; git config core.autocrlf false
doc () { # $1 = fichero  $2 = número de líneas viejas
  { for i in $(seq 1 100); do echo "cabecera $i"; done; for i in $(seq 1 "$2"); do echo "El build tiene 99 jobs ($i)."; done; } > "$1"; }
a2 () { DOCS="X.md Y.md" bash "$H/harness.bash" "$T" A2 2>&1 | grep -E '❌|✓ ning|FAIL=' | tr '\n' ' ' | cut -c1-260; echo; }
tabla () { { echo '# etiqueta	documento	cifra	líneas'; printf '%s\n' "$@"; } > doc/control/a2-deuda.tsv; }
doc X.md 2; doc Y.md 1; tabla 'jobs	X.md	99	2' 'jobs	Y.md	99	1'; git add -A; git commit -qm base; BASE=$(git rev-parse HEAD)
echo "S6 tabla en CRLF (y la base también en CRLF):"
sed -i 's/$/\r/' doc/control/a2-deuda.tsv; git commit -qam crlf; B2=$(git rev-parse HEAD); printf '   '; B_BASE_REF=$B2 a2
echo "S7 tabla con BOM al principio:"
printf '\xef\xbb\xbf' | cat - doc/control/a2-deuda.tsv > t && mv t doc/control/a2-deuda.tsv; printf '   '; B_BASE_REF=$B2 a2
git checkout -qf "$BASE"
echo "S8 una entrada sale de la base (se arregla Y.md y la base avanza) y luego VUELVE:"
doc Y.md 0; tabla 'jobs	X.md	99	2'; git commit -qam "Y arreglado"; B3=$(git rev-parse HEAD)
doc Y.md 1; tabla 'jobs	X.md	99	2' 'jobs	Y.md	99	1'; printf '   '; B_BASE_REF=$B3 a2
git checkout -qf "$BASE"
echo "S9 traslado: se arregla una línea de X.md y aparece una en Y.md (el total no sube):"
doc X.md 1; doc Y.md 2; tabla 'jobs	X.md	99	1' 'jobs	Y.md	99	2'; printf '   '; B_BASE_REF=$BASE a2
git checkout -qf "$BASE"
echo "S10 traslado de CIFRA: se arregla un «99 jobs» de X.md y aparece un «98 jobs» en X.md:"
{ for i in $(seq 1 100); do echo "cabecera $i"; done; echo "El build tiene 99 jobs (1)."; echo "El build tiene 98 jobs (2)."; } > X.md
tabla 'jobs	X.md	98	1' 'jobs	X.md	99	1' 'jobs	Y.md	99	1'; printf '   '; B_BASE_REF=$BASE a2
