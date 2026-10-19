#!/bin/bash
# t5: el trinquete de [A2] en un repositorio de JUGUETE (en el scratchpad). Corre el bloque [A2] VERBATIM (harness.bash).
# Un documento X.md: 100 líneas de cabecera y, en el cuerpo, N líneas «El build tiene 99 jobs.» (JOBS real = 133).
H=$(cd "$(dirname "$0")" && pwd)
T=$H/t5_repo; rm -rf "$T"; mkdir -p "$T/doc/control"; cd "$T"
git init -q .; git config user.email t@t; git config user.name t; git config core.autocrlf false
doc () { { for i in $(seq 1 100); do echo "cabecera $i"; done; for i in $(seq 1 "$1"); do echo "El build tiene 99 jobs (línea $i)."; done; } > X.md; }
a2 () { DOCS=X.md bash "$H/harness.bash" "$T" A2 2>&1 | grep -E '❌|⚠️|✓|deuda declarada|FAIL='; }
commit () { git add -A; git commit -qm "$1"; }
echo "===== S0: base SIN tabla y 2 líneas viejas; --a2-deuda-inicial (la creación)"
doc 2; echo "X.md" > docs.list; commit base0
B_BASE_REF=$(git rev-parse HEAD) A2_DEUDA_MODO=2 a2; cat doc/control/a2-deuda.tsv | grep -v '^#'
commit "con la tabla (2)"; BASE1=$(git rev-parse HEAD)
echo "===== S1: con la base que ya tiene la tabla, 3 líneas en vez de 2 (debe ser ROJO)"
doc 3; B_BASE_REF=$BASE1 a2
echo "===== S2 (vía b): la deuda llega a 0 y se BORRA la tabla vacía; luego, 5 líneas viejas NUEVAS con una tabla nueva"
doc 0; B_BASE_REF=$BASE1 A2_DEUDA_MODO=1 a2; grep -vc '^#' doc/control/a2-deuda.tsv
git rm -qf doc/control/a2-deuda.tsv; commit "deuda 0: fuera la tabla vacía"
echo "   -- el commit que borra la tabla, contra la base BASE1:"; B_BASE_REF=$BASE1 a2
BASE2=$(git rev-parse HEAD)
mkdir -p doc/control; doc 5; B_BASE_REF=$BASE2 A2_DEUDA_MODO=2 a2 > /dev/null; commit "5 cifras viejas nuevas"
echo "   -- el commit con 5 cifras viejas NUEVAS, contra la base BASE2 (master tras el borrado):"; B_BASE_REF=$BASE2 a2
echo "===== S3 (vía b): en el commit de CREACIÓN (base sin tabla), una entrada DUPLICADA con «+inf» que el sort deja delante"
git checkout -qf --detach "$(git rev-list --max-parents=0 HEAD)"; mkdir -p doc/control; doc 2
printf '%s\n' '# etiqueta	documento	cifra	líneas' 'jobs	X.md	99	2' 'jobs	X.md	99	+inf' > doc/control/a2-deuda.tsv
B_BASE_REF=$(git rev-parse HEAD) a2; commit "creación con duplicado"; BASE3=$(git rev-parse HEAD)
echo "   -- después, 40 líneas viejas (la tabla dice 40, a mano), contra la base BASE3:"
doc 40; printf '%s\n' '# etiqueta	documento	cifra	líneas' 'jobs	X.md	99	40' > doc/control/a2-deuda.tsv
B_BASE_REF=$BASE3 a2
echo "   -- lo mismo con «10» en vez de «+inf» (sort: «10» < «2»; el orden del fichero deja el 10 al final):"
git checkout -qf --detach "$(git rev-list --max-parents=0 HEAD)"; mkdir -p doc/control; doc 2
printf '%s\n' '# etiqueta	documento	cifra	líneas' 'jobs	X.md	99	2' 'jobs	X.md	99	10' > doc/control/a2-deuda.tsv
B_BASE_REF=$(git rev-parse HEAD) a2; commit "creación con duplicado 10"; BASE4=$(git rev-parse HEAD)
doc 10; printf '%s\n' '# etiqueta	documento	cifra	líneas' 'jobs	X.md	99	10' > doc/control/a2-deuda.tsv
B_BASE_REF=$BASE4 a2
echo "===== S4 (a): el CAMBIO dentro de una clave: se arregla una línea vieja y se añade OTRA nueva con la misma cifra"
git checkout -qf "$BASE1"; { for i in $(seq 1 100); do echo "cabecera $i"; done; echo "El build tiene 99 jobs (línea 1)."; echo "Afirmación NUEVA y falsa: hoy el build tiene 99 jobs."; } > X.md
B_BASE_REF=$BASE1 a2
echo "===== S5 (c): --quick (JOBS vacío) con deuda de jobs en la tabla"
git checkout -qf "$BASE1"; JOBS= B_BASE_REF=$BASE1 a2
echo "   -- y --a2-deuda con JOBS vacío BAJA la tabla, quitando la deuda de jobs:"
JOBS= B_BASE_REF=$BASE1 A2_DEUDA_MODO=1 a2; grep -v '^#' doc/control/a2-deuda.tsv | wc -l
git checkout -q -- doc/control/a2-deuda.tsv
