#!/bin/bash
# a_techo_cero_t04b.bash [SALIDA] — el techo CERO de [A2] (ADR-169 §3), visto fallar en un juguete: en una copia de
# trabajo aparte (git worktree, sin tocar el árbol), un commit borra doc/control/a2-deuda.tsv y el siguiente la
# devuelve; con la base verificada en el commit que la borró (que sí la conoce: su check-doc-sync.bash la nombra), la
# tabla devuelta tiene que salir POR ENCIMA del techo. Corre check-doc-sync.bash --quick (sin build: [A2] no lo necesita;
# los bloques que piden la librería construida salen rojos allí, y no cuentan) e imprime el bloque [A2].
export PATH="/usr/bin:/bin:$PATH"
SAL=$(realpath -m "${1:-/dev/stdout}")
cd "$(dirname "$0")/../../.." || exit 2
WT=$(mktemp -d)/wt
trap 'git worktree remove --force "$WT" 2>/dev/null; rm -rf "$(dirname "$WT")"' EXIT INT TERM
git worktree add -q --detach "$WT" HEAD || exit 2
cp check-doc-sync.bash "$WT/check-doc-sync.bash"   # (el del árbol de trabajo, por si aún no está en el commit)
(
  cd "$WT" || exit 2
  git rm -q doc/control/a2-deuda.tsv
  git -c user.name=juguete -c user.email=juguete@localhost commit -q -m 'juguete: la tabla, borrada' -- doc/control/a2-deuda.tsv
  BORRA=$(git rev-parse HEAD)
  git checkout -q HEAD~1 -- doc/control/a2-deuda.tsv
  git -c user.name=juguete -c user.email=juguete@localhost commit -q -m 'juguete: la tabla, otra vez' -- doc/control/a2-deuda.tsv
  echo "# a_techo_cero_t04b.bash, $(date -u +%Y-%m-%dT%H:%MZ): base = el commit que borra la tabla ($(git rev-parse --short "$BORRA")), HEAD = el que la devuelve"
  echo
  B_BASE_REF="$BORRA" bash check-doc-sync.bash --quick 2>&1 | LC_ALL=C awk '/^════ \[A2\]/ { p = 1; print; next } /^════/ { p = 0 } p && NF' | cut -c1-200
) > "$SAL"
