#!/bin/bash
# harness.bash — corre VERBATIM los bloques [A], [A2] e [I] de la copia de check-doc-sync.bash (rpp-check.bash,
# copiada del árbol de RPP al empezar la revisión) dentro de un directorio de juguete.
# uso: bash harness.bash <dir> <A|A2|I>        variables: JOBS ACTIVE META QUAR AXIOMS SORRY SOND DOCS A2_DEUDA_MODO
#      B_BASE_REF  DECLS (fichero)  CIERRE (texto)  B_DECLS_OK
H=$(cd "$(dirname "$0")" && pwd); SCRIPT=${MUT:-$H/rpp-check.bash}
cd "$1" || exit 2; SEC=$2
set -uo pipefail
JOBS=${JOBS-133}; ACTIVE=${ACTIVE-116}; META=${META-112}; QUAR=${QUAR-0}; AXIOMS=${AXIOMS-0}; SORRY=${SORRY-0}; SOND=${SOND-43}
DOCS=${DOCS-$(cat docs.list 2>/dev/null)}; FAIL=0; A2_DEUDA_MODO=${A2_DEUDA_MODO-0}
CIERRE=${CIERRE-}; B_DECLS_OK=${B_DECLS_OK-1}; DECLS=${DECLS-/dev/null}
lineas() { sed -n "$(grep -n "$1" "$SCRIPT" | head -1 | cut -d: -f1),$(grep -n "$2" "$SCRIPT" | head -1 | cut -d: -f1)p" "$SCRIPT"; }
A_SRC=$(lineas '════ \[A\] CIFRAS' 'A_FAIL" = "0"')
A2_SRC=$(lineas '^echo "════ \[A2\]' 'A2_FAIL" = "0"')
I_SRC=$(lineas '^I_REGLAS=\$(mktemp)' 'I_FAIL" = "0"')
case "$SEC" in
  A)  eval "$A_SRC" ;;
  A2) eval "$A_SRC" > /dev/null; eval "$A2_SRC" ;;
  I)  eval "$I_SRC" ;;
esac
echo "FAIL=$FAIL"
