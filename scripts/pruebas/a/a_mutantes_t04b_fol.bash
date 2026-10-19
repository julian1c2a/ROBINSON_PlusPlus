#!/bin/bash
# a_mutantes_t04b_fol.bash [SALIDA] — los mutantes de T04b (ADR-169) en FOL (../FOL): cada uno inserta UNA línea en un
# documento, corre el check-doc-sync.bash de FOL entero y la deshace (también si se interrumpe). Imprime, por mutante,
# el código de salida y las líneas de [A] y [A2]. Lo esperado: rojo en todos menos en el de control («Histórico:»).
export PATH="/usr/bin:/bin:$PATH"
SAL=$(realpath -m "${1:-/dev/stdout}")   # (antes del cd: una ruta relativa es la de quien llama)
cd "$(dirname "$0")/../../../../FOL" || exit 2
TMP=$(mktemp -d)
FICH="CURRENT-STATUS-PROJECT.md NEXT-STEPS.md"
for f in $FICH; do cp "$f" "$TMP/$f"; done
restaura() { for f in $FICH; do cp "$TMP/$f" "$f"; done; }
trap 'restaura; rm -rf "$TMP"' EXIT INT TERM
mutante() {   # $1 nombre  $2 fichero  $3 línea tras la que insertar  $4 texto
  awk -v l="$3" -v t="$4" '{ print } NR == l { print t }' "$2" > "$TMP/x" && cat "$TMP/x" > "$2"
  bash check-doc-sync.bash > "$TMP/out" 2>&1; local rc=$?
  restaura
  { echo "== $1 (salida $rc): $4"
    LC_ALL=C awk '/^════ \[(A|A2)\]/ { p = 1; print; next } /^════/ { p = 0 } p && NF' "$TMP/out" | cut -c1-200
    echo; } >> "$SAL"
}
: > "$SAL" 2>/dev/null || true
echo "# a_mutantes_t04b_fol.bash, $(date -u +%Y-%m-%dT%H:%MZ), FOL HEAD $(git rev-parse --short HEAD) (más el árbol de trabajo)" >> "$SAL"
echo >> "$SAL"
mutante cabecera-fecha-negrita CURRENT-STATUS-PROJECT.md 5 'Estado 2026-10-19: **3** sorry en el build.'
mutante cabecera-palabra-dentro CURRENT-STATUS-PROJECT.md 5 'Fuera de las listas: **2** `axiom` de Lean.'
mutante cabecera-axiom-en-el-build CURRENT-STATUS-PROJECT.md 5 'Hay **4 `axiom`** en el build.'
mutante cabecera-cita-con-digito CURRENT-STATUS-PROJECT.md 5 'Hay 5 sorry (ver «ADR-121»).'
mutante cuerpo-fecha NEXT-STEPS.md 150 'Estado 2026-10-19: 7 sorry en el build.'
mutante cuerpo-control-historico NEXT-STEPS.md 150 'Histórico: 7 sorry en el build.'
