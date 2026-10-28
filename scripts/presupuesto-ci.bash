#!/bin/bash
# scripts/presupuesto-ci.bash — el TIEMPO y la MEMORIA del build y de leanchecker, contra un presupuesto (T41, ADR-202).
#
# Uso (en la CI, tras medir con GNU time): bash scripts/presupuesto-ci.bash <tiempo-build.txt> <tiempo-leanchecker.txt>
#
# Lee la salida de `/usr/bin/time -v` de cada uno (el tiempo de reloj y la memoria residente máxima), la escribe en el
# resumen del run y la compara con `doc/control/presupuesto-ci.tsv`: por encima de su presupuesto, rojo. Las cifras de
# tiempo y memoria sólo estaban en prosa, medidas en condiciones distintas (la auditoría, T41). El presupuesto sólo se
# sube con un ADR que diga por qué; se baja cuando las medidas lo permitan.

set -uo pipefail
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")/.." || exit 2

TABLA=doc/control/presupuesto-ci.tsv
RESUMEN="${GITHUB_STEP_SUMMARY:-/dev/stdout}"
FAIL=0

# los segundos de «Elapsed (wall clock) time (h:mm:ss or m:ss): 6:12.34»
segundos() {
  awk -F': ' '/Elapsed \(wall clock\)/ { v = $NF; n = split(v, p, ":"); s = 0
      for (i = 1; i <= n; i++) s = s * 60 + p[i]; printf "%d\n", s + 0.5 }' "$1"
}
# los MB de «Maximum resident set size (kbytes): 5242880»
megas() {
  awk -F': ' '/Maximum resident set size/ { printf "%d\n", $NF / 1024 + 0.5 }' "$1"
}

{
  echo "### Tiempo y memoria (T41)"
  echo ""
  echo "| medida | segundos | presupuesto | MB | presupuesto |"
  echo "|---|---:|---:|---:|---:|"
} >> "$RESUMEN"

i=0
for f in "$@"; do
  i=$((i + 1))
  case "$i" in 1) nombre=build ;; 2) nombre=leanchecker ;; *) nombre="medida$i" ;; esac
  if [ ! -s "$f" ]; then
    echo "❌ $nombre: no hay medida ($f): ¿corrió con /usr/bin/time?"
    FAIL=1; continue
  fi
  S=$(segundos "$f"); M=$(megas "$f")
  LIN=$(grep -v '^#' "$TABLA" | tr -d '\r' | awk -F'\t' -v n="$nombre" '$1 == n { print $2 "\t" $3 }')
  PS=${LIN%%	*}; PM=${LIN##*	}
  if [ -z "$S" ] || [ -z "$M" ] || [ -z "$LIN" ]; then
    echo "❌ $nombre: no pude leer la medida («$S» s, «$M» MB) o su presupuesto («$LIN») en $TABLA"
    FAIL=1; continue
  fi
  echo "| $nombre | $S | $PS | $M | $PM |" >> "$RESUMEN"
  if [ "$S" -gt "$PS" ] || [ "$M" -gt "$PM" ]; then
    echo "❌ $nombre: $S s y $M MB, por encima del presupuesto ($PS s, $PM MB)"
    FAIL=1
  else
    echo "✓ $nombre: $S s (presupuesto $PS) · $M MB (presupuesto $PM)"
  fi
done
[ "$i" -ge 2 ] || { echo "❌ hacen falta las dos medidas (build y leanchecker)"; FAIL=1; }
exit "$FAIL"
