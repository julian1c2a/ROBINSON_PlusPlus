#!/bin/bash
# scripts/presupuesto-ci.bash — el TIEMPO y la MEMORIA del build y de leanchecker, contra un presupuesto (T41, ADR-202).
#
# Uso (en la CI, tras medir con GNU time): bash scripts/presupuesto-ci.bash <tiempo-build.txt> <tiempo-leanchecker.txt>
#
# Lee la salida de `/usr/bin/time -v` de cada uno (el tiempo de reloj y la memoria residente máxima), la escribe en el
# resumen del run y la compara con `doc/control/presupuesto-ci.tsv`: por encima de su presupuesto, rojo. Las cifras de
# tiempo y memoria sólo estaban en prosa, medidas en condiciones distintas (la auditoría, T41). El presupuesto sólo se
# sube con un ADR que diga por qué; se baja cuando las medidas lo permitan.
# ⚠️ ✏️ 2026-11-04 (R3-3-04 de la ronda 3, ADR-256): los MB NO son la memoria del build. «Maximum resident set size» de
# GNU time es el PICO del proceso más pesado del árbol (un `lean` de un módulo, o leanchecker), no la suma de los que
# corren a la vez: así se rotula ahora, en el resumen y en la tabla.
#   bash scripts/presupuesto-ci.bash --autotest   # ✏️ (R3-5-14, ADR-256): con medidas sintéticas; en la CI

set -uo pipefail
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")/.." || exit 2

TABLA=doc/control/presupuesto-ci.tsv
RESUMEN="${GITHUB_STEP_SUMMARY:-/dev/stdout}"
FAIL=0

# ⭐ el AUTOTEST: dentro del presupuesto, verde; por encima en tiempo, en memoria, sin medida o con una ilegible, rojo.
# «Probado con el fallo puesto» (ADR-202) no tenía artefacto.
if [ "${1:-}" = "--autotest" ]; then
  T=$(mktemp -d)
  trap 'rm -rf "$T"' EXIT
  medida() { printf '\tElapsed (wall clock) time (h:mm:ss or m:ss): %s\n\tMaximum resident set size (kbytes): %s\n' "$1" "$2" > "$3"; }
  medida 1:00.00 1048576 "$T/bien"; medida 59:00.00 1048576 "$T/lento"; medida 1:00.00 104857600 "$T/gordo"
  printf 'nada\n' > "$T/ilegible"
  AF=0
  uno() {  # $1 = esperado (0/1), resto = medidas
    local esp=$1; shift
    GITHUB_STEP_SUMMARY=/dev/null bash "$0" "$@" > "$T/sal" 2>&1; local rc=$?
    if [ "$rc" != "$esp" ]; then echo "  ✗ autotest: con $(basename -a "$@" | tr '\n' ' ')salió $rc, y debía $esp"; cat "$T/sal"; AF=1; fi
  }
  uno 0 "$T/bien" "$T/bien"
  uno 1 "$T/lento" "$T/bien"
  uno 1 "$T/bien" "$T/gordo"
  uno 1 "$T/bien" "$T/ilegible"
  uno 1 "$T/bien" "$T/no-existe"
  uno 1 "$T/bien"
  if [ "$AF" = 0 ]; then echo "✅ autotest de presupuesto-ci.bash: dentro, verde; lento, gordo, ilegible, ausente o solo, rojo."; exit 0; fi
  echo "❌ autotest de presupuesto-ci.bash."; exit 1
fi

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
  echo "| medida | segundos | presupuesto | MB (pico del proceso más pesado) | presupuesto |"
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
  # ✏️ 2026-10-28 (R3-3-03 de la ronda 3, ADR-212): también una celda vacía o no numérica (antes, `[ 5 -gt "" ]` daba
  # error, no «mayor», y el control escribía ✓).
  if [ -z "$S" ] || [ -z "$M" ] || [ -z "$LIN" ] || ! [[ "$S$M" =~ ^[0-9]+$ ]] || ! [[ "$PS" =~ ^[0-9]+$ ]] || ! [[ "$PM" =~ ^[0-9]+$ ]]; then
    echo "❌ $nombre: no pude leer la medida («$S» s, «$M» MB) o su presupuesto («$PS» s, «$PM» MB) en $TABLA"
    FAIL=1; continue
  fi
  echo "| $nombre | $S | $PS | $M | $PM |" >> "$RESUMEN"
  if [ "$S" -gt "$PS" ] || [ "$M" -gt "$PM" ]; then
    echo "❌ $nombre: $S s y $M MB, por encima del presupuesto ($PS s, $PM MB)"
    FAIL=1
  else
    echo "✓ $nombre: $S s (presupuesto $PS) · $M MB de pico del proceso más pesado (presupuesto $PM)"
  fi
done
[ "$i" -ge 2 ] || { echo "❌ hacen falta las dos medidas (build y leanchecker)"; FAIL=1; }
exit "$FAIL"
