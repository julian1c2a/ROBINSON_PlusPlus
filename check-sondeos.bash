#!/bin/bash
# check-sondeos.bash — compila los sondeos con `lake lean`, cada uno con tiempo límite, y escribe una tabla TSV.
#
# Nace de T06 de doc/AUDITORIA-SUELO-2026-10-12.md (ADR-141). Lo que había era `scripts/sondeos_todos.ps1`, que
# compilaba con `lake env lean`, y esa orden NO pasa los `leanOptions` del lakefile: los sondeos se medían con
# `autoImplicit` ENCENDIDO, otra configuración que la del build (ADR-128). `lake lean` sí los pasa. Y la CI no
# compilaba ningún sondeo: los controles negativos (los que refutan algo) no los vigilaba nadie.
#
# Uso (en Windows, desde PowerShell: `lake` no está en el PATH de Git Bash):
#   bash check-sondeos.bash               todos los sondeos/*.lean → sondeos/pasadas/tabla-<fecha>.tsv (INFORME: sale 0)
#   bash check-sondeos.bash --controles   sólo los de sondeos/CONTROLES.txt; ROJO (sale 1) si alguno no compila
#   bash check-sondeos.bash F.lean ...    sólo esos (informe)
#   opciones: -j N  en paralelo (por defecto 2: cada proceso carga el entorno entero; más agota la memoria)
#             -t S  tiempo límite por sondeo, en segundos (por defecto 600)
#             --env compila con `lake env lean` en vez de `lake lean` (para comparar; T06)
#
# ⚠️ Un sondeo que no se pudo medir (fichero ausente, lista vacía) es ROJO con --controles: no medir no es «0 fallos».
# ⚠️ Un sondeo que compila con un `sorry` sale como SORRY, no como 0: un aviso no es una prueba.
# ⚠️ `timeout` en Git Bash mata `lake`, pero puede dejar vivo el `lean` hijo: el límite es generoso a propósito.
# ⚠️ Algunos sondeos ESCRIBEN (ConoTitulares, en doc/registro/2026-10-16-cono/): con el mismo build, lo mismo.

set -uo pipefail
cd "$(dirname "$0")"
[ -d /usr/bin ] && export PATH="/usr/bin:/bin:$PATH"

J=2; T=600; MODO=todos; CMD="lean"; LISTA=()
while [ $# -gt 0 ]; do
  case "$1" in
    -j) J=$2; shift ;;
    -t) T=$2; shift ;;
    --controles) MODO=controles ;;
    --env) CMD="env lean" ;;
    -h|--help) awk 'NR > 1 && /^#/ { print; next } NR > 1 { exit }' "$0"; exit 0 ;;
    *.lean) LISTA+=("$(basename "$1")") ;;
    *) echo "opción desconocida: $1" >&2; exit 2 ;;
  esac
  shift
done

command -v lake >/dev/null 2>&1 || { echo "❌ NO PUDE MEDIR: 'lake' no está en el PATH (¿Git Bash? lánzalo desde PowerShell)"; exit 1; }

if [ "$MODO" = controles ]; then
  [ -f sondeos/CONTROLES.txt ] || { echo "❌ NO PUDE MEDIR: falta sondeos/CONTROLES.txt"; exit 1; }
  mapfile -t LISTA < <(sed -e 's/#.*//' -e 's/[[:space:]]//g' sondeos/CONTROLES.txt | grep -v '^$')
  [ ${#LISTA[@]} -gt 0 ] || { echo "❌ NO PUDE MEDIR: sondeos/CONTROLES.txt no nombra ningún sondeo"; exit 1; }
elif [ ${#LISTA[@]} -eq 0 ]; then
  mapfile -t LISTA < <(ls sondeos/*.lean | xargs -n1 basename | sort)
fi

OUT=sondeos/pasadas/salida            # fuera de git (.gitignore)
mkdir -p "$OUT"
FALTAN=0
uno() {   # $1 = fichero; escribe «nombre<TAB>rc<TAB>segundos<TAB>primer error» en $OUT/<base>.fila
  local f=$1 b=${1%.lean} t0 t1 rc e1
  if [ ! -f "sondeos/$f" ]; then printf '%s\tAUSENTE\t0\t\n' "$f" > "$OUT/$b.fila"; return; fi
  t0=$(date +%s)
  timeout "$T" lake $CMD "sondeos/$f" > "$OUT/$b.out" 2>&1; rc=$?
  t1=$(date +%s)
  [ "$rc" = 124 ] && rc=TIMEOUT
  # un `sorry` es un aviso, no un error: compila con rc 0 y no prueba nada. Aquí cuenta como fallo.
  [ "$rc" = 0 ] && grep -qE 'declaration uses .sorry.' "$OUT/$b.out" && rc=SORRY
  e1=$(grep -m1 -E 'error' "$OUT/$b.out" | sed -E 's#^.*sondeos[\\/]##' | tr '\t' ' ' | cut -c1-200)
  printf '%s\t%s\t%s\t%s\n' "$f" "$rc" "$((t1 - t0))" "$e1" > "$OUT/$b.fila"
}

for f in "${LISTA[@]}"; do
  while [ "$(jobs -rp | wc -l)" -ge "$J" ]; do wait -n; done
  uno "$f" &
done
wait

TSV=$(mktemp)
printf 'sondeo\trc\tsegundos\tprimer_error\n' > "$TSV"
for f in "${LISTA[@]}"; do cat "$OUT/${f%.lean}.fila"; done | sort >> "$TSV"
N=$(( $(wc -l < "$TSV") - 1 ))
OK=$(awk -F'\t' 'NR > 1 && $2 == "0"' "$TSV" | wc -l)
TO=$(awk -F'\t' 'NR > 1 && $2 == "TIMEOUT"' "$TSV" | wc -l)
AU=$(awk -F'\t' 'NR > 1 && $2 == "AUSENTE"' "$TSV" | wc -l)

if [ "$MODO" = controles ]; then
  echo "════ SONDEOS DE CONTROL (sondeos/CONTROLES.txt, con \`lake $CMD\`) ════"
  awk -F'\t' 'NR > 1 { printf "  %s %s (%s s)%s\n", ($2 == "0" ? "✓" : "❌"), $1, $3, ($2 == "0" ? "" : "  rc=" $2 "  " $4) }' "$TSV"
  rm -f "$TSV"
  # ⭐ 2026-11-04 (R3-5-06 de la ronda 3, ADR-255): el control NEGATIVO que enunciaba ADR-128 y nunca se cableó. Un
  # fichero con una variable implícita automática tiene que FALLAR con `lake lean` (los leanOptions del lakefile:
  # `autoImplicit` apagado) y COMPILAR con `lake env lean` (sin ellos: así el fallo es por la opción, no por otra cosa).
  # Si `autoImplicit` vuelve a encenderse en el lakefile, o `lake lean` deja de pasar las opciones, rojo.
  NEG=0
  NEGD=$(mktemp -d)
  printf '%s\n' '-- (lo genera check-sondeos.bash: tiene que fallar con autoImplicit apagado)' \
    'theorem autoImplicitApagado (h : n = n) : True := trivial' > "$NEGD/AutoImplicitDebeFallar.lean"
  NEGF=$(cygpath -m "$NEGD/AutoImplicitDebeFallar.lean" 2>/dev/null || printf '%s' "$NEGD/AutoImplicitDebeFallar.lean")
  if lake lean "$NEGF" > "$NEGD/con.out" 2>&1; then
    echo "  ❌ autoImplicit: un fichero con una variable implícita automática COMPILA con \`lake lean\`"; NEG=1
  elif ! grep -qiE 'unknown identifier .n.' "$NEGD/con.out"; then
    echo "  ❌ autoImplicit: \`lake lean\` falla, pero no por la variable: $(grep -m1 error "$NEGD/con.out" | cut -c1-120)"; NEG=1
  elif ! lake env lean "$NEGF" > "$NEGD/sin.out" 2>&1; then
    echo "  ❌ autoImplicit: el fichero no compila tampoco sin las opciones (no prueba lo que dice)"; NEG=1
  else
    echo "  ✓ autoImplicit apagado: la variable implícita automática falla con \`lake lean\` y compila sin sus opciones"
  fi
  rm -rf "$NEGD"
  if [ "$OK" = "$N" ] && [ "$N" -gt 0 ] && [ "$NEG" = 0 ]; then echo "✅ los $N sondeos de control compilan, y el negativo falla"; exit 0; fi
  echo "❌ $((N - OK)) de $N sondeos de control NO compilan (o no se pudieron medir), o el negativo no falla"; exit 1
fi

DEST=sondeos/pasadas/tabla-$(date +%F)$([ "$CMD" = "env lean" ] && echo -env).tsv
[ ${#LISTA[@]} -lt "$(ls sondeos/*.lean | wc -l)" ] && DEST=$OUT/_tabla-parcial.tsv
mv "$TSV" "$DEST"
echo "sondeos: $N · compilan $OK · no $((N - OK - TO - AU)) · TIMEOUT $TO · ausentes $AU  →  $DEST"
exit 0
