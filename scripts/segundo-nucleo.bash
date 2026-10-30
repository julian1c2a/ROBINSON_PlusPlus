#!/bin/bash
# scripts/segundo-nucleo.bash — el CIERRE de los titulares, comprobado por núcleos que NO son el de Lean (T23, ADR-222).
#
# Uso (desde la raíz de RPP, tras `lake build`): bash scripts/segundo-nucleo.bash [directorio de salida]
#
# `leanchecker` vuelve a pasar cada declaración por el núcleo, pero por el MISMO núcleo («This is not an external
# verifier», LeanChecker.lean). Desde v4.35 el toolchain trae otros, los que corre `lake check --paranoid`
# (Lake/CLI/Check.lean): `leanchecker-paranoid`, `lean4lean` (el núcleo reescrito en Lean), `nanoda` (en Rust),
# `con-leche` y `con-ron` (verificados: «a file that declares a theorem of type False is never accepted»). Todos leen
# una EXPORTACIÓN (NDJSON, de `leanexport`), no los `.olean`.
#
# Qué hace, para cada CONJUNTO de titulares (`titulares`: los 32 de `TITULARES`, `Meta/ContratoTitulares.lean`, que son
# los de `T_UNIVERSO`; `puros`: los 12 de la clase (i), `PUROS` de `Meta/PurezaTitulares.lean`, cuyo cierre no nombra
# la semántica ni el modelo):
#   1. Exporta su cierre: `leanexport` escribe cada constante con todas las suyas, tipos y VALORES (las pruebas
#      también), hasta los primitivos de Lean.
#   2. Lee la exportación sin núcleo (`scripts/exportacion.py`): los titulares tienen que estar, como teoremas, y sus
#      `axiom` tienen que ser EXACTAMENTE la unión de sus footprints en la tabla de `check-footprints.bash`: dos
#      recorridos distintos de las dependencias (el de `#print axioms` y el del exportador), la misma respuesta.
#   3. Pasa la exportación por cada núcleo (y por el de Lean desde cero, `leanchecker --from-export`) y clasifica lo
#      que dice: ACEPTA, RECHAZA (un error de tipos) o AGOTA (se queda sin recursos: pila, recursión, combustible o
#      tiempo, sin pronunciarse). El resultado tiene que ser el DECLARADO en `doc/control/segundo-nucleo.tsv`, en los
#      dos sentidos: un núcleo que deja de aceptar es rojo, y uno que empieza a aceptar también (para que la tabla
#      suba). RECHAZA sobre la exportación verdadera es siempre rojo.
#   4. El control NEGATIVO: un mutante de la exportación (el valor del primer teorema, cambiado por su tipo). Donde la
#      tabla dice ACEPTA, el núcleo tiene que RECHAZAR el mutante como error de tipos; si lo acepta, o se cae, no
#      comprueba nada, y es rojo.
# Sin la herramienta, sin la exportación o sin una tabla, rojo: un control que no mide no da verde.
#
# ⚠️ Fuera de la CI: en la máquina del propietario, Windows («Control de aplicaciones») bloquea `leanexport`,
# `lean4lean`, `con-leche` y `con-ron` (medido el 2026-10-30). No se rodea: corre en la CI (Linux).
# ⚠️ Se corren directamente, no por `lake check`: `lake check` aísla con `bwrap`, que en el runner de GitHub no
# arranca («loopback: Failed RTM_NEWADDR: Operation not permitted», y lo cuenta como «kernel rejected the solution»), y
# no ve el hermano `../FOL`. Los argumentos de cada núcleo son los de `bundledKernels` y `runExternalKernel` de
# Lake/CLI/Check.lean (v4.35.0), con la misma configuración de nanoda (más pila para sus hilos: SEGUNDO_NUCLEO_PILA).

set -uo pipefail
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")/.." || exit 2

OUT=${1:-$(mktemp -d)}
mkdir -p "$OUT" || exit 2
RESUMEN="${GITHUB_STEP_SUMMARY:-/dev/null}"
LIMITE=${SEGUNDO_NUCLEO_LIMITE:-1200}          # segundos por núcleo y fichero
PILA=${SEGUNDO_NUCLEO_PILA:-1073741824}       # bytes de pila por hilo de nanoda (RUST_MIN_STACK)
DECL=doc/control/segundo-nucleo.tsv
NUCLEOS="lean paranoid lean4lean nanoda con-leche con-ron"
FAIL=0

command -v lake >/dev/null || { echo "❌ NO PUEDO MEDIR: lake no está en el PATH"; exit 2; }
command -v python3 >/dev/null || { echo "❌ NO PUEDO MEDIR: python3 no está en el PATH"; exit 2; }
[ -s "$DECL" ] || { echo "❌ NO PUEDO MEDIR: falta $DECL"; exit 2; }
PREFIJO=$(lake env lean --print-prefix 2>/dev/null | tr -d '\r')
BIN="$PREFIJO/bin"
[ -x "$BIN/lean" ] || { echo "❌ NO PUEDO MEDIR: no encuentro el toolchain del proyecto («$PREFIJO»)"; exit 2; }
echo "toolchain: $PREFIJO"

# ── Los conjuntos ───────────────────────────────────────────────────────────────────────────────────────────────────
lista() {   # $1 = fichero, $2 = nombre de la lista → sus nombres, uno por línea
  awk -v d="def $2 : List Name := [" 'index($0, d) == 1 { f = 1; next }
       f && /^ *``/ { s = $0; sub(/^ *``/, "", s); sub(/[],].*$/, "", s); print s } f && /\]/ { exit }' "$1"
}
lista ROBINSON_PlusPlus/Meta/ContratoTitulares.lean TITULARES > "$OUT/titulares.txt"
lista ROBINSON_PlusPlus/Meta/PurezaTitulares.lean PUROS > "$OUT/puros.txt"
NT=$(wc -l < "$OUT/titulares.txt"); NP=$(wc -l < "$OUT/puros.txt")
NU=$(awk '/^T_UNIVERSO="/ { f = 1 } f { print } f && /"$/ { exit }' check-doc-sync.bash \
     | sed 's/^T_UNIVERSO="//; s/"$//' | tr ' ' '\n' | grep -c .)
if [ "$NT" -eq 0 ] || [ "$NT" != "$NU" ] || [ "$NP" -eq 0 ]; then
  echo "❌ NO PUEDO MEDIR: $NT titulares en TITULARES, $NU en T_UNIVERSO y $NP en PUROS"; exit 2
fi
if [ -n "$(LC_ALL=C comm -23 <(LC_ALL=C sort "$OUT/puros.txt") <(LC_ALL=C sort "$OUT/titulares.txt"))" ]; then
  echo "❌ NO PUEDO MEDIR: un nombre de PUROS no está en TITULARES"; exit 2
fi
echo "conjuntos: titulares ($NT = T_UNIVERSO) y puros ($NP, la clase (i))"

# los axiom esperados de un conjunto: la unión de los footprints de sus titulares (check-footprints.bash)
TABLA=$(awk '/^read -r -d .. TABLA <<.EOF.$/ { f = 1; next } f && /^EOF$/ { exit } f' check-footprints.bash)
esperados() {
  local t fila acc=""
  while read -r t; do
    fila=$(printf '%s\n' "$TABLA" | awk -F'|' -v n="$t" '$1 == n { print $2; exit }')
    [ -n "$fila" ] || { echo "@@SIN_FILA@@ $t"; return; }
    [ "$fila" = "-" ] || acc="$acc,$fila"
  done < "$1"
  printf '%s\n' "$acc" | tr ',' '\n' | grep . | LC_ALL=C sort -u | paste -sd, -
}

segundos() { awk -F': ' '/Elapsed \(wall clock\)/ { v = $NF; n = split(v, p, ":"); s = 0
  for (i = 1; i <= n; i++) s = s * 60 + p[i]; printf "%d\n", s + 0.5 }' "$1"; }
megas() { awk -F': ' '/Maximum resident set size/ { printf "%d\n", $NF / 1024 + 0.5 }' "$1"; }

# veredicto <núcleo> <rc> <log> → acepta | rechaza | agota | ?  (lo que dice cada uno, medido el 2026-10-30)
veredicto() {
  local k=$1 rc=$2 log=$3
  if [ "$rc" -eq 124 ]; then echo agota; return; fi
  if [ "$rc" -eq 0 ]; then echo acepta; return; fi
  case "$k" in
    lean|paranoid)
      if grep -q 'deep recursion\|maximum recursion\|stack overflow' "$log"; then echo agota
      elif grep -q 'rejects the solution' "$log"; then echo rechaza; else echo '?'; fi ;;
    lean4lean)
      if grep -q 'deep recursion\|stack overflow' "$log"; then echo agota
      elif grep -q 'type mismatch\|(kernel)' "$log"; then echo rechaza; else echo '?'; fi ;;
    nanoda)
      if grep -q 'overflowed its stack' "$log"; then echo agota
      elif [ "$rc" -ne 134 ] && grep -qi 'error\|mismatch\|fail' "$log"; then echo rechaza; else echo '?'; fi ;;
    con-leche|con-ron)
      # sus códigos (con-leche --help): 1, rechazado; 3, error interno (aquí, «fuel exhausted»)
      if [ "$rc" -eq 3 ] && grep -q 'fuel exhausted' "$log"; then echo agota
      elif [ "$rc" -eq 1 ]; then echo rechaza; else echo '?'; fi ;;
  esac
}

# corre <núcleo> <conjunto> <fichero de exportación> <etiqueta>: deja el código de salida en $RC
corre() {
  local k=$1 c=$2 f=$3 e=$4 arg
  local log="$OUT/$c-$k-$e.log" t="$OUT/$c-$k-$e.tiempo"
  case "$k" in
    lean)      /usr/bin/time -v -o "$t" timeout "$LIMITE" "$BIN/leanchecker" --from-export "$f" > "$log" 2>&1 ;;
    paranoid)  /usr/bin/time -v -o "$t" timeout "$LIMITE" "$BIN/leanchecker-paranoid" --from-export "$f" > "$log" 2>&1 ;;
    lean4lean) /usr/bin/time -v -o "$t" timeout "$LIMITE" "$BIN/lean4lean" --import "$f" > "$log" 2>&1 ;;
    nanoda)
      arg="$OUT/$c-nanoda-$e.json"
      python3 -c 'import json, sys; print(json.dumps({"use_stdin": False, "export_file_path": sys.argv[1],
        "permitted_axioms": [a for a in sys.argv[2].split(",") if a], "unpermitted_axiom_hard_error": True,
        "num_threads": 4, "nat_extension": True, "string_extension": True}))' "$f" "$ESP" > "$arg"
      RUST_MIN_STACK="$PILA" /usr/bin/time -v -o "$t" timeout "$LIMITE" "$BIN/nanoda_bin" "$arg" > "$log" 2>&1 ;;
    con-leche) /usr/bin/time -v -o "$t" timeout "$LIMITE" "$BIN/con-leche" "$f" > "$log" 2>&1 ;;
    con-ron)   /usr/bin/time -v -o "$t" timeout "$LIMITE" "$BIN/con-ron" "$f" > "$log" 2>&1 ;;
  esac
  RC=$?
}

{
  echo "### Segundo núcleo (T23)"
  echo ""
  echo "| conjunto | núcleo | exportación | declarado | s | MB | mutante |"
  echo "|---|---|---|---|---:|---:|---|"
} >> "$RESUMEN"
: > "$OUT/medido.tsv"

for c in titulares puros; do
  TIT="$OUT/$c.txt"; N=$(wc -l < "$TIT")
  ESP=$(esperados "$TIT")
  case "$ESP" in @@SIN_FILA@@*) echo "❌ NO PUEDO MEDIR: ${ESP#@@SIN_FILA@@ } no tiene fila en check-footprints.bash"; exit 2 ;; esac
  EXP="$OUT/$c.ndjson"; MUT="$OUT/$c-mutante.ndjson"
  echo
  echo "════ $c: el cierre de los $N ════"
  # shellcheck disable=SC2046
  if ! /usr/bin/time -v -o "$OUT/$c-leanexport.tiempo" lake env "$BIN/leanexport" ROBINSON_PlusPlus.Meta.ContratoTitulares -- \
       $(cat "$TIT") > "$EXP" 2> "$OUT/$c-leanexport.err" || [ ! -s "$EXP" ]; then
    echo "❌ NO PUEDO MEDIR: leanexport falló"; tail -20 "$OUT/$c-leanexport.err"; exit 2
  fi
  echo "  leanexport: $(du -h "$EXP" | cut -f1), $(segundos "$OUT/$c-leanexport.tiempo") s"
  python3 scripts/exportacion.py resumen "$EXP" "$TIT" "$ESP"; r=$?
  [ "$r" -eq 2 ] && exit 2
  [ "$r" -eq 0 ] || FAIL=1
  python3 scripts/exportacion.py mutante "$EXP" "$MUT" || exit 2
  for k in $NUCLEOS; do
    DEC=$(grep -v '^#' "$DECL" | tr -d '\r' | awk -F'\t' -v k="$k" -v c="$c" '$1 == k && $2 == c { print $3 }')
    case "$k" in lean) x=leanchecker ;; paranoid) x=leanchecker-paranoid ;; nanoda) x=nanoda_bin ;; *) x=$k ;; esac
    if [ ! -x "$BIN/$x" ]; then
      echo "  ❌ $k: no está en el toolchain ($BIN/$x)"; FAIL=1
      echo "| $c | $k | ❌ no está | $DEC | | | |" >> "$RESUMEN"; continue
    fi
    corre "$k" "$c" "$EXP" exportacion; V1=$(veredicto "$k" "$RC" "$OUT/$c-$k-exportacion.log"); R1=$RC
    corre "$k" "$c" "$MUT" mutante;     V2=$(veredicto "$k" "$RC" "$OUT/$c-$k-mutante.log"); R2=$RC
    S=$(segundos "$OUT/$c-$k-exportacion.tiempo"); M=$(megas "$OUT/$c-$k-exportacion.tiempo")
    printf '%s\t%s\t%s\t%s\n' "$k" "$c" "$V1" "$V2" >> "$OUT/medido.tsv"
    MAL=""
    [ -n "$DEC" ] || MAL="sin fila en $DECL"
    [ "$V1" = rechaza ] && MAL="${MAL:+$MAL; }RECHAZA la exportación verdadera"
    [ "$V1" = '?' ] && MAL="${MAL:+$MAL; }una salida que no sé leer (exit $R1)"
    [ -n "$DEC" ] && [ "$V1" != "$DEC" ] && MAL="${MAL:+$MAL; }declarado «$DEC»"
    [ "$DEC" = acepta ] && [ "$V2" != rechaza ] && MAL="${MAL:+$MAL; }el mutante: «$V2» (exit $R2), no un rechazo"
    if [ -z "$MAL" ]; then echo "  ✓ $k: $V1 ($S s, $M MB) · mutante: $V2"
    else
      echo "  ❌ $k: $V1 ($S s, $M MB) · mutante: $V2 — $MAL"; FAIL=1
      echo "     ── exportación (lo último):"; tail -4 "$OUT/$c-$k-exportacion.log" | cut -c1-240 | sed 's/^/        /'
      echo "     ── mutante (lo último):"; tail -3 "$OUT/$c-$k-mutante.log" | cut -c1-240 | sed 's/^/        /'
    fi
    echo "| $c | $k | $V1 | $DEC | $S | $M | $V2 |" >> "$RESUMEN"
  done
done

echo
if [ "$FAIL" -eq 0 ]; then
  echo "✓ SEGUNDO NÚCLEO: lo medido es lo declarado en $DECL, y donde un núcleo acepta, rechaza el mutante"
else
  echo "❌ SEGUNDO NÚCLEO: ver arriba (lo medido, en $OUT/medido.tsv)"
fi
exit "$FAIL"
