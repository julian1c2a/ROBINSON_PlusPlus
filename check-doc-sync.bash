#!/bin/bash
# check-doc-sync.bash — detecta documentación DESINCRONIZADA del código real.
#
# Nace de dos fallos reales, ambos caros (ver AI-GUIDE.md §27 y la memoria
# `feedback-doc-audit-traps`):
#
#   1. Los documentos de estado se actualizan por su BANNER y no por su CUERPO.
#      `CURRENT-STATUS-PROJECT.md` llegó a tener un banner correcto y, tres líneas
#      más abajo, una tabla que decía «113 jobs, 99 módulos». Un ADR llevó un mes
#      diciendo «no implementado» sobre algo hecho.
#   2. Se citan como vigentes símbolos que YA NO EXISTEN en el código
#      (`goedel_first_real'`, `prf_tc_cons'`, …).
#
# [A], [C] y [D] son OBJETIVOS y rompen el check. [B] es un AVISO que pide juicio:
# hay menciones legítimas de símbolos inexistentes (históricas, planificadas, descartadas).
#
# Uso:
#   bash check-doc-sync.bash            # comprobación completa
#   bash check-doc-sync.bash --quick    # sin `lake build` (usa el conteo de módulos)
#   bash check-doc-sync.bash --fix-hint # además, sugiere el sed de cada corrección
#
# Salida: 0 si todo cuadra, 1 si hay desincronización.

set -uo pipefail
cd "$(dirname "$0")"

QUICK=0
HINT=0
for a in "$@"; do
  case "$a" in
    --quick)     QUICK=1 ;;
    --fix-hint)  HINT=1 ;;
    -h|--help)   sed -n '2,20p' "$0"; exit 0 ;;
    *) echo "opción desconocida: $a" >&2; exit 2 ;;
  esac
done

# ─── 1. VERDAD DEL CÓDIGO ────────────────────────────────────────────────────
MIN=$(ls ROBINSON_PlusPlus/Minimal/*.lean ROBINSON_PlusPlus/Minimal/**/*.lean 2>/dev/null | sort -u | wc -l)
META=$(ls ROBINSON_PlusPlus/Meta/*.lean 2>/dev/null | wc -l)
FULL=$(ls ROBINSON_PlusPlus/Full/*.lean 2>/dev/null | wc -l)
ACTIVE=$((MIN + META + FULL))
QUAR=$(ls cuarentena/*.lean 2>/dev/null | wc -l)
SOND=$(ls sondeos/*.lean 2>/dev/null | wc -l)
AXIOMS=$(grep -rhc "^axiom " ROBINSON_PlusPlus/ --include=*.lean 2>/dev/null | paste -sd+ | bc)

if [ "$QUICK" = "1" ]; then
  JOBS=""
else
  JOBS=$(lake build 2>&1 | grep -oE "Build completed successfully \([0-9]+ jobs\)" | grep -oE "[0-9]+" || true)
fi

echo "════ VERDAD DEL CÓDIGO ════"
printf "  módulos activos : %s  (Minimal %s + Meta %s + Full %s)\n" "$ACTIVE" "$MIN" "$META" "$FULL"
printf "  cuarentena      : %s\n" "$QUAR"
printf "  sondeos         : %s\n" "$SOND"
printf "  axiom de Lean   : %s\n" "$AXIOMS"
[ -n "$JOBS" ] && printf "  build jobs      : %s\n" "$JOBS"
echo

# Documentos AUTORITATIVOS: los que describen el ESTADO ACTUAL y por tanto deben cuadrar.
# Quedan fuera, y con razón, los de diario, diseño e historia (CHANGELOG, GODEL-*-DESIGN,
# PLAN-*, THOUGHTS, MINIMAL-AXIOMS…): sus cifras y símbolos son históricos POR DISEÑO.
AUTHORITATIVE="REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md AXIOMS.md GODEL-STATUS.md NEXT-STEPS.md"
AUTHORITATIVE="$AUTHORITATIVE $(ls doc/REFERENCE-*.md 2>/dev/null) cuarentena/README.md sondeos/README.md"
DOCS="$AUTHORITATIVE"
FAIL=0

# ─── 2. CIFRAS OBSOLETAS ─────────────────────────────────────────────────────
# CHANGELOG.md se excluye: es un diario, sus cifras son históricas por diseño.
# Las líneas marcadas como históricas también (fecha ISO al principio, o marcador).
echo "════ [A] CIFRAS ════"
A_FAIL=0
# ALCANCE: sólo la REGIÓN DE CABECERA (primeras 100 líneas) de cada doc autoritativo.
# Ahí viven el banner y las tablas resumen — lo que AFIRMA el estado actual. Más abajo
# están los registros de logros, donde «93 jobs» es historia correcta, no un error.
# Esta acotación es la que hace utilizable el control: sin ella, los diarios de
# `NEXT-STEPS.md` disparan una docena de falsos positivos y nadie vuelve a mirarlo.
HEADREGION=$(mktemp)
: > "$HEADREGION"
for d in $DOCS; do
  [ -e "$d" ] || continue
  head -100 "$d" | sed "s|^|$d:|" >> "$HEADREGION"
done

check_num () {   # $1 = regex con grupo numérico   $2 = valor correcto   $3 = etiqueta
  local pat="$1" good="$2" label="$3" hits
  hits=$(grep -nE "$pat" "$HEADREGION" 2>/dev/null          | grep -viE "hist[oó]rico|previo|antes|era |fueron|→|->|en su momento|entonces|ya no|20[0-9]{2}-[0-9]{2}-[0-9]{2}" || true)
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    local n; n=$(echo "$line" | grep -oE "$pat" | grep -oE "[0-9]+" | head -1)
    if [ -n "$n" ] && [ "$n" != "$good" ]; then
      echo "  ✗ $label: dice $n, real $good"
      echo "      ${line:0:150}"
      A_FAIL=1
    fi
  done <<< "$hits"
}
[ -n "$JOBS" ] && check_num "[0-9]+ jobs" "$JOBS" "jobs"
check_num "[0-9]+ módulos activos" "$ACTIVE" "módulos activos"
check_num "Meta ([0-9]+ \+|[0-9]+\))" "$META" "conteo de Meta"
check_num "[0-9]+ (módulos )?en \`cuarentena/\`" "$QUAR" "cuarentena"
rm -f "$HEADREGION"
[ "$A_FAIL" = "0" ] && echo "  ✓ sin cifras obsoletas" || FAIL=1

# ─── 3. SÍMBOLOS MUERTOS ─────────────────────────────────────────────────────
# Un símbolo está MUERTO si se cita en un doc AUTORITATIVO pero ninguna declaración
# del árbol activo empieza por él.
#
# Dos calibraciones aprendidas al estrenar este control (2026-08-23):
#   * Sólo se miran los docs AUTORITATIVOS (los que describen el estado actual). Los
#     de diseño e historia — MINIMAL-AXIOMS, THOUGHTS, GODEL-*-DESIGN, PLAN-* — citan
#     por diseño cosas que ya no están, y marcarlos sería ruido.
#   * Se compara por PREFIJO, no por igualdad: la prosa abrevia (`ax_C3` por
#     `ax_C3_concat_assoc`, `ax_lineWF` por `ax_lineWF_c1`), y eso es legítimo.
#     Un símbolo de verdad muerto (`goedel_first_real'`, `prf_tc_cons'`) no prefija nada.
echo
echo "════ [B] SÍMBOLOS MUERTOS — AVISO, requiere juicio ════"
echo "   (no rompe el check: hay menciones legítimas en secciones de diseño e historia.)"
B_FAIL=0
AUTHORITATIVE="REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md AXIOMS.md GODEL-STATUS.md NEXT-STEPS.md"
AUTHORITATIVE="$AUTHORITATIVE $(ls doc/REFERENCE-*.md 2>/dev/null) cuarentena/README.md sondeos/README.md"
# Marcadores que hacen LEGÍTIMA la mención de un símbolo inexistente:
#   (a) se declara retirado;  (b) es hipotético/propuesto/descartado;  (c) va en una
#   entrada fechada (histórico por diseño).
DEAD_MARKER='YA NO EXISTE|NO EXISTEN|retirad|RETIRADO|eliminad|borrad|legacy|F7a|histórico|ANTERIORES|🗑️|muert|Aquí vivía|tampoco existe|inexistente|desapareci|ya no son|se borró'
DEAD_MARKER="$DEAD_MARKER"'|propuest|candidat|hipot[eé]tic|har[ií]a falta|si se |habr[ií]a que|añadir |descartad|no existe|NO EXISTE|sin materializar|20[0-9]{2}-[0-9]{2}-[0-9]{2}'
#   (d) es un OBJETIVO declarado, no una afirmación de que ya está.
DEAD_MARKER="$DEAD_MARKER"'|falta|FALTA|construir|objetivo|medir|sin medir|pendiente|⏳|abiert|necesita|exige|pide|TAREA|hace falta|no hay ni habrá|sub‑familia|sub-familia|buscaba|buscó|usan la'
DECLS=$(mktemp)
# El árbol de declaraciones incluye `cuarentena/`: esos símbolos EXISTEN (están fuera
# del build, no borrados), y los docs los discuten con razón.
grep -rhoE "(theorem|def|abbrev|axiom|noncomputable def) +[A-Za-z_][A-Za-z0-9_']*"      ROBINSON_PlusPlus/ cuarentena/ ../FOL/ --include=*.lean 2>/dev/null      | awk '{print $NF}' | sort -u > "$DECLS"
CANDS=$(grep -rhoE '`(prf_|pcc_|goedel_|godel|d[123]_|repr_|ax_)[A-Za-z0-9_'"'"']+`' $AUTHORITATIVE 2>/dev/null         | tr -d '`' | sort -u)
for sym in $CANDS; do
  # los axiomas objeto son snake_case: `ax_UpperCamel` es un PLACEHOLDER de convención
  # de nombres (`ax_TagDescriptor`), no un símbolo. Se ignora.
  case "$sym" in ax_[A-Z]*) continue ;; esac
  # vivo si ALGUNA declaración empieza por el símbolo (la prosa abrevia)
  grep -qE "^${sym}" "$DECLS" && continue
  bad=$(grep -rn "\`${sym}\`" $AUTHORITATIVE 2>/dev/null | grep -vE "$DEAD_MARKER" || true)
  if [ -n "$bad" ]; then
    echo "  ✗ \`$sym\` no existe en el árbol activo, y se cita sin marcar como retirado:"
    echo "$bad" | head -2 | sed 's/^/      /' | cut -c1-140
    B_FAIL=1
  fi
done
rm -f "$DECLS"
# [B] NO marca FAIL: es un aviso. [A], [C] y [D] sí son objetivos y sí lo marcan.
# Razón: un control que grita lobo se acaba ignorando, y ése era justo el fallo que
# este script existe para evitar.
[ "$B_FAIL" = "0" ] && echo "  ✓ ningún símbolo muerto citado como vigente"                     || echo "  ⚠️  revisar los de arriba: ¿es una afirmación de que YA ESTÁ, o una mención histórica/planificada?"

# ─── 4. PROYECCIÓN: ¿está cada módulo en el catálogo? ────────────────────────
echo
echo "════ [C] PROYECCIÓN (AI-GUIDE §1/§14) ════"
C_FAIL=0
for f in ROBINSON_PlusPlus/Meta/*.lean ROBINSON_PlusPlus/Minimal/*.lean \
         ROBINSON_PlusPlus/Minimal/**/*.lean ROBINSON_PlusPlus/Full/*.lean; do
  [ -e "$f" ] || continue
  m=$(basename "$f" .lean)
  if ! grep -q "$m" REFERENCE.md 2>/dev/null; then
    echo "  ✗ $m NO aparece en el catálogo REFERENCE.md §1"
    C_FAIL=1
  fi
done
for f in cuarentena/*.lean; do
  [ -e "$f" ] || continue
  m=$(basename "$f" .lean)
  grep -q "$m" cuarentena/README.md 2>/dev/null || { echo "  ✗ $m (cuarentena) sin listar en su README"; C_FAIL=1; }
done
[ "$C_FAIL" = "0" ] && echo "  ✓ todo módulo aparece en su catálogo" || FAIL=1

# ─── 5. MARCAS DE TIEMPO (AI-GUIDE §22: YYYY-MM-DD HH:MM) ───────────────────
echo
echo "════ [D] MARCAS DE TIEMPO ════"
D_FAIL=0
for f in REFERENCE.md doc/REFERENCE-*.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md; do
  [ -e "$f" ] || continue
  grep -qE '\*\*(Last updated|Última actualización):\*\*' "$f" \
    || { echo "  ✗ $f sin marca de tiempo"; D_FAIL=1; }
done
[ "$D_FAIL" = "0" ] && echo "  ✓ todos los docs técnicos llevan marca de tiempo" || FAIL=1

# ─── RESUMEN ────────────────────────────────────────────────────────────────
echo
if [ "$FAIL" = "0" ]; then
  echo "✅ DOCUMENTACIÓN SINCRONIZADA."
else
  echo "❌ HAY DESINCRONIZACIÓN — corregir ANTES de commitear."
  if [ "$HINT" = "1" ]; then
    echo
    echo "Sugerencias de sed (revisar antes de aplicar):"
    [ -n "$JOBS" ] && echo "  sed -i -E 's/[0-9]+ jobs/$JOBS jobs/g' *.md doc/*.md"
    echo "  sed -i -E 's/[0-9]+ módulos activos/$ACTIVE módulos activos/g' *.md doc/*.md"
  fi
  echo
  echo "⚠️  Recordatorio: NO basta con arreglar el banner. Comprobar también el CUERPO"
  echo "    (tablas resumen, §Próximos pasos, notas de auditoría antiguas)."
fi
exit "$FAIL"
