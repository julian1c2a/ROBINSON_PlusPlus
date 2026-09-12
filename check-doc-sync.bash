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

# ═══ PATH HIGIÉNICO ═════════════════════════════════════════════════════════
# ⚠️ No es paranoia: es un fallo MEDIDO el 2026-09-09. Lanzado desde PowerShell (o desde
# cualquier consola de Windows), `bash` hereda el PATH de Windows, y en esta máquina eso
# hace que `head` resuelva a C:/msys64/ucrt64/bin/head.exe — que no es el `head` de
# coreutils, sino el HEAD de Quantum ESPRESSO — y que `grep` sea otro build que rechaza
# las expresiones de este script («warning: ? at start of expression»).
#
# El resultado era el peor posible: los CUATRO controles [A] salían VACÍOS y el script
# imprimía «✅ DOCUMENTACIÓN SINCRONIZADA» sin haber comprobado absolutamente nada.
# Se antepone el /usr/bin de MSYS2, que es contra el que están escritos estos scripts.
[ -d /usr/bin ] && export PATH="/usr/bin:/bin:$PATH"

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
# ⚠️ Sin `bc`: no está instalado en Git Bash ni, por defecto, en el runner de CI, y
# `paste -sd+ | bc` fallaba en silencio dejando la cifra VACÍA. `wc -l` sobre las
# líneas que casan cuenta lo mismo y no depende de nada.
AXIOMS=$(grep -rhE "^axiom " ROBINSON_PlusPlus/ --include=*.lean 2>/dev/null | wc -l)
# ⚠️ El conteo de `sorry` se DELEGA en check-sorry.bash y no se reimplementa aquí: qué
# cuenta como `sorry` (token de código, fuera de comentarios y de literales) es una
# definición delicada, y tenerla en dos sitios garantiza que se separen.
# ⚠️⚠️ Esta extracción estuvo ROTA POR DOS SITIOS A LA VEZ hasta el 2026‑09‑11:
#   (1) el reemplazo del `sed` era un BYTE DE CONTROL 0x01 en lugar de la
#       retro‑referencia (backslash‑uno), así que de casar habría escrito un SOH
#       donde va un número. ⭐ Y NO fue una errata: escribir esa
#       secuencia a través de la cadena de herramientas la CONVIERTE en 0x01 — se
#       reprodujo sola al arreglarlo. Por eso aquí no se usa ninguna retro‑referencia:
#       se extrae con `grep -oE | grep -oE`, como ya se hacía con JOBS;
#   (2) el patrón sólo cubría la rama «⚠️  Total: N sorry», y con CERO sorry
#       `check-sorry.bash` imprime «✅ No sorry found.» ⇒ el `sed` NO casaba NUNCA y la
#       línea siguiente fijaba SORRY=0 POR DEFECTO.
# ⇒ El «0 sorry» de todos los banners se comparaba contra una CONSTANTE, no contra una
# medición: [A] habría dado verde con el árbol lleno de `sorry`. Es la sexta causa de
# [[feedback-controles-que-no-comprueban]], y la única que estaba en el propio control.
# Ahora se leen LAS DOS ramas y, si no aparece ninguna, se AVISA (§27.1).
SORRY_OUT=$(bash check-sorry.bash 2>/dev/null || true)
SORRY_MISSING=0
if printf '%s' "$SORRY_OUT" | grep -q 'No sorry found'; then
  SORRY=0
elif printf '%s' "$SORRY_OUT" | grep -qE 'Total: [0-9]+ sorry'; then
  SORRY=$(printf '%s' "$SORRY_OUT" | grep -oE 'Total: [0-9]+ sorry' | grep -oE '[0-9]+' | head -1)
else
  SORRY=0
  SORRY_MISSING=1
fi

# ⚠️ `lake` NO está en el PATH de Git Bash en la máquina de desarrollo (sí en el runner
# de CI). Cuando no lo está, `JOBS` quedaba vacío y el control [A] de jobs — el más
# importante — se SALTABA EN SILENCIO dando verde. Ahora se distingue «no lo pedí»
# (`--quick`) de «no pude medirlo», y lo segundo avisa.
JOBS=""
LAKE_MISSING=0
if [ "$QUICK" != "1" ]; then
  if command -v lake >/dev/null 2>&1; then
    JOBS=$(lake build 2>&1 | grep -oE "Build completed successfully \([0-9]+ jobs\)" | grep -oE "[0-9]+" || true)
    [ -z "$JOBS" ] && LAKE_MISSING=2
  else
    LAKE_MISSING=1
  fi
fi

echo "════ VERDAD DEL CÓDIGO ════"
printf "  módulos activos : %s  (Minimal %s + Meta %s + Full %s)\n" "$ACTIVE" "$MIN" "$META" "$FULL"
printf "  cuarentena      : %s\n" "$QUAR"
printf "  sondeos         : %s\n" "$SOND"
printf "  axiom de Lean   : %s\n" "$AXIOMS"
printf "  sorry           : %s
" "$SORRY"
[ -n "$JOBS" ] && printf "  build jobs      : %s\n" "$JOBS"
[ "$LAKE_MISSING" = "1" ] && echo "  ⚠️  build jobs    : SIN MEDIR — 'lake' no está en el PATH de este shell."
[ "$LAKE_MISSING" = "1" ] && echo "                     Lánzalo desde PowerShell, o usa --quick para decirlo a propósito."
[ "$LAKE_MISSING" = "2" ] && echo "  ⚠️  build jobs    : SIN MEDIR — 'lake build' no dijo 'Build completed successfully'."
[ "$SORRY_MISSING" = "1" ] && echo "  ⚠️  sorry         : SIN MEDIR — check-sorry.bash no dijo ni 'No sorry found' ni 'Total: N sorry'."
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

# ⚠️ Los patrones se pasan SIEMPRE entre comillas SIMPLES: un backtick dentro de
#    comillas dobles lo ejecuta bash como sustitución de comando y el patrón queda roto.
check_num () {   # $1 = regex con grupo numérico   $2 = valor correcto   $3 = etiqueta
  local pat="$1" good="$2" label="$3" hits
  # Se descartan: menciones históricas, aproximaciones (~40), rangos (40-50) y ejemplos.
  hits=$(grep -nE "$pat" "$HEADREGION" 2>/dev/null          | grep -viE "hist[oó]rico|previo|antes|era |fueron|→|->|en su momento|entonces|ya no|20[0-9]{2}-[0-9]{2}-[0-9]{2}|~|p\. ej|ejemplo|umbral|[0-9]+-[0-9]+" || true)
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    local n; n=$(echo "$line" | grep -oE "$pat" | grep -oE "[0-9]+" | head -1)
    if [ -n "$n" ] && [ "$n" != "$good" ]; then
      echo "  ✗ $label: dice $n, real $good"
      echo "      ${line:0:150}"
      A_FAIL=1
    fi
  done <<< "$hits"
  # ⚠️ Un patrón sin ninguna aparición NO está comprobando nada, y da verde. Es el peor
  # resultado posible para un control cuyo cometido es que no te fibres de los docs: por eso
  # se avisa en vez de callar. Si sale este aviso, o el fraseo del doc cambió, o el patrón
  # está mal — en los dos casos hay que tocar algo.
  [ -z "$hits" ] && echo "  ⚠️  $label: la frase no aparece en ningún doc autoritativo — control VACÍO"
  return 0
}
[ -n "$JOBS" ] && check_num "[0-9]+ jobs" "$JOBS" "jobs"
check_num "[0-9]+ módulos activos" "$ACTIVE" "módulos activos"
check_num "Meta ([0-9]+ \+|[0-9]+\))" "$META" "conteo de Meta"
check_num "[0-9]+ (módulos )?en \`cuarentena/\`" "$QUAR" "cuarentena"
check_num '[0-9]+ `?axiom`? de Lean' "$AXIOMS" "axiom de Lean"
check_num '[0-9]+ sorrys?' "$SORRY" "sorry"
rm -f "$HEADREGION"
[ "$A_FAIL" = "0" ] && echo "  ✓ sin cifras obsoletas" || FAIL=1

# ─── 2bis. CIFRAS EN EL **CUERPO** ───────────────────────────────────────────
# ⭐ Añadido el 2026-09-10h, y lo pidió una auditoría externa (`doc/book/AUDITORIA-2026-09-10.md`
# §5 y R3), que midió la causa raíz de la deriva documental del proyecto:
#
#     «check-doc-sync.bash:108 — ALCANCE: sólo la REGIÓN DE CABECERA (primeras 100 líneas).
#      Eso explica el patrón entero. El commit 50e8864 pudo declarar la sincronía en verde con
#      ocho contradicciones vivas a partir de la línea 218. No es que nadie mire: es que el
#      control mira sólo el banner, y el banner es justamente la parte que sí se actualiza.
#      Auditar el banner es auditar lo que ya está bien.»
#
# ⚠️ Y la acotación NO era un descuido: sin ella, los diarios de `NEXT-STEPS.md` disparan una
# docena de falsos positivos y el control deja de usarse. Así que el cuerpo entra como **AVISO**,
# igual que [B]: se ve, pide juicio, y no rompe. Lo que rompe sigue siendo la cabecera.
echo ""
echo "════ [A2] CIFRAS EN EL CUERPO — AVISO, requiere juicio ════"
BODYREGION=$(mktemp)
: > "$BODYREGION"
for d in $DOCS; do
  [ -e "$d" ] || continue
  tail -n +101 "$d" | sed "s|^|$d:|" >> "$BODYREGION"
done

A2_HITS=0
warn_num () {   # $1 = regex con grupo numérico   $2 = valor correcto   $3 = etiqueta
  local pat="$1" good="$2" label="$3" hits
  hits=$(grep -nE "$pat" "$BODYREGION" 2>/dev/null          | grep -viE "hist[oó]rico|previo|antes|era |fueron|→|->|en su momento|entonces|ya no|retirad|20[0-9]{2}-[0-9]{2}-[0-9]{2}|20[0-9]{2}‑[0-9]{2}‑[0-9]{2}|~|p\. ej|ejemplo|umbral|[0-9]+-[0-9]+" || true)
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    local n; n=$(echo "$line" | grep -oE "$pat" | grep -oE "[0-9]+" | head -1)
    if [ -n "$n" ] && [ "$n" != "$good" ]; then
      echo "  ⚠️  $label: dice $n, real $good"
      echo "      ${line:0:150}"
      A2_HITS=$((A2_HITS+1))
    fi
  done <<< "$hits"
  return 0
}
[ -n "$JOBS" ] && warn_num "[0-9]+ jobs" "$JOBS" "jobs"
warn_num "[0-9]+ módulos activos" "$ACTIVE" "módulos activos"
warn_num '[0-9]+ `?axiom`? de Lean' "$AXIOMS" "axiom de Lean"
warn_num '[0-9]+ sorrys?' "$SORRY" "sorry"
rm -f "$BODYREGION"
if [ "$A2_HITS" = "0" ]; then
  echo "  ✓ el cuerpo tampoco tiene cifras obsoletas"
else
  echo "  ⚠️  $A2_HITS línea(s) en el CUERPO con cifras que no cuadran."
  echo "      ¿es una afirmación de estado ACTUAL (⇒ corregir) o un registro histórico"
  echo "      sin marcar (⇒ marcarlo: fecha ISO, «previo», «era», «histórico»)?"
fi

echo ""
echo "════ [E] FRESCURA DEL TITULAR — AVISO, requiere juicio ════"
# ⭐ Añadido el 2026-09-11 por la auditoría (hallazgo F-2). El control [A] comprueba las
# CIFRAS del banner y [D] que exista una marca de tiempo, pero NADIE comprobaba la FRASE.
# Resultado medido: SEIS documentos autoritativos compartían el mismo titular del 2026-09-09
# —«C3: 5 de 7 reflectores · D3 a DOS obligaciones»— con las cifras de abajo ya al día.
# C3 se cerró el 10e y D3 se probó el 10g. El titular estaba duplicado ⇒ el error se multiplicó
# por seis, y ningún control lo veía porque no es un número.
#
# La heurística: la fecha del TITULAR de cada doc autoritativo no debería ser anterior a la
# entrada más reciente del CHANGELOG. Si lo es, o el titular se quedó atrás o falta marcarlo.
NEWEST=$(grep -ohE "20[0-9]{2}[-‑][0-9]{2}[-‑][0-9]{2}" CHANGELOG.md 2>/dev/null | sed "s/‑/-/g" | sort -r | head -1)
E_HITS=0
if [ -n "$NEWEST" ]; then
  for d in $DOCS; do
    [ -e "$d" ] || continue
    HEAD_DATE=$(head -12 "$d" | grep -ohE "20[0-9]{2}[-‑][0-9]{2}[-‑][0-9]{2}" | sed "s/‑/-/g" | sort -r | head -1)
    [ -z "$HEAD_DATE" ] && continue
    if [ "$HEAD_DATE" \< "$NEWEST" ]; then
      echo "  ⚠️  $d: titular fechado $HEAD_DATE, y el CHANGELOG llega a $NEWEST"
      echo "      $(head -12 "$d" | grep -m1 -E "ESTADO REAL|^\*\*Estado |^> \*\*Estado " | cut -c1-120)"
      E_HITS=$((E_HITS+1))
    fi
  done
  if [ "$E_HITS" = "0" ]; then
    echo "  ✓ ningún titular se ha quedado atrás del CHANGELOG ($NEWEST)"
  else
    echo "  ⚠️  $E_HITS titular(es) por detrás del CHANGELOG."
    echo "      ⚠️ El titular es una FRASE: [A] no lo ve. Comprobar que lo que AFIRMA sigue"
    echo "      siendo cierto, no sólo que sus cifras cuadren."
  fi
else
  echo "  ⚠️  no pude leer la fecha más reciente del CHANGELOG — control VACÍO"
fi

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

# ─── [F] ARTEFACTOS HUÉRFANOS ───────────────────────────────────────────────
# ⛔⛔ AÑADIDO EL 2026‑09‑12, y por un fallo REAL de la víspera.
#
# El 2026‑09‑11 se puso `FOL/Soundness.lean` en cuarentena porque su teorema es FALSO
# (con `raa` demuestra `False` sin hipótesis). Se movió el fuente, se quitó del barrel,
# se reconstruyó el árbol y dio VERDE. Pero `lake` NO recoge la basura: el
# `.olean` COMPILADO se quedó, `import FOL.Soundness` SEGUÍA RESOLVIENDO desde él, y
# `False` se demostraba al día siguiente exactamente igual.
#
# 🔑 La lección: **retirar el FUENTE no retira el MÓDULO**. Un `.olean` sin `.lean` es un
# módulo fantasma — importable, invisible al build y sin fuente que auditar.
#
# Este bloque ROMPE: no hay ningún caso legítimo de `.olean` sin fuente.
echo
echo "════ [F] ARTEFACTOS HUÉRFANOS (.olean sin fuente) ════"
F_FAIL=0
for ROOT in "." "../FOL"; do
  LAKEDIR="$ROOT/.lake/build/lib/lean"
  [ -d "$LAKEDIR" ] || continue
  while IFS= read -r O; do
    [ -n "$O" ] || continue
    REL="${O#$LAKEDIR/}"
    SRC="$ROOT/${REL%.olean}.lean"
    if [ ! -f "$SRC" ]; then
      echo "  ✗ módulo FANTASMA: ${REL%.olean} — hay .olean pero NO hay fuente"
      echo "      $O"
      F_FAIL=1
    fi
  done <<< "$(find "$LAKEDIR" -name '*.olean' 2>/dev/null)"
done
if [ "$F_FAIL" = "0" ]; then
  echo "  ✓ ningún .olean sin fuente (ni aquí ni en ../FOL)"
else
  echo "  ⚠️  un .olean sin fuente SIGUE SIENDO IMPORTABLE. Bórralo:"
  echo "      rm -f <ruta>.olean <ruta>.olean.hash <ruta>.ilean <ruta>.ilean.hash <ruta>.trace"
  FAIL=1
fi

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
