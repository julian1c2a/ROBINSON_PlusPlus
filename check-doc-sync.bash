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
# ⛔ 2026-10-03 (ADR-116): antes era `grep "^axiom "`, ciego a `private`/`@[…]`/sangrados y crédulo con
# los docstrings. Ahora es el mismo patrón que `check-axioms.bash` (de FOL), sobre el código sin
# comentarios (`strip-lean.awk`). El censo autoritativo, por entorno, es `check-estratos.bash` de RPP.
# ⛔⛔ 2026-10-04 (ADR-116, segunda revisión): y la primera versión de esa línea daba SIEMPRE 0. Donde
# iba la continuación de línea había un `\n` LITERAL (la cadena de herramientas se comió la barra al
# escribirla): `find` recibía «\n» como un camino más y fallaba, y el `|| true` del final se tragaba
# el fallo. Como el árbol tiene de verdad 0 `axiom`, la cifra cuadraba con los documentos y nadie lo
# vio: un `axiom` nuevo habría dado VERDE. Ahora la cuenta es una función que DEVUELVE su fallo, y
# antes de medir el árbol mide un fixture con TRES `axiom` reales y cinco señuelos: si no salen 3,
# no se mide (y no medir es rojo).
# 🔑 *Un `|| true` al final de una tubería convierte «no he podido medir» en «cero».*
AX_RE='^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|unsafe|partial)[[:space:]]+)*axiom[[:space:]]+[^[:space:]:({]+'
cuenta_axiomas () {   # $@ = caminos; imprime la cifra, o nada y estado 2 si no ha podido medir
  local p n
  for p in "$@"; do [ -e "$p" ] || return 2; done
  [ -n "$(find "$@" -name '*.lean' ! -path '*/.lake/*' -print -quit)" ] || return 2
  n=$(find "$@" -name '*.lean' ! -path '*/.lake/*' -print0 \
        | xargs -0 env LC_ALL=C awk -f strip-lean.awk \
        | { grep -E "$AX_RE" || [ $? -eq 1 ]; } | wc -l) || return 2
  printf '%s\n' "$n" | tr -d ' '
}
AX_FIX=$(mktemp -d)
cat > "$AX_FIX/Fixture.lean" <<'EOF'
/-- un docstring con «axiom senuelo1 : True» -/
axiom real1 : True
-- axiom senuelo2 : True
@[simp] private axiom real2 : True
def s := "axiom senuelo3 : True"
/-- doc -/ axiom real3 : True
/- axiom senuelo4 : True -/ def t := 0
theorem u : True := trivial -- axiom senuelo5
EOF
AXIOMS=""
if [ "$(cuenta_axiomas "$AX_FIX" || true)" = "3" ]; then
  AXIOMS=$(cuenta_axiomas ROBINSON_PlusPlus/ || true)
fi
rm -rf "$AX_FIX"
AXIOMS_MISSING=0
[ -n "$AXIOMS" ] || AXIOMS_MISSING=1
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
printf "  sorry           : %s\n" "$SORRY"
[ -n "$JOBS" ] && printf "  build jobs      : %s\n" "$JOBS"
[ "$LAKE_MISSING" = "1" ] && echo "  ⚠️  build jobs    : SIN MEDIR — 'lake' no está en el PATH de este shell."
[ "$LAKE_MISSING" = "1" ] && echo "                     Lánzalo desde PowerShell, o usa --quick para decirlo a propósito."
[ "$LAKE_MISSING" = "2" ] && echo "  ⚠️  build jobs    : SIN MEDIR — 'lake build' no dijo 'Build completed successfully'."
[ "$SORRY_MISSING" = "1" ] && echo "  ⚠️  sorry         : SIN MEDIR — check-sorry.bash no dijo ni 'No sorry found' ni 'Total: N sorry'."
[ "$AXIOMS_MISSING" = "1" ] && echo "  ⚠️  axiom de Lean : SIN MEDIR — el autotest de cuenta_axiomas no dio 3 (¿strip-lean.awk, LC_ALL?)."
echo

# Documentos AUTORITATIVOS: los que describen el ESTADO ACTUAL y por tanto deben cuadrar.
# Quedan fuera, y con razón, los de diario, diseño e historia (CHANGELOG, GODEL-*-DESIGN,
# PLAN-*, THOUGHTS, MINIMAL-AXIOMS…): sus cifras y símbolos son históricos POR DISEÑO.
AUTHORITATIVE="REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md AXIOMS.md GODEL-STATUS.md NEXT-STEPS.md"
AUTHORITATIVE="$AUTHORITATIVE $(ls doc/REFERENCE-*.md 2>/dev/null) cuarentena/README.md sondeos/README.md"
DOCS="$AUTHORITATIVE"
FAIL=0

# ⚠️ SI NO SE PUEDE MEDIR, ES ROJO (añadido el 2026-09-17, medido en PeanoRF).
# Hasta hoy `LAKE_MISSING`/`SORRY_MISSING` sólo IMPRIMÍAN «SIN MEDIR» y el script seguía y
# salía con 0: anunciaba verde sobre cifras que nadie había comprobado. En PeanoRF eso
# llegó a empujar un commit con el check en rojo, creyéndolo verde.
# 🔑 Un control tiene TRES resultados —pasa, falla, NO HE PODIDO COMPROBARLO— y colapsar
# el tercero en el primero es lo que lo convierte en decoración. El único verde sin medida
# es el que se pide a mano con `--quick`, y ése se anuncia como tal.
if [ "$QUICK" != "1" ] && { [ "$LAKE_MISSING" != "0" ] || [ "$SORRY_MISSING" != "0" ]; }; then
  FAIL=1
fi
# El censo de `axiom` no depende de `lake`: no medirlo es rojo también con `--quick`.
[ "$AXIOMS_MISSING" != "0" ] && FAIL=1

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
[ -n "$AXIOMS" ] && check_num '[0-9]+ `?axiom`? de Lean' "$AXIOMS" "axiom de Lean"
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
[ -n "$AXIOMS" ] && warn_num '[0-9]+ `?axiom`? de Lean' "$AXIOMS" "axiom de Lean"
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
echo "════ [E] FRESCURA DEL TITULAR — ROJO (objetivo: lo decide git) ════"
# ⭐ Añadido el 2026-09-11 por la auditoría (hallazgo F-2): [A] comprueba las CIFRAS del banner
# y [D] que EXISTA una marca de tiempo, pero nadie comprobaba que la marca fuera CIERTA.
#
# ⛔⛔ REARMADO EL 2026-09-18 (auditoría A3, ADR-072). Estaba desarmado por TRES vías y daba
# verde sin comprobar nada:
#   1. La referencia era la entrada más reciente de CHANGELOG.md — un documento que un HUMANO
#      tiene que actualizar. Congelado en 2026-05-16 con **111 commits** detrás, `NEWEST` se
#      quedaba viejo y NINGÚN doc podía estar «por detrás»: aprobaba siempre.
#   2. `E_HITS` no tocaba `FAIL` en ninguna rama, ni en la de «control VACÍO».
#   3. Leía la fecha con `head -12`, y `**Last updated:**` vive en la línea 22-38 ⇒ medía la
#      fecha de OTRA cosa (el aviso histórico de la cabecera).
#
# 🔑 *Un control cuya REFERENCIA es un documento que alguien tiene que mantener se pudre con
# él. La referencia tiene que CALCULARSE.* Aquí se calcula, y por documento: la fecha del
# ÚLTIMO COMMIT QUE TOCÓ ESE DOCUMENTO, que no se puede quedar vieja.
#
# ⚠️ LA TABLA DE DEUDA, y por qué existe: al rearmarlo, la medición dio 21 defectos en 24
# documentos — deuda ANTERIOR, acumulada mientras el control estaba ciego. Ponerlo en rojo de
# golpe habría dejado el repo en rojo indefinidamente; callarla habría sido volver al verde
# falso. Se declara, como en `check-warnings.bash` (ADR-065), y el control **ROMPE EN LOS DOS
# SENTIDOS**: si un doc NO declarado falla, rojo; y si un doc declarado ya está bien, también
# rojo — *la deuda se saldó, quítala de la tabla*. Así la cifra sólo puede BAJAR.
read -r -d '' E_DEUDA <<'EOF'
REFERENCE.md
CURRENT-STATUS-PROJECT.md
DEPENDENCIES.md
README.md
AXIOMS.md
GODEL-STATUS.md
doc/REFERENCE-Arithmetic.md
doc/REFERENCE-Full.md
doc/REFERENCE-Incompleteness.md
doc/REFERENCE-Kernel.md
cuarentena/README.md
# ── ampliación del universo, 2026-09-22 (ADR-084): los 21 defectos de los 25
#    documentos que `[E]` nunca había mirado. La cifra sólo puede BAJAR.
.claude/commands/docsync.md
AI-GUIDE.md
CHANGELOG.md
DISCUSIONES.md
doc/AUDITORIA-2026-09-11.md
doc/AUDITORIA-FOL-2026-09-12.md
doc/FEEDBACK-PARA-EL-LIBRO.md
GODEL-D3-TRACKED-DESIGN.md
GODEL-D-ARITHMETIZATION.md
MINIMAL-AXIOMS.md
PLAN-FRENTE-A.md
PLAN-LIBRO.md
PLAN-NEGVERIFIER.md
PLANNING.md
PLAN-PRUEBAS.md
PLAN-SORTES.md
Sobre_el_libro.md
# TEOREMAS-E-HIPOTESIS.md — SALDADA el 2026-10-02 (ADR-115): reescrito entero, con su marca.
THOUGHTS.md
TuplasFuncionesYListas.md
WORKFLOW.md
# ── y estas TRES las cazó el propio control, no la medición a mano: `comm` con
#    locales distintos se las había comido. 🔑 Mi red era la estrecha esta vez.
doc/PLAN-COMPLETITUD-FINITISTA.md
ESCALANDO_EL_PROYECTO.md
NAMING-CONVENTIONS.md
EOF

# ⛔ GUARDA DEL CLON SUPERFICIAL (2026-09-18, ADR-072). En `--depth 1`, `git log -1 -- <f>`
# devuelve HEAD para TODOS los ficheros ⇒ este control mediría basura y la CI se pondría roja
# con falsos positivos. Pasó: la primera ejecución en CI. No se calla, se ROMPE diciendo qué
# hacer. 🔑 *Un control que depende de la historia de git mide OTRA COSA bajo un clon
# superficial, y la diferencia no se ve en local.*
if [ "$(git rev-parse --is-shallow-repository 2>/dev/null)" = "true" ]; then
  echo "  ❌ CLON SUPERFICIAL: \`git log\` no tiene historia, este control no puede medir."
  echo "      Arreglo: \`fetch-depth: 0\` en el paso de checkout del workflow."
  FAIL=1
fi
# ⛔⛔ EL UNIVERSO DE ESTE CONTROL, AMPLIADO EL 2026-09-22 (ADR-084).
# Hasta hoy `[E]` recorría `$DOCS` = los **15 AUTHORITATIVE**. Los otros **25** `.md` del repo
# —AI-GUIDE, CHANGELOG, PLANNING, WORKFLOW, THOUGHTS, los PLAN-*, los GODEL-*, las auditorías—
# **no los miraba nadie**, y de esos 25 había **21 defectuosos**.
# ⚠️ La cifra publicada decía «11 de 18». Medida sobre el repo entero: **30 de 40**.
# 🔑 *Un control con universo estrecho no mide menos: mide OTRA COSA, y publica la cifra
#    como si fuera la del repo.* Es la misma trampa que `[COBERTURA]` (ADR-073) y que `[H]`
#    (más abajo, mismo día): mirar lo declarado en vez de mirar el ÁRBOL.
# ⛔ Y lo que NO se hizo: poner la fecha de hoy en los 30. Eso sería actualizar el BANNER sin
# tocar el CUERPO, que es exactamente el defecto que este control existe para cazar.
E_UNIVERSO="$DOCS $(git ls-files '*.md' 2>/dev/null | grep -v '^doc/book/')"
E_BAD=0      # documentos que fallan y NO estaban declarados
E_SALDADA=0  # documentos declarados que ya están bien ⇒ hay que quitarlos de la tabla
E_DECL=0     # deuda declarada que sigue vigente
for d in $(printf '%s\n' $E_UNIVERSO | sort -u); do
  [ -e "$d" ] || continue
  GIT_DATE=$(git log -1 --format=%ad --date=short -- "$d" 2>/dev/null)
  LU=$(grep -m1 -iE "^\*\*Last updated" "$d" 2>/dev/null \
       | grep -ohE "20[0-9]{2}[-‑][0-9]{2}[-‑][0-9]{2}" | sed "s/‑/-/g" | head -1)
  EN_TABLA=0
  while IFS= read -r t; do
    [ -n "$t" ] || continue
    [ "$t" = "$d" ] && EN_TABLA=1
  done <<< "$E_DEUDA"

  ESTADO="ok"
  MOTIVO=""
  if [ -z "$LU" ]; then
    ESTADO="mal"; MOTIVO="sin marca \`**Last updated:**\`"
  elif [ -z "$GIT_DATE" ]; then
    ESTADO="mal"; MOTIVO="sin historia en git"
  elif [ "$LU" \< "$GIT_DATE" ]; then
    ESTADO="mal"; MOTIVO="la marca dice $LU y el último commit que lo tocó es $GIT_DATE"
  fi

  if [ "$ESTADO" = "mal" ] && [ "$EN_TABLA" = "0" ]; then
    echo "  ❌ $d: $MOTIVO"
    E_BAD=$((E_BAD+1))
  elif [ "$ESTADO" = "mal" ]; then
    E_DECL=$((E_DECL+1))
  elif [ "$EN_TABLA" = "1" ]; then
    echo "  ❌ $d: la deuda ESTÁ SALDADA — quítalo de la tabla E_DEUDA de este script."
    E_SALDADA=$((E_SALDADA+1))
  fi
done
echo "  deuda declarada: $E_DECL   ·   sin declarar: $E_BAD   ·   saldadas sin quitar: $E_SALDADA"
if [ "$E_BAD" = "0" ] && [ "$E_SALDADA" = "0" ]; then
  echo "  ✓ ninguna marca de tiempo miente fuera de la deuda declarada"
else
  echo "      ⚠️ El titular es una FRASE: [A] no lo ve. Al actualizar la marca, comprobar que lo"
  echo "      que el titular AFIRMA sigue siendo cierto, no sólo que sus cifras cuadren."
  FAIL=1
fi

# ─── 3. SÍMBOLOS MUERTOS ─────────────────────────────────────────────────────
# Un símbolo está MUERTO si se cita en un doc AUTORITATIVO pero ninguna declaración
# del árbol activo se llama así.
#
# Dos calibraciones aprendidas al estrenar este control (2026-08-23):
#   * Sólo se miran los docs AUTORITATIVOS (los que describen el estado actual). Los
#     de diseño e historia — MINIMAL-AXIOMS, THOUGHTS, GODEL-*-DESIGN, PLAN-* — citan
#     por diseño cosas que ya no están, y marcarlos sería ruido.
#   * (✏️ 2026-10-03, ADR-116: REVOCADA.) Se comparaba por PREFIJO («la prosa abrevia»), y eso
#     absolvía a todo nombre que empezara como uno vivo. Hoy se casa el nombre EXACTO, y una
#     familia se cita con `_` final (`ax_C3_`): ver (2) más abajo.
echo
echo "════ [B] SÍMBOLOS MUERTOS — ROJO, con trinquete ════"
echo "   (deuda DECLARADA y con trinquete desde 2026-09-22: no puede crecer.)"
# ⛔⛔ ADJUDICADO EL 2026-09-22 (ADR-084): `[B]` deja de ser AVISO y pasa a ser CONTROL.
#
# Nacía como aviso porque «hay menciones legítimas en secciones de diseño e historia», y eso
# es cierto — pero un aviso que nadie adjudica es una lista que crece sola. Los `DEAD_MARKER`
# de arriba ya absuelven las menciones históricas bien marcadas; lo que queda **no está
# marcado**, y por tanto o se marca o se arregla.
#
# ⚠️ LA CIFRA: el banner del proyecto hablaba de «los 223 nombres». Medido hoy son **44**.
# No es que se hayan adjudicado 179: es que 223 era el conteo de CANDIDATOS antes de aplicar
# los marcadores. 🔑 *Una cifra de deuda sin decir en qué punto del filtro se tomó no es
# comparable consigo misma.*
#
# ⬜ La deuda REAL que queda, y es de LECTURA, no de script: cada uno de los 44 pide mirar su
# línea y decidir si es historia (⇒ marcarla) o una afirmación de estado caducada (⇒ arreglar
# el doc). Mientras tanto el trinquete garantiza que **no puede crecer**.
# 2026-10-03 (ADR-116): 44 → 41. Al pasar [B] a nombre exacto, las líneas de 16 símbolos que pasaban
# por un homónimo más largo se corrigieron una a una, y de paso quedaron marcadas las últimas citas
# de `goedel_first_real`, `prf_isTsC` y `prf_tc_substfc`: el trinquete las pidió quitar.
read -r -d '' B_DEUDA <<'EOF'
ax_notInAxC
ax_tc_liftfc
ax_tc_substfc
godelC'_fixedpoint
goedel_first_real'
goedel_first_undecidable_real'
goedel_second'
pcc_axiom_inst_k
pcc_binOk_tracked
pcc_congr_hole_code
pcc_eval_substfc_wit_REAL
pcc_eval_substtc'
pcc_eval_substtsc'
pcc_In_tracked
pcc_isFCB_tracked
pcc_nodeOk_pure
pcc_substfc_forall_dot
pcc_thm_inst_k
pcc_wfAll_tracked
pcc_wfAll_tracked_lit
prf_add_eq_zero_right
prf_crit_In_F_rejects_open
prf_div2_double_all
prf_isFC_junk
prf_isFC_nil
prf_isFC_varc
prf_isFCB_bottom
prf_isFormCodeE_str
prf_isTermCodeE_str
prf_liftc_arith_open
prf_tagConcl_code
prf_tc_carc
prf_tc_cons
prf_tc_cons'
prf_tc_eqc
prf_tc_nthc
prf_tc_nul
prf_tc_objAt
prf_tc_of_cons
prf_wfAll_objList
repr_neg
EOF
B_FAIL=0
# ⛔ 2026-10-04 (ADR-116, segunda revisión): el «de 41» del final era un literal que nada comparaba.
# Ahora el tope es un dato y se compara con la tabla en los DOS sentidos: crece la tabla sin subir
# el tope ⇒ rojo; se salda una deuda y no se baja ⇒ rojo. 🔑 *El tope sólo BAJA: subirlo es aceptar
# deuda nueva, y eso pide un ADR, no un commit de documentación.*
B_TOPE=41
AUTHORITATIVE="REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md AXIOMS.md GODEL-STATUS.md NEXT-STEPS.md"
AUTHORITATIVE="$AUTHORITATIVE $(ls doc/REFERENCE-*.md 2>/dev/null) cuarentena/README.md sondeos/README.md"
# Marcadores que hacen LEGÍTIMA la mención de un símbolo inexistente:
#   (a) se declara retirado;  (b) es hipotético/propuesto/descartado;  (c) va en una
#   entrada fechada (histórico por diseño).
# ⚠️⚠️ MEDIDO EL 2026-10-02 (ADR-115): en msys (GNU grep 3.0, locale es_ES.UTF-8) la alternativa
# `🗑️` de abajo NO CASA NUNCA — grep no maneja en UTF-8 un carácter fuera del BMP (`⏳` y `✏` sí casan;
# `🗑` no, con o sin U+FE0F; con LC_ALL=C sí). En la CI (Linux) casa. ⇒ el MISMO documento podía dar
# verde en CI y rojo en local. Regla: una marca de retirada lleva SIEMPRE una palabra (`retirad…`),
# no sólo el emoji. 🔑 *Un patrón que no casa en el entorno donde se ejecuta no es un patrón.*
# ⭐ 2026-10-04: desde la segunda revisión los marcadores se aplican por BYTES (awk con LC_ALL=C), así
# que casan igual en msys y en Linux — `🗑️` incluido. Por eso un acento va con `(e|é)` y no con `[eé]`
# (en modo byte un corchete casa UN byte, y `é` son dos), y la fecha sin `{2}` (no todo awk lo lee).
DEAD_MARKER='YA NO EXISTE|NO EXISTEN|retirad|RETIRADO|eliminad|borrad|legacy|F7a|histórico|ANTERIORES|🗑️|muert|Aquí vivía|tampoco existe|inexistente|desapareci|ya no son|se borró'
DEAD_MARKER="$DEAD_MARKER"'|propuest|candidat|hipot(e|é)tic|har(i|í)a falta|si se |habr(i|í)a que|añadir |descartad|no existe|NO EXISTE|sin materializar|20[0-9][0-9]-[0-9][0-9]-[0-9][0-9]'
#   (d) es un OBJETIVO declarado, no una afirmación de que ya está.
DEAD_MARKER="$DEAD_MARKER"'|falta|FALTA|construir|objetivo|medir|sin medir|pendiente|⏳|abiert|necesita|exige|pide|TAREA|hace falta|no hay ni habrá|sub‑familia|sub-familia|buscaba|buscó|usan la'
#   (e) 2026-10-03 (ADR-116): vive en `sondeos/`, FUERA del árbol activo, y la línea lo dice. No es un
#       marcador de texto (eximía líneas que nombran `sondeos/` por otra razón): se exime la línea que
#       nombra el FICHERO que lo declara (`sondeos/Foo.lean`, o `sondeos/Foo`) — desde la segunda
#       revisión, ese fichero y no otro sondeo cualquiera.
# El árbol de declaraciones incluye `cuarentena/`: esos símbolos EXISTEN (están fuera
# del build, no borrados), y los docs los discuten con razón.
# ⛔⛔ 2026-10-03 (ADR-116 de RPP): dos defectos de este bloque, medidos. (1) Las declaraciones se
# sacaban del texto ENTERO, comentarios incluidos: un nombre que sólo aparece en prosa (p. ej. el
# «axiom ax_list_induction» de un docstring de RPP) pasaba por VIVO. Ahora salen del código SIN
# comentarios ni cadenas (`strip-lean.awk`), y con todas las palabras clave de declaración.
# (2) Se casaba por PREFIJO («la prosa abrevia»): `ax_list_induction` pasaba por vivo porque existe
# `ax_list_induction_refutable`, y `d3_prf` porque existe `d3_prf_real`. Ahora se casa el nombre
# EXACTO; la abreviatura de una FAMILIA se escribe con `_` final (`prf_tc_`), y sólo ésa casa por
# prefijo. 🔑 *Un control que casa por prefijo absuelve a todo nombre que empiece igual que uno vivo.*
# (3) 2026-10-03, v2 (revisión adversarial): el NOMBRE se toma entero (`prf_foo₀`, `Prf.prf_bar`: antes
# se cortaba en el primer carácter no ASCII o en el primer `.`) y se guarda también su último
# componente; el ALCANCE es explícito (antes entraban `auditoria/`, las librerías muertas y, en local,
# `Probe/`, que la CI no tiene); y si la lista sale vacía o sin un nombre que existe seguro, NO se mide.
# (4) 2026-10-04, segunda revisión: (a) las CITAS se leen enteras también: calificadas
# (`GodelTwo.goedel_second'`, que vale por su último componente) y con caracteres no ASCII
# (`prf_zz₀`); antes el patrón se paraba en el `.` o en el subíndice y esas citas no las miraba nadie;
# (b) `def prf_univ.{u}` declara `prf_univ` (antes, `prf_univ.` y un nombre vacío); (c) la pasada es
# UNA sola de awk sobre los documentos —antes, un grep por símbolo y documento: ~90 s en msys—;
# (d) si falta la copia de FOL del despojador, rojo (antes se saltaba la comparación en silencio).
# ⚠️ Lo que NO ve: los constructores y los campos de estructura no son declaraciones de primer nivel,
# así que citar uno sale como MUERTO — falso rojo, nunca falso verde; se arregla citando el tipo.
if [ ! -f ../FOL/strip-lean.awk ]; then
  echo "  ❌ falta ../FOL/strip-lean.awk: no puedo comprobar que las dos copias del despojador sean la misma."
  B_FAIL=1
elif ! cmp -s <(grep -v '^#' strip-lean.awk | tr -d '\r') <(grep -v '^#' ../FOL/strip-lean.awk | tr -d '\r'); then
  # (sin los `\r`: FOL no fuerza LF y, con core.autocrlf, su copia sale con CRLF tras un checkout en Windows)
  echo "  ❌ strip-lean.awk y ../FOL/strip-lean.awk ya no tienen el mismo código: unifícalos."
  B_FAIL=1
fi
DECL_RE="(^|[^A-Za-z0-9_'.])(theorem|lemma|def|abbrev|axiom|opaque|instance|structure|inductive|class) +[^[:space:]:({[]+"
# el nombre entero y su último componente; `prf_univ.{u}` → `prf_univ`
NOMBRES='{n = $NF; sub(/[.]$/, "", n); if (n == "") next; print n; k = n; sub(/.*[.]/, "", k); if (k != n && k != "") print k}'
DECLS=$(mktemp); DECLS_SOND=$(mktemp); B_SALIDA=$(mktemp); B_VISTOS=$(mktemp)
find ROBINSON_PlusPlus/ cuarentena/ ../FOL/FOL/ ../FOL/TheoryFramework/ ../FOL/FOL.lean -name '*.lean' ! -path '*/.lake/*' -print0 2>/dev/null \
  | xargs -0 env LC_ALL=C awk -f strip-lean.awk | grep -oE "$DECL_RE" | awk "$NOMBRES" | sort -u > "$DECLS"
# (e): «nombre|fichero» de cada declaración de un sondeo
find sondeos/ -name '*.lean' 2>/dev/null | sort | while IFS= read -r f; do
  LC_ALL=C awk -f strip-lean.awk "$f" | grep -oE "$DECL_RE" | awk "$NOMBRES" | awk -v f="$f" '{print $0 "|" f}'
done | sort -u > "$DECLS_SOND"
B_MEDIDO=1
if [ "$(wc -l < "$DECLS" | tr -d ' ')" -lt 1000 ] || ! grep -qxF goedel_first_prf "$DECLS" \
   || ! grep -qxF derives0_soundness "$DECLS" || ! grep -q '^prf_wfAll_objList|sondeos/' "$DECLS_SOND"; then
  echo "  ❌ NO PUDE MEDIR [B]: las declaraciones salen vacías o sin \`goedel_first_prf\`, \`derives0_soundness\`"
  echo "      o \`prf_wfAll_objList\` (de un sondeo), que existen seguro (¿strip-lean.awk?)."
  B_FAIL=1; B_MEDIDO=0
fi
B_DOCS=""
for d in $AUTHORITATIVE; do [ -f "$d" ] && B_DOCS="$B_DOCS $d"; done
if [ "$B_MEDIDO" = "1" ]; then
  # UNA pasada: cada cita `…` con la forma de un símbolo; viva si su nombre entero o su último
  # componente está declarado (una familia, con `_` final, por prefijo); si no, la línea se exime
  # por un marcador o por nombrar el sondeo que lo declara; lo que queda sale como «clave|cita|línea».
  LC_ALL=C awk -v MARK="$DEAD_MARKER" '
    FILENAME == ARGV[1] { vivo[$0] = 1; next }
    FILENAME == ARGV[2] { p = index($0, "|"); k = substr($0, 1, p - 1); sond[k] = sond[k] "|" substr($0, p + 1); next }
    {
      s = $0
      # un carácter de nombre: ASCII, o en UTF-8 una letra (2 bytes), un subíndice, un letterlike, ⱼ,
      # el griego extendido o el alfabeto matemático — NO la puntuación general (`1‑3`, `a–b`, `…`)
      while (match(s, /`([A-Z][A-Za-z0-9_]*[.])*(prf_|pcc_|goedel_|godel|d[123]_|repr_|ax_)([A-Za-z0-9_'"'"'!?]|[\303-\337][\200-\277]|\342(\202|\204|\205|\261)[\200-\277]|\341[\265-\277][\200-\277]|\360\235[\200-\277][\200-\277])+`/)) {
        t = substr(s, RSTART + 1, RLENGTH - 2); s = substr(s, RSTART + RLENGTH)
        k = t; sub(/^([A-Z][A-Za-z0-9_]*[.])*/, "", k)
        # los axiomas objeto son snake_case: `ax_UpperCamel` es un PLACEHOLDER de convención
        # de nombres (`ax_TagDescriptor`), no un símbolo
        if (k ~ /^ax_[A-Z]/) continue
        if ((t in vivo) || (k in vivo)) continue
        if (k ~ /_$/) {
          if (!(k in fam)) { fam[k] = 0; for (v in vivo) if (index(v, k) == 1) { fam[k] = 1; break } }
          if (fam[k]) continue
        }
        if ($0 ~ MARK) continue
        if (k in sond) {
          nf = split(substr(sond[k], 2), fs, "|"); ex = 0
          for (q = 1; q <= nf; q++) { b = fs[q]; sub(/[.]lean$/, "", b); if (match($0, b "([^A-Za-z0-9_]|$)")) ex = 1 }
          if (ex) continue
        }
        print k "|" t "|" FILENAME ":" FNR ":" $0
      }
    }' "$DECLS" "$DECLS_SOND" $B_DOCS > "$B_SALIDA"
  cut -d'|' -f1 "$B_SALIDA" | sort -u | while IFS= read -r k; do
    if printf '%s\n' "$B_DEUDA" | grep -qxF "$k"; then
      echo "$k" >> "$B_VISTOS"
    else
      echo "  ❌ \`$k\` no existe en el árbol activo, se cita sin marcar como retirado,"
      echo "      y NO está en la tabla B_DEUDA de este script:"
      awk -F'|' -v k="$k" '$1 == k' "$B_SALIDA" | head -2 | cut -d'|' -f3- | sed 's/^/      /' | cut -c1-140
      echo x >> "$B_SALIDA.rojo"
    fi
  done
  [ -s "$B_SALIDA.rojo" ] && B_FAIL=1
  # ⛔⛔ EL AGUJERO QUE ESTO TAPA (2026-09-22, cazado por su propia prueba de rotura):
  # el bucle de arriba recorre los símbolos **CITADOS**. Una entrada de `B_DEUDA` cuyo documento
  # se arregle deja de estar citada ⇒ **no vuelve a entrar en el bucle nunca**, y la tabla se
  # quedaría con fantasmas para siempre. La comprobación de «deuda saldada» tiene que hacerse
  # DESPUÉS del bucle, contra la tabla, no dentro.
  # 🔑 *Un trinquete que sólo mira lo que entra en el bucle no es un trinquete: es media
  #    cuenta.* La versión de `[E]` no tenía el agujero porque recorre los DOCUMENTOS, que
  #    siempre existen; ésta recorre las CITAS, que desaparecen.
  while IFS= read -r t; do
    [ -n "$t" ] || continue
    case "$t" in '#'*) continue ;; esac
    if ! grep -qxF "$t" "$B_VISTOS" 2>/dev/null; then
      echo "  ❌ \`$t\`: declarado en B_DEUDA pero YA NO se cita como vigente — quítalo de la tabla."
      B_FAIL=1
    fi
  done <<< "$B_DEUDA"
fi
B_NT=$(printf '%s\n' "$B_DEUDA" | grep -v '^#' | grep -c . || true)
if [ "$B_NT" != "$B_TOPE" ]; then
  echo "  ❌ la tabla B_DEUDA tiene $B_NT entradas y su tope (B_TOPE) es $B_TOPE: tabla y tope cambian juntos,"
  echo "      y el tope sólo baja."
  B_FAIL=1
fi
B_DECL=$(sort -u "$B_VISTOS" | grep -c . || true)
rm -f "$DECLS" "$DECLS_SOND" "$B_SALIDA" "$B_SALIDA.rojo" "$B_VISTOS"
if [ "$B_MEDIDO" = "1" ]; then
  echo "  deuda declarada: $B_DECL de $B_NT (tope $B_TOPE) · sin declarar y sin saldar: rompen arriba"
else
  echo "  deuda declarada: SIN MEDIR"
fi
[ "$B_FAIL" = "0" ] && echo "  ✓ ningún símbolo muerto citado como vigente" || FAIL=1

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
# ⛔⛔ AÑADIDO el 2026-09-17. Hasta hoy este control SOLO miraba los modulos de
# ROBINSON_PlusPlus contra SU REFERENCE.md: los de FOL no los miraba NADIE, y por eso
# veintiseis modulos llevaban dias sin proyectar en FOL/REFERENCE.md §6 sin que saltara
# nada. Y se comprueba contra §6 (Exports), que es lo que AI-GUIDE §14 exige de verdad
# -- no basta con que el nombre aparezca en la tabla de modulos.
if [ -f ../FOL/REFERENCE.md ]; then
  FOLEXP=$(sed -n '/^## 6\. Exports/,/^## 7\./p' ../FOL/REFERENCE.md)
  for f in ../FOL/FOL/*.lean ../FOL/FOL/Theorems/*.lean; do
    [ -e "$f" ] || continue
    m=${f#../FOL/FOL/}; m=${m%.lean}
    [ "$m" = "FOL" ] && continue
    # ⚠ Frontera de palabra OBLIGATORIA, y la RUTA y no el basename:
    #   • con `grep -F "Eq.lean"` el modulo `Theorems/Eq.lean` daba VERDE porque
    #     "Eq.lean" es subcadena de "DecEq.lean";
    #   • con el basename, `Deduction.lean` y `Theorems/Deduction.lean` eran el MISMO
    #     control, y una sola entrada absolvia a los dos.
    # Un control que casa por subcadena no comprueba: absuelve.
    case "$m" in
      */*) PAT="(^|[^A-Za-z0-9_])$m\.lean" ;;
      *)   PAT="(^|[^A-Za-z0-9_/])$m\.lean" ;;
    esac
    if ! printf '%s' "$FOLEXP" | grep -qE "$PAT"; then
      echo "  ✗ FOL/$m NO esta proyectado en ../FOL/REFERENCE.md §6 (AI-GUIDE §14)"
      C_FAIL=1
    fi
  done
fi

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

echo '════ [H] CATÁLOGO DE `sondeos/` — ROJO, y rompe en LOS DOS SENTIDOS ════'
# ⛔⛔ POR QUÉ EXISTE (2026-09-22, ADR-084): `sondeos/` está FUERA del build por diseño, así que
# `[C]` —que proyecta los módulos de las `lean_lib`— **no lo mira**. Resultado: el catálogo de
# sondeos no lo vigilaba nadie, que es exactamente la condición que ya costó reconstruir dos
# veces algo que estaba medido («un módulo sin proyectar se vuelve a construir»).
#
# ⛔ Y AL ESCRIBIRLO CAMBIÓ LA CIFRA. La medición vieja decía «13 de 74 sin proyectar»; salía de
# contar como proyectado cualquier fichero **mencionado en la prosa** de otra fila. Casando sólo
# contra **cabeceras de fila** (`| **`X.lean`** |` a principio de línea) son **19 de 76**.
# 🔑 *Un control que casa por SUBCADENA absuelve, y la cifra que produce es más alta que la
#    verdad.* Es la novena vez que este repo paga esa trampa; la primera en la que muerde a una
#    cifra que ya estaba publicada como «medida».
#
# ⚠️ Rompe en los DOS sentidos a propósito: un fichero sin fila es trabajo que se va a repetir,
# y una fila sin fichero es una referencia falsa —el mismo daño que el CHANGELOG congelado de
# ADR-072—. `lintlab/` no acaba en `.lean` y por eso no entra por ninguno de los dos lados.
H_FAIL=0
if [ ! -d sondeos ]; then
  echo "  ⚠️  no hay carpeta sondeos/ — nada que comprobar"
else
  H_FILES=$(mktemp); H_ROWS=$(mktemp)
  ls sondeos/*.lean 2>/dev/null | xargs -r -n1 basename | sort -u > "$H_FILES"
  grep -oE '^\| \*\*`[^`]+`\*\*' sondeos/README.md 2>/dev/null \
    | sed -E 's/^\| \*\*`(.*)`\*\*$/\1/' | grep '\.lean$' | sort -u > "$H_ROWS"
  H_NF=$(wc -l < "$H_FILES" | tr -d ' ')
  H_NR=$(wc -l < "$H_ROWS" | tr -d ' ')
  if [ "$H_NF" = "0" ]; then
    echo "  ❌ NO PUDE MEDIR: no se listó ni un .lean en sondeos/. ¿Se movió la carpeta?"
    H_FAIL=1
  fi
  H_SIN_FILA=$(comm -23 "$H_FILES" "$H_ROWS")
  H_SIN_FICH=$(comm -13 "$H_FILES" "$H_ROWS")
  # ⚠️ `printf '%s'` NO añade salto final: con EXACTAMENTE uno, `wc -l` cuenta 0 y el control
  # APRUEBA. Es el bug con el que nació `[COBERTURA]` (ADR-073) y que su propia prueba de rotura
  # cazó a la primera. Aquí va `printf '%s\n'` desde el minuto cero.
  H_A=$(printf '%s\n' "$H_SIN_FILA" | sed '/^$/d' | wc -l | tr -d ' ')
  H_B=$(printf '%s\n' "$H_SIN_FICH" | sed '/^$/d' | wc -l | tr -d ' ')
  if [ "$H_A" != "0" ]; then
    echo "  ❌ $H_A fichero(s) en sondeos/ SIN fila en el catálogo:"
    printf '%s\n' "$H_SIN_FILA" | sed '/^$/d' | head -20 | sed 's/^/      /'
    [ "$H_A" -gt 20 ] && echo "      … y $((H_A - 20)) más"
    echo "      🔑 Un sondeo sin proyectar se vuelve a construir. Añádelo a sondeos/README.md."
    H_FAIL=1
  fi
  if [ "$H_B" != "0" ]; then
    echo "  ❌ $H_B fila(s) del catálogo SIN fichero en sondeos/:"
    printf '%s\n' "$H_SIN_FICH" | sed '/^$/d' | head -20 | sed 's/^/      /'
    echo "      🔑 Una fila que nombra un fichero que no existe es una referencia FALSA."
    H_FAIL=1
  fi
  [ "$H_FAIL" = "0" ] && echo "  ✓ los $H_NF sondeos del disco y las $H_NR filas del catálogo CUADRAN"
  rm -f "$H_FILES" "$H_ROWS"
fi
[ "$H_FAIL" = "0" ] || FAIL=1

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
