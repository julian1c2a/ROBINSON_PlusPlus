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
TEOREMAS-E-HIPOTESIS.md
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
read -r -d '' B_DEUDA <<'EOF'
ax_notInAxC
ax_tc_liftfc
ax_tc_substfc
godelC'_fixedpoint
goedel_first_real
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
prf_isTsC
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
prf_tc_substfc
prf_wfAll_objList
repr_neg
EOF
B_FAIL=0
B_DECL=0
B_VISTOS=$(mktemp)
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
  EN_B=0
  while IFS= read -r t; do
    [ -n "$t" ] || continue
    [ "$t" = "$sym" ] && EN_B=1
  done <<< "$B_DEUDA"
  if [ -n "$bad" ]; then
    if [ "$EN_B" = "1" ]; then
      B_DECL=$((B_DECL + 1))
      echo "$sym" >> "$B_VISTOS"
    else
      echo "  ❌ \`$sym\` no existe en el árbol activo, se cita sin marcar como retirado,"
      echo "      y NO está en la tabla B_DEUDA de este script:"
      echo "$bad" | head -2 | sed 's/^/      /' | cut -c1-140
      B_FAIL=1
    fi
  elif [ "$EN_B" = "1" ]; then
    echo "  ❌ \`$sym\`: la deuda ESTÁ SALDADA — quítalo de la tabla B_DEUDA de este script."
    B_FAIL=1
  fi
done
rm -f "$DECLS"
# [B] NO marca FAIL: es un aviso. [A], [C] y [D] sí son objetivos y sí lo marcan.
# Razón: un control que grita lobo se acaba ignorando, y ése era justo el fallo que
# este script existe para evitar.
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
rm -f "$B_VISTOS"
echo "  deuda declarada: $B_DECL de 44 · sin declarar y sin saldar: rompen arriba"
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
