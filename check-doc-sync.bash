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
# ✏️ 2026-10-18 (ADR-166, T04): [B] es otro: toda cita con forma de identificador o de ruta (b-citas.awk), absuelta
# sólo por un marcador a 100 bytes (no por una fecha), con la deuda POR CITA en doc/control/b-deuda.tsv.
# ✏️ 2026-10-31 (T21, ADR-235): y también la absuelve, si la declara un sondeo, que la línea nombre ese sondeo (ya en
# ADR-166); desde ADR-167 (2026-10-19), el techo de la tabla es la de la base verificada (B_BASE_REF), y el marcador no
# cuenta negado, como sustantivo ni a través de otra cita o de un fin de oración.
# ✏️ 2026-10-18 (ADR-163, T15): y [L], el universo de los módulos (el cierre de imports del barril = el disco = git).
# ✏️ 2026-10-31 (T24, ADR-233): y [E], con DOS tablas de deuda —E_DEUDA, la de contenido (marca vieja), y
# E_DEUDA_FORMATO, la de formato (sin marca; vacía)— y un TECHO en la base verificada, como [A2] y [B].
# ✏️ 2026-11-02 (T32, T39, T37 y T10; ADR-237, 240, 241 y 243): y cinco bloques más, al final, los cinco ROJOS: [G] y
# [G.2] (portados de FOL: las deudas enunciadas con testigo y el censo de los marcadores de deuda), [P] (los footprints
# de la prosa contra las filas de check-footprints.bash), [R] (el registro de hallazgos) y [S] (las citas de sondeos
# del build: evidencia o procedencia). DEPENDENCIES.md lo genera gen-dependencies.py (T30, ADR-238); su --check, en la CI.
# ✏️ 2026-10-31 (T21, ADR-235): hoy rompen todos los bloques —[L], [EOL], [H] (el PATH higiénico), [A], [A2], [E],
# [B], [I], [N], [C], [D], [F], [H] (el catálogo de sondeos/), [M] y [T]— y la VERDAD DEL CÓDIGO si no puede medir;
# ninguno es sólo aviso. La nota del 2026-10-14 (ADR-135) decía «hoy rompen [A], [B], [C], [D], [E], [F], [H], [M] y
# [T]; sólo [A2] es aviso»: [A2] rompe desde ADR-169 (2026-10-19). Lo que sigue es la cabecera del 2026-08-23, cuando
# [B] era aviso (lo fue hasta ADR-084):
# [A], [C] y [D] son OBJETIVOS y rompen el check. [B] es un AVISO que pide juicio:
# hay menciones legítimas de símbolos inexistentes (históricas, planificadas, descartadas).
#
# Uso:
#   bash check-doc-sync.bash            # comprobación completa
#   bash check-doc-sync.bash --quick    # sin `lake build`: no mide los jobs ([A] y [A2] no los comparan, y --a2-deuda
#                                       # se niega, en rojo); [B] sigue pidiendo `lake` y el build hecho (✏️ 2026-10-31,
#                                       # T21, ADR-235: decía «usa el conteo de módulos»; [B] pide `lake` desde ADR-166)
#   bash check-doc-sync.bash --fix-hint # además, si sale rojo, dos sed genéricos para revisar a mano: los jobs (si se
#                                       # midieron) y los módulos activos, sobre *.md doc/*.md (también las líneas
#                                       # de historia)
#   bash check-doc-sync.bash --b-deuda  # además, baja doc/control/b-deuda.tsv a la deuda de hoy, si nada sube (ADR-166)
#   bash check-doc-sync.bash --b-deuda-inicial  # crea esa tabla, sólo si no existe (se hizo una vez, ADR-166)
#   bash check-doc-sync.bash --b-deuda-rehacer  # la rehace, sólo en el commit que cambia el núcleo de [B] (y sube, como
#                                               # mucho, lo que el núcleo nuevo ve de más que el viejo)
#   bash check-doc-sync.bash --a2-deuda  # además, baja doc/control/a2-deuda.tsv (las cifras viejas del cuerpo, [A2];
#                                        # ADR-169), si nada sube
#   bash check-doc-sync.bash --a2-deuda-inicial  # crea esa tabla, sólo si no existe (se hizo una vez, ADR-169)
#   bash check-doc-sync.bash -h, --help          # esta ayuda (los comentarios del principio)
# Variables: M_DOC=fichero y T_DOC=fichero, modos de prueba de [M] y [T] (dicen qué fichero miran y nunca dan verde);
#   B_BASE_REF=ref, la base verificada del techo de [A2], [E] y [B] (por omisión refs/remotes/origin/master).
#
# Salida: 0 si todo cuadra (y con -h); 1 si hay desincronización o algo no se pudo medir (siempre, con M_DOC o T_DOC);
# 2 con una opción desconocida.

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
B_DEUDA_MODO=0
A2_DEUDA_MODO=0
for a in "$@"; do
  case "$a" in
    --quick)     QUICK=1 ;;
    --fix-hint)  HINT=1 ;;
    --b-deuda)   B_DEUDA_MODO=1 ;;
    --b-deuda-inicial) B_DEUDA_MODO=2 ;;
    --b-deuda-rehacer) B_DEUDA_MODO=3 ;;
    --a2-deuda)  A2_DEUDA_MODO=1 ;;
    --a2-deuda-inicial) A2_DEUDA_MODO=2 ;;
    -h|--help)   awk 'NR > 1 && /^#/ { print; next } NR > 1 { exit }' "$0"; exit 0 ;;
    *) echo "opción desconocida: $a" >&2; exit 2 ;;
  esac
done

# ─── 1. VERDAD DEL CÓDIGO ────────────────────────────────────────────────────
# ✏️ 2026-10-18 (T15, ADR-163): los módulos se cuentan sobre el CIERRE de imports del barril (`cierre-imports.bash`),
# el mismo conjunto que [L] compara con el disco y con git. Antes eran `ls` por capas, y `Minimal/**/*.lean` sin
# `globstar` es UN nivel: un subdirectorio nuevo no lo contaba nadie. Un módulo es un fichero de una capa
# (`ROBINSON_PlusPlus/<capa>/…`); los dos barriles (`ROBINSON_PlusPlus.lean` y `ROBINSON_PlusPlus/Meta.lean`) no.
CIERRE=$(bash cierre-imports.bash 2>/dev/null)
CIERRE_RC=$?
cuenta_cierre() { printf '%s\n' "$CIERRE" | grep -cE "$1" || true; }
MIN=$(cuenta_cierre '^ROBINSON_PlusPlus/Minimal/')
META=$(cuenta_cierre '^ROBINSON_PlusPlus/Meta/')
FULL=$(cuenta_cierre '^ROBINSON_PlusPlus/Full/')
ACTIVE=$(cuenta_cierre '^ROBINSON_PlusPlus/[^/]*/')
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
# ⛔ Y desde la tercera revisión (2026-10-04): (1) se cuenta el TOKEN `axiom` en todo el código
# despojado, no sólo a principio de línea —`open Nat in axiom x`, `def t := 0 axiom x` o el nombre en la
# línea siguiente son declaraciones que el patrón anclado no veía; en código, `axiom` sólo declara—;
# (2) el fixture EJERCE el despojador: señuelos que empiezan línea DENTRO de un docstring, de una
# cadena de dos líneas y de un comentario anidado (el patrón anclado de antes los rechazaba aunque no
# se despojara nada), y `axiom` reales detrás de una comilla escapada, de `'"'`, de una interpolación y
# de una cadena en bruto: si el despojador falla en cualquiera, la cifra no sale.
# (3) El alcance incluye el barrel raíz `ROBINSON_PlusPlus.lean`, que el build compila y se edita a mano.
# (cuarta revisión: la frontera excluye la comilla invertida —`` `axiom `` es un literal de nombre— y los
#  bytes de continuación UTF-8 —`αaxiom` es UN identificador—, y tras `axiom` vale también `«`; el fixture
#  tiene hoy NUEVE `axiom` reales, y si no salen 9 no se mide)
AX_TOK="(^|[^A-Za-z0-9_'.«\`"$'\x80-\xbf'"])axiom([[:space:]«]|$)"
cuenta_axiomas () {   # $@ = caminos; imprime la cifra, o nada y estado 2 si no ha podido medir
  local p n
  for p in "$@"; do [ -e "$p" ] || return 2; done
  [ -n "$(find "$@" -name '*.lean' ! -path '*/.lake/*' -print -quit)" ] || return 2
  n=$(find "$@" -name '*.lean' ! -path '*/.lake/*' -print0 \
        | xargs -0 env LC_ALL=C awk -f strip-lean.awk \
        | { LC_ALL=C grep -oE "$AX_TOK" || [ $? -eq 1 ]; } | wc -l) || return 2
  printf '%s\n' "$n" | tr -d ' '
}
AX_FIX=$(mktemp -d)
cat > "$AX_FIX/Fixture.lean" <<'EOF'
/-- un docstring
axiom senuelo1 : True
-/
axiom real1 : True
-- axiom senuelo2 : True
  @[simp] private axiom real2 : True
def s := "una cadena de dos líneas
axiom senuelo3 : True"
/-- doc -/ axiom real3 : True
/- /- anidado -/
axiom senuelo4 : True -/
def q := "comilla: \"" axiom real4 : True
def c := '"' axiom real5 : True
def i := s!"{1}" axiom real6 : True
def r := r#"x"# axiom real7 : True
open Nat in axiom real8 : True
axiom«real9» : True
theorem u : True := trivial -- axiom senuelo5
def k := `axiom
def αaxiom : Nat := 1
EOF
AXIOMS=""
if [ "$(cuenta_axiomas "$AX_FIX" || true)" = "9" ]; then
  AXIOMS=$(cuenta_axiomas ROBINSON_PlusPlus/ ROBINSON_PlusPlus.lean || true)
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
# ⛔ 2026-10-04 (tercera revisión): se leen las LÍNEAS DE RESUMEN, enteras. check-sorry reimprime cada
# línea fuente con `sorry`, y una que contuviera «No sorry found» hacía SORRY=0 con un `sorry` real.
if printf '%s\n' "$SORRY_OUT" | LC_ALL=C grep -qxF '✅ No sorry found.'; then
  SORRY=0
elif printf '%s\n' "$SORRY_OUT" | LC_ALL=C grep -qE '^⚠️  Total: [0-9]+ sorry in '; then
  SORRY=$(printf '%s\n' "$SORRY_OUT" | LC_ALL=C grep -oE '^⚠️  Total: [0-9]+' | grep -oE '[0-9]+$' | head -1)
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
# ✏️ 2026-10-31 (T21, ADR-235): decía «o usa --quick para decirlo a propósito»; desde ADR-166, [B] pide lake también con --quick.
[ "$LAKE_MISSING" = "1" ] && echo "                     Lánzalo desde PowerShell: --quick no basta (no mide los jobs, y [B] sigue pidiendo lake)."
[ "$LAKE_MISSING" = "2" ] && echo "  ⚠️  build jobs    : SIN MEDIR — 'lake build' no dijo 'Build completed successfully'."
[ "$SORRY_MISSING" = "1" ] && echo "  ⚠️  sorry         : SIN MEDIR — check-sorry.bash no dijo ni 'No sorry found' ni 'Total: N sorry'."
[ "$AXIOMS_MISSING" = "1" ] && echo "  ⚠️  axiom de Lean : SIN MEDIR — el autotest de cuenta_axiomas no dio 9 (¿strip-lean.awk, LC_ALL?)."
echo

# Documentos AUTORITATIVOS: los que describen el ESTADO ACTUAL y por tanto deben cuadrar.
# Quedan fuera, y con razón, los de diario, diseño e historia (CHANGELOG, GODEL-*-DESIGN,
# PLAN-*, THOUGHTS, MINIMAL-AXIOMS…): sus cifras y símbolos son históricos POR DISEÑO.
AUTHORITATIVE="REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md AXIOMS.md GODEL-STATUS.md NEXT-STEPS.md"
# (2026-10-14, ADR-135; T09: TEOREMAS-E-HIPOTESIS.md entra en el universo: es normativo y nadie lo miraba)
AUTHORITATIVE="$AUTHORITATIVE TEOREMAS-E-HIPOTESIS.md"
# (2026-10-21, ADR-185; T28: PLAN-PRUEBAS.md entra también: dice qué comprueba cada control, y es normativo)
AUTHORITATIVE="$AUTHORITATIVE PLAN-PRUEBAS.md"
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
if [ "$QUICK" != "1" ] && [ "$LAKE_MISSING" != "0" ]; then
  FAIL=1
fi
# Los censos de `axiom` y de `sorry` no dependen de `lake`: no medirlos es rojo también con `--quick`.
# (El de `sorry`, desde la tercera revisión: con `--quick`, un check-sorry que no podía medir dejaba
# comparar el «0 sorry» de los documentos con un 0 por defecto, y daba verde.)
[ "$AXIOMS_MISSING" != "0" ] && FAIL=1
[ "$SORRY_MISSING" != "0" ] && FAIL=1

# ─── [L] LIBRERÍA = CIERRE DE IMPORTS ────────────────────────────────────────
# ⭐ AÑADIDO el 2026-10-18 (T15, ADR-163). Con `globs := #[.andSubmodules `ROBINSON_PlusPlus]` (lakefile.lean),
# Lake compila TODO `.lean` de `ROBINSON_PlusPlus/` y el barril, lo importe alguien o no. Tres conjuntos tienen que
# ser EL MISMO: (1) el cierre de imports del barril (`cierre-imports.bash`), que es lo que cuentan [A] y recorre [C];
# (2) lo que compilan los globs (el disco); (3) lo que ve la CI (`git ls-files`). Rompe en LOS DOS SENTIDOS: un
# fichero fuera del cierre (suelto: compila, pero no lo cuenta nadie) es rojo, y uno del cierre sin `git add`
# también (aquí compila y en la CI no existe). Y un módulo fuera de las tres capas, que [A] no contaría.
# 🔑 Probado con el fallo puesto: el autotest de `cierre-imports.bash` (cuatro mutantes lo rompen) y un fichero
# suelto de verdad en `ROBINSON_PlusPlus/Meta/` (ADR-163 §2).
echo "════ [L] LIBRERÍA = CIERRE DE IMPORTS — ROJO, y rompe en LOS DOS SENTIDOS ════"
L_FAIL=0
sin_vacias() { grep -v '^$' || true; }
if ! bash cierre-imports.bash --autotest; then
  echo "  ❌ SIN MEDIR: el autotest de cierre-imports.bash falla (¿strip-lean.awk? ¿LC_ALL? ¿bash?)."
  L_FAIL=1
elif [ "$CIERRE_RC" != "0" ] || [ -z "$CIERRE" ]; then
  echo "  ❌ el cierre de imports no sale (código $CIERRE_RC): bash cierre-imports.bash"
  L_FAIL=1
elif ! git rev-parse --git-dir > /dev/null 2>&1; then
  echo "  ❌ SIN MEDIR: esto no es un repositorio de git, y sin \`git ls-files\` no sé qué ve la CI."
  L_FAIL=1
else
  L_GIT=$(git ls-files -- 'ROBINSON_PlusPlus.lean' 'ROBINSON_PlusPlus/*.lean' | sin_vacias | LC_ALL=C sort -u)
  L_DISCO=$( { [ -f ROBINSON_PlusPlus.lean ] && echo ROBINSON_PlusPlus.lean; find ROBINSON_PlusPlus -name '*.lean'; } \
    | sin_vacias | LC_ALL=C sort -u)
  L_SUELTOS=$(printf '%s\n%s\n' "$L_GIT" "$L_DISCO" | sin_vacias | LC_ALL=C sort -u \
    | LC_ALL=C comm -23 - <(printf '%s\n' "$CIERRE"))
  L_SINGIT=$(printf '%s\n' "$CIERRE" | LC_ALL=C comm -23 - <(printf '%s\n' "$L_GIT"))
  L_CAPAS=$((MIN + META + FULL))
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    echo "  ✗ $f está en el disco o en git y NO en el cierre de imports del barril: los globs lo compilan, pero"
    echo "      ningún \`import\` lo alcanza. Impórtalo desde su barril, o sácalo de ROBINSON_PlusPlus/ (¿sondeos/?)."
    L_FAIL=1
  done <<< "$L_SUELTOS"
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    echo "  ✗ $f está en el cierre y NO en git: aquí compila, y la CI no lo tiene (git add)."
    L_FAIL=1
  done <<< "$L_SINGIT"
  if [ "$L_CAPAS" != "$ACTIVE" ]; then
    echo "  ✗ hay módulos del cierre fuera de Minimal/, Meta/ y Full/ ($ACTIVE en capas, $L_CAPAS en las tres): [A] no"
    echo "      los contaría por capa. Añade la capa a la cuenta de arriba."
    L_FAIL=1
  fi
  # El código de `cierre-imports.bash` es el de FOL salvo sus raíces (`RAICES`, `PREFIJOS`): si se separan, rojo.
  if [ ! -f ../FOL/cierre-imports.bash ]; then
    echo "  ❌ falta ../FOL/cierre-imports.bash: no puedo comprobar que las dos copias tengan el mismo código."
    L_FAIL=1
  elif ! cmp -s <(grep -vE '^#|^(RAICES|PREFIJOS)=' cierre-imports.bash | tr -d '\r') \
                <(grep -vE '^#|^(RAICES|PREFIJOS)=' ../FOL/cierre-imports.bash | tr -d '\r'); then
    echo "  ❌ cierre-imports.bash y ../FOL/cierre-imports.bash ya no tienen el mismo código: unifícalos."
    L_FAIL=1
  fi
  L_TOTAL=$(printf '%s\n' "$CIERRE" | grep -c .)
  [ "$L_FAIL" = "0" ] && echo "  ✓ los $L_TOTAL ficheros del cierre de imports del barril son los del disco y los de git" \
    "($((L_TOTAL - ACTIVE)) barriles y $ACTIVE módulos); el autotest del cierre pasa"
fi
[ "$L_FAIL" = "0" ] || FAIL=1

# ─── [EOL] FINALES DE LÍNEA: ningún blob con CRLF en el índice — ROJO ──────────
# ⭐ AÑADIDO el 2026-10-28 (T43, ADR-200 de RPP). Con `core.autocrlf=true` en local y LF en la CI, una medida anclada en
# «$» da distinto en los dos sitios. El índice de RPP ya era todo LF; el de FOL guardaba 45 blobs con CRLF (nueve `.lean`
# activos y treinta de la cuarentena), y se renormalizaron. Desde hoy, ninguno: lo mira `git ls-files --eol` (la
# columna del ÍNDICE, no la del árbol de trabajo, que en Windows es CRLF a propósito).
echo
echo "════ [EOL] FINALES DE LÍNEA EN EL ÍNDICE — ROJO ════"
if git rev-parse --git-dir > /dev/null 2>&1; then
  EOL_MAL=$(git ls-files --eol | awk '$1 == "i/crlf" || $1 == "i/mixed" { print $NF }')
  if [ -n "$EOL_MAL" ]; then
    echo "  ✗ blobs con CRLF en el índice ($(printf '%s\n' "$EOL_MAL" | grep -c .)): renormaliza con «git add --renormalize .»"
    printf '%s\n' "$EOL_MAL" | head -10 | sed 's/^/      /'
    FAIL=1
  else
    echo "  ✓ ningún blob con CRLF en el índice ($(git ls-files --eol | grep -c '^i/lf') en LF)"
  fi
else
  echo "  ❌ SIN MEDIR: esto no es un repositorio de git, y sin el índice no sé qué ve la CI."
  FAIL=1
fi

# ─── [H] PATH HIGIÉNICO EN TODO SCRIPT — ROJO ──────────────────────────────────
# ⭐ AÑADIDO el 2026-10-28 (T52, ADR-201 de RPP). Lanzado desde una consola de Windows, `bash` hereda su PATH, y `head`,
# `grep`, `sort` o `find` pueden resolver a otro programa (le pasó a este script el 2026-09-09: cuatro controles vacíos y
# verde). Todo `.bash` versionado antepone el /usr/bin de MSYS2 (`export PATH="/usr/bin…`) antes de su código. Salvo
# `b-control.bash`, que no se ejecuta (lo carga este script con `source` y hereda su PATH), y lo de `doc/registro/`,
# que es registro tal cual.
echo
echo "════ [H] PATH HIGIÉNICO EN TODO SCRIPT — ROJO ════"
H_TODOS=$(git ls-files '*.bash' | grep -v '^doc/registro/' | grep -vx 'b-control.bash')
H_SIN=$(printf '%s\n' "$H_TODOS" | while IFS= read -r f; do
  [ -n "$f" ] || continue
  grep -q '^[^#]*export PATH="/usr/bin' "$f" || echo "$f"; done)
if [ -z "$H_TODOS" ]; then
  echo "  ❌ SIN MEDIR: git no lista ningún .bash."
  FAIL=1
elif [ -n "$H_SIN" ]; then
  echo "  ✗ scripts sin el PATH higiénico:"
  printf '%s\n' "$H_SIN" | sed 's/^/      /'
  FAIL=1
else
  echo "  ✓ los $(printf '%s\n' "$H_TODOS" | grep -c .) scripts lo llevan (b-control.bash se carga con source)"
fi
echo

# ─── 2. CIFRAS OBSOLETAS ─────────────────────────────────────────────────────
# CHANGELOG.md se excluye: es un diario, sus cifras son históricas por diseño.
# ⛔ 2026-10-19 (T04b, ADR-169): REHECHO. Lo que había (un `grep -v` sobre la línea entera) tenía tres agujeros
# medidos: la FECHA eximía la línea (y una fecha no dice que la cifra sea de ese día); la NEGRITA cegaba los patrones
# («**1** axiom de Lean» no casaba con nada); y la cifra de los SONDEOS se calculaba y no se comparaba. La revisión
# adversarial de ADR-169 encontró más: los marcadores casaban DENTRO de una palabra («era » en «fuera», «antes» en
# «constantes»: un 13 % de las líneas, exentas, y entre ellas CURRENT-STATUS-PROJECT.md:48, «**1** `axiom` de Lean»
# con 0), y «→», «~», un rango o una cita «…» con un dígito eximían la línea entera, estuvieran donde estuvieran.
# Ahora lo hace un awk (A_AWK, el mismo en FOL), en la configuración regional C, línea a línea:
#   · lo citado entre «…» y lo tachado (~~…~~) se quita: lo dice otro, o está retirado; el resto de la línea cuenta;
#   · un MARCADOR de historia, como PALABRA entera, exime la línea: histórico, previo, antes, era, fueron, entonces,
#     «ya no», «en su momento», ejemplo, «p. ej», umbral (y en [A2], retirado);
#   · cada aparición de cada patrón se mira por separado; la exime sólo lo que la toca: «~» justo delante (una
#     aproximación), un rango corto que acaba en ella («40-50»), o una flecha justo detrás (es la cifra VIEJA de un
#     «131 jobs → 133 jobs»);
#   · los patrones admiten la negrita, y el número es el primero de lo que casa.
# Los documentos tienen que ser UTF-8 válido y sin NUL: un byte malo escondía la línea a grep, y un NUL el resto.
echo "════ [A] CIFRAS ════"
A_FAIL=0
A_DIR=$(mktemp -d)
A_DOCS=""
A_MAL=""; A_SAL=""; A2_SAL=""
for d in $DOCS; do
  [ -e "$d" ] || continue
  A_DOCS="$A_DOCS $d"
  if ! iconv -f UTF-8 -t UTF-8 "$d" > /dev/null 2>&1 || ! tr -d '\000' < "$d" | cmp -s - "$d"; then A_MAL="$A_MAL $d"; fi
done
# las cifras: etiqueta<TAB>patrón (ERE en minúsculas; la cifra es el primer número de lo que casa)<TAB>valor de hoy
# (vacío: no se midió, y la etiqueta no se compara)
NB='([*][*])?'   # la negrita que puede cerrar la cifra: `**133** jobs`
{
  printf 'jobs\t%s\t%s\n' "[0-9]+$NB jobs" "$JOBS"
  printf 'módulos activos\t%s\t%s\n' "[0-9]+$NB módulos activos" "$ACTIVE"
  printf 'conteo de Meta\t%s\t%s\n' "meta $NB([0-9]+$NB [+]|[0-9]+$NB[)])" "$META"
  printf 'cuarentena\t%s\t%s\n' "[0-9]+$NB (módulos )?en \`cuarentena/\`" "$QUAR"
  printf 'axiom de Lean\t%s\t%s\n' "[0-9]+$NB \`?axiom\`?$NB (de lean|en el build)" "$AXIOMS"
  printf 'sorry\t%s\t%s\n' "[0-9]+$NB \`?sorrys?" "$SORRY"
  printf 'sondeos\t%s\t%s\n' "[0-9]+$NB \`sondeos/\`" "$SOND"
} > "$A_DIR/patrones"
# los marcadores (palabra entera; la línea va en minúsculas y con un espacio a cada lado)
A_MARC='[^a-z0-9_](hist(o|ó)ric(o|a|os|as)|previ(o|a|os|as)|antes|era|eran|fueron|entonces|ya no|en su momento|ejemplos?|p[.] ej|umbral)[^a-z0-9_]'
A_MARC2='[^a-z0-9_](hist(o|ó)ric(o|a|os|as)|previ(o|a|os|as)|antes|era|eran|fueron|entonces|ya no|en su momento|ejemplos?|p[.] ej|umbral|retirad(o|a|os|as))[^a-z0-9_]'
# (sin intervalos `{m,n}` ni `^` dentro de una alternativa: la CI usa mawk)
A_AWK='
function bajar(s) { s = tolower(s); gsub(/Á/, "á", s); gsub(/É/, "é", s); gsub(/Í/, "í", s); gsub(/Ó/, "ó", s)
  gsub(/Ú/, "ú", s); gsub(/Ñ/, "ñ", s); gsub(/Ö/, "ö", s); return s }
function fuera(s, a, b,   p, r, q) {
  while ((p = index(s, a)) > 0) { r = substr(s, p + length(a)); q = index(r, b); if (!q) break
    s = substr(s, 1, p - 1) " " substr(r, q + length(b)) }
  return s }
BEGIN { marc = ENVIRON["A_MARC_USO"] }
FILENAME == ARGV[1] { split($0, z, "\t"); np++; ETQ[np] = z[1]; PAT[np] = z[2]; BUENO[np] = z[3]; next }
FNR < desde || FNR > hasta { next }
{ t = " " bajar(fuera(fuera($0, "«", "»"), "~~", "~~")) " "
  if (t ~ marc) next
  for (i = 1; i <= np; i++) {
    if (BUENO[i] == "") continue
    r = t
    while (match(r, PAT[i])) {
      m = RSTART; L = RLENGTH; seg = substr(r, m, L)
      match(seg, /[0-9]+/); num = substr(seg, RSTART, RLENGTH); p0 = m + RSTART - 1
      antes = " " substr(r, 1, p0 - 1); despues = substr(r, m + L)
      exento = (antes ~ /~ *$/) || (despues ~ /^ *(→|->)/) || (length(num) <= 3 && antes ~ /[^0-9-][0-9][0-9]?[0-9]?-$/)
      if (!exento) { visto[ETQ[i]] = 1; if (num + 0 != BUENO[i] + 0) print ETQ[i] "\t" FILENAME "\t" FNR "\t" num "\t" substr($0, 1, 150) }
      r = substr(r, m + L)
    }
  }
}
END { for (e in visto) print e > VISTO }'
# autotest: cada exención y cada vía de las revisiones, con salida exacta
printf 'jobs\t%s\t133\nconteo de Meta\t%s\t112\n' "[0-9]+$NB jobs" "meta $NB([0-9]+$NB [+]|[0-9]+$NB[)])" > "$A_DIR/pat-auto"
printf '%s\n' 'Hay **120** jobs.' 'Fuera de esto, 121 jobs.' 'Histórico: 122 jobs.' 'Unos ~123 jobs.' 'De 40-124 jobs.' \
  'El 2026-10-19: 125 jobs.' 'Pasó de 126 jobs → 133 jobs.' 'Se dijo «127 jobs».' '~~128 jobs~~ y 133 jobs.' \
  'Antes, 129 jobs.' 'En la primera pasada, 130 jobs.' 'Constantes: 131 jobs.' 'HISTÓRICO: 132 jobs.' 'Meta **5** + 2.' \
  'Son 134 jobs (ver «ADR-121»).' > "$A_DIR/doc-auto.md"
A_AUTO=$(cd "$A_DIR" && LC_ALL=C A_MARC_USO="$A_MARC" awk -v desde=1 -v hasta=100 -v VISTO=/dev/null "$A_AWK" pat-auto doc-auto.md \
  | LC_ALL=C awk -F'\t' '{ printf "%s:%s:%s;", $1, $3, $4 }')
A_AUTO_OK='jobs:1:120;jobs:2:121;jobs:6:125;jobs:11:130;jobs:12:131;conteo de Meta:14:5;jobs:15:134;'
if [ -n "$A_MAL" ]; then
  echo "  ❌ NO PUDE MEDIR [A] ni [A2]: no son UTF-8 válido o llevan NUL:$A_MAL"; A_FAIL=1
elif [ "$A_AUTO" != "$A_AUTO_OK" ]; then
  echo "  ❌ NO PUDE MEDIR [A] ni [A2]: el autotest no da lo esperado ($A_AUTO_OK), da: $A_AUTO"; A_FAIL=1
else
  # ALCANCE: la REGIÓN DE CABECERA (las primeras 100 líneas) de cada documento autoritativo: el banner y las tablas
  # resumen, lo que AFIRMA el estado actual. (✏️ ADR-169: los banners apilados se fueron a doc/historia/BANNERS.md con
  # ADR-142, T33: la cabecera ya no se los come.) El cuerpo lo mira [A2].
  if ! A_SAL=$(LC_ALL=C A_MARC_USO="$A_MARC" awk -v desde=1 -v hasta=100 -v VISTO="$A_DIR/visto" "$A_AWK" "$A_DIR/patrones" $A_DOCS); then
    echo "  ❌ NO PUDE MEDIR [A]: el awk falló."; A_FAIL=1
  fi
  printf '%s\n' "$A_SAL" | while IFS=$'\t' read -r e d l n texto; do
    [ -n "$e" ] || continue
    echo "  ✗ $e: dice $n, real $(LC_ALL=C awk -F'\t' -v e="$e" '$1 == e { print $3 }' "$A_DIR/patrones")"
    echo "      $d:$l: $texto"
  done
  [ -n "$A_SAL" ] && A_FAIL=1
  # ⚠️ Un patrón sin ninguna aparición NO está comprobando nada, y da verde. Si sale, o el fraseo del documento cambió,
  # o el patrón está mal: en los dos casos hay que tocar algo.
  # ✏️ 2026-10-30 (T45, ADR-223): ROJO. Era un aviso, y un aviso no para nada (la auditoría, T45); visto fallar con un
  # patrón que no casa con ningún documento.
  A_VACIOS=$(LC_ALL=C awk -F'\t' '$3 != "" { print $1 }' "$A_DIR/patrones" | while IFS= read -r e; do
    grep -qxF "$e" "$A_DIR/visto" 2>/dev/null || echo "$e"
  done)
  if [ -n "$A_VACIOS" ]; then
    printf '%s\n' "$A_VACIOS" | sed 's/$/: la frase no aparece en ningún doc autoritativo — control VACÍO/; s/^/  ❌ /'
    A_FAIL=1
  fi
fi
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
# ⛔ 2026-10-19 (T04b, ADR-169): deja de ser un AVISO. Las cifras viejas del cuerpo de hoy se congelan en una tabla,
# `doc/control/a2-deuda.tsv` («etiqueta<TAB>documento<TAB>cifra<TAB>líneas»), como la deuda de [B]: una línea de más es
# rojo; una de menos, también, hasta `bash check-doc-sync.bash --a2-deuda`; y la tabla no sube sobre la de la base
# verificada (la misma que la de [B]). La tabla tiene que EXISTIR siempre (sin deuda, sólo con su cabecera): si la base
# verificada ya la conocía (su check-doc-sync.bash la nombra) y no la tiene, el techo es CERO. La tabla se valida: cuatro
# campos, la cifra y las líneas numéricas, ninguna clave repetida. Una etiqueta que no se midió (los jobs con --quick)
# no se compara, y entonces la tabla no se puede bajar. El mismo awk que [A], sobre las líneas 101 en adelante.
# DECISIONS.md no entra: un ADR dice las cifras de su día, y su fecha es su ámbito (M-13), como en CHANGELOG.
# ⚠️ Lo que NO ve, por diseño (ADR-169 §8): cambiar una línea vieja por otra con la misma etiqueta, documento y cifra
# deja el recuento igual; y un documento renombrado con deuda es rojo hasta que se edite la tabla a mano.
# 🔑 Cuando una cifra cambia (el build pasa de 133 a 134 jobs), las líneas del cuerpo que la decían se corrigen o se
# marcan como historia: eso es lo que este control pide.
echo ""
echo "════ [A2] CIFRAS EN EL CUERPO — ROJO, con trinquete por línea (T04b, ADR-169) ════"
A2_TABLA=doc/control/a2-deuda.tsv
A2_FAIL=0
A2_DOCS=""
for d in $A_DOCS; do [ "$d" = DECISIONS.md ] || A2_DOCS="$A2_DOCS $d"; done
# las etiquetas medidas hoy (las otras no se comparan)
A2_MED=$(LC_ALL=C awk -F'\t' '$3 != "" { print $1 }' "$A_DIR/patrones")
A2_NOMED=$(LC_ALL=C awk -F'\t' '$3 == "" { printf "%s«%s»", s, $1; s = ", " }' "$A_DIR/patrones")
a2_medidas() { LC_ALL=C awk -F'\t' 'FILENAME == ARGV[1] { m[$0] = 1; next } ($1 in m)' <(printf '%s\n' "$A2_MED") -; }
# una tabla, normalizada (sin BOM, sin CR, sin comentarios ni líneas vacías, ordenada) y sus errores de forma
a2_norm() { sed '1s/^\xEF\xBB\xBF//' | tr -d '\r' | grep -v '^#' | grep . | LC_ALL=C sort; }
a2_valida() { LC_ALL=C awk -F'\t' 'NF != 4 || $3 !~ /^[0-9]+$/ || $4 !~ /^[1-9][0-9]*$/ { print "      mal formada: " $0; next }
  ($1 "\t" $2 "\t" $3) in v { print "      repetida: " $0; next } { v[$1 "\t" $2 "\t" $3] = 1 }'; }
A2_HOY=""
if [ -z "$A_MAL" ] && [ "$A_AUTO" = "$A_AUTO_OK" ]; then
  if ! A2_SAL=$(LC_ALL=C A_MARC_USO="$A_MARC2" awk -v desde=101 -v hasta=999999999 -v VISTO=/dev/null "$A_AWK" "$A_DIR/patrones" $A2_DOCS); then
    echo "  ❌ NO PUDE MEDIR [A2]: el awk falló."; A2_FAIL=1
  fi
  A2_HOY=$(printf '%s\n' "$A2_SAL" | LC_ALL=C awk -F'\t' 'NF >= 4 { print $1 "\t" $2 "\t" $4 }' | LC_ALL=C sort | uniq -c \
    | LC_ALL=C awk '{ n = $1; sub(/^ *[0-9]+ /, ""); print $0 "\t" n }' | LC_ALL=C sort)
else
  echo "  ❌ NO PUDE MEDIR [A2]: ver [A]."; A2_FAIL=1
fi
A2_CAB="# $A2_TABLA — las cifras VIEJAS del cuerpo de los documentos autoritativos ([A2] de check-doc-sync.bash; ADR-169).
# Una línea por (etiqueta, documento, cifra que dice): cuántas líneas la dicen. Una de más es rojo; una de menos,
# también, hasta bajar la tabla: bash check-doc-sync.bash --a2-deuda. El techo es esta tabla en la base verificada.
# Se arregla en el DOCUMENTO: la cifra, o un marcador de historia («histórico», «previo», «entonces»…) en su línea.
# La tabla tiene que existir siempre: sin deuda, sólo con esta cabecera.
# etiqueta	documento	cifra	líneas"
if [ "$A2_DEUDA_MODO" != "0" ] && [ -n "$A2_NOMED" ]; then
  echo "  ❌ --a2-deuda: sin medir $A2_NOMED (¿--quick?): la tabla no se toca."; A2_FAIL=1; A2_DEUDA_MODO=0
fi
if [ "$A2_DEUDA_MODO" = "2" ] && [ "$A2_FAIL" = "0" ]; then
  if [ -e "$A2_TABLA" ]; then echo "  ❌ --a2-deuda-inicial: $A2_TABLA ya existe; la tabla sólo baja (--a2-deuda)."; A2_FAIL=1
  else { printf '%s\n' "$A2_CAB"; printf '%s\n' "$A2_HOY" | grep .; } > "$A2_TABLA"; echo "  ✓ la tabla, creada: $(grep -vc '^#' "$A2_TABLA") entradas"; fi
fi
A2_TAB=""
if [ ! -e "$A2_TABLA" ]; then
  echo "  ❌ $A2_TABLA no existe: tiene que estar siempre (sin deuda, sólo con la cabecera)."; A2_FAIL=1
else
  A2_TAB=$(a2_norm < "$A2_TABLA")
  A2_MALF=$(printf '%s\n' "$A2_TAB" | grep . | a2_valida)
  if [ -n "$A2_MALF" ]; then echo "  ❌ $A2_TABLA no tiene la forma de la tabla:"; printf '%s\n' "$A2_MALF" | head -5; A2_FAIL=1; fi
fi
if [ "$A2_DEUDA_MODO" = "1" ] && [ "$A2_FAIL" = "0" ]; then
  A2_SUBEN=$(LC_ALL=C awk -F'\t' 'FILENAME == ARGV[1] { t[$1 "\t" $2 "\t" $3] = $4; next }
    $0 != "" { k = $1 "\t" $2 "\t" $3; if (!(k in t) || $4 + 0 > t[k] + 0) print }' <(printf '%s\n' "$A2_TAB") <(printf '%s\n' "$A2_HOY"))
  if [ -n "$A2_SUBEN" ]; then
    echo "  ❌ --a2-deuda NO baja la tabla: estas entradas suben o son nuevas (corrige la cifra o márcala como historia):"
    printf '%s\n' "$A2_SUBEN" | head -10 | sed 's/^/      /'; A2_FAIL=1
  else
    { printf '%s\n' "$A2_CAB"; printf '%s\n' "$A2_HOY" | grep .; } > "$A2_TABLA"
    A2_TAB=$(a2_norm < "$A2_TABLA")
    echo "  ✓ --a2-deuda: la tabla baja a $(printf '%s\n' "$A2_TAB" | grep -c .) entradas"
  fi
fi
# hoy frente a la tabla, sólo en las etiquetas medidas
A2_DIF=$(LC_ALL=C awk -F'\t' 'FILENAME == ARGV[1] { if ($0 != "") t[$1 "\t" $2 "\t" $3] = $4; next }
    $0 != "" { k = $1 "\t" $2 "\t" $3; h[k] = 1; if (!(k in t) || $4 + 0 > t[k] + 0) print "S\t" $0 "\t" (t[k] + 0)
      else if ($4 + 0 < t[k] + 0) print "B\t" $0 "\t" t[k] }
    END { for (k in t) if (!(k in h)) print "B\t" k "\t0\t" t[k] }' <(printf '%s\n' "$A2_TAB" | a2_medidas) <(printf '%s\n' "$A2_HOY"))
printf '%s\n' "$A2_DIF" | LC_ALL=C awk -F'\t' '$1 == "S"' | while IFS=$'\t' read -r tipo e d c n m; do
  echo "  ❌ $e: «$c» en $d, $n línea(s), y la tabla dice $m — una cifra vieja NUEVA en el cuerpo:"
  printf '%s\n' "$A2_SAL" | LC_ALL=C awk -F'\t' -v e="$e" -v d="$d" -v c="$c" '$1 == e && $2 == d && $4 == c { print "      " $2 ":" $3 ": " $5 }' | head -3
done
printf '%s\n' "$A2_DIF" | LC_ALL=C awk -F'\t' '$1 == "S" { s = 1 } END { exit !s }' && A2_FAIL=1
A2_NB=$(printf '%s\n' "$A2_DIF" | LC_ALL=C awk -F'\t' '$1 == "B"' | grep -c . || true)
if [ "$A2_NB" -gt 0 ]; then
  echo "  ❌ $A2_NB entradas de $A2_TABLA tienen MENOS líneas que las que dice la tabla: bájala con --a2-deuda"
  printf '%s\n' "$A2_DIF" | LC_ALL=C awk -F'\t' '$1 == "B" { print "      " $2 " · " $3 " · " $4 ": " $5 " (tabla " $6 ")" }' | head -5
  A2_FAIL=1
fi
[ -n "$A2_NOMED" ] && echo "  ⚠️  sin medir $A2_NOMED: sus entradas de la tabla no se comparan."
# el techo: la tabla de la base verificada, LA MISMA que la de [B] (B_BASE_REF; por omisión el master protegido, con su
# nombre entero), que tiene que ser antepasado de HEAD; sin ella, rojo
A2_BASE_REF="${B_BASE_REF:-refs/remotes/origin/master}"
case "$A2_BASE_REF" in 0000000*) A2_BASE_REF=refs/remotes/origin/master ;; esac
A2_BASE=$(GIT_NO_REPLACE_OBJECTS=1 git rev-parse -q --verify "$A2_BASE_REF^{commit}" 2>/dev/null)
A2_TECHO=""; A2_TXT_TECHO=""
if [ -z "$A2_BASE" ]; then
  echo "  ❌ no hay BASE VERIFICADA ($A2_BASE_REF): sin ella la tabla no tiene techo (¿falta un git fetch?)."; A2_FAIL=1
elif ! git merge-base --is-ancestor "$A2_BASE" HEAD 2>/dev/null; then
  echo "  ❌ HEAD no desciende de la base verificada ($A2_BASE_REF, $(git rev-parse --short "$A2_BASE")): rebase sobre ella."; A2_FAIL=1
elif GIT_NO_REPLACE_OBJECTS=1 git cat-file -e "$A2_BASE:$A2_TABLA" 2>/dev/null; then
  A2_TECHO=$(GIT_NO_REPLACE_OBJECTS=1 git show "$A2_BASE:$A2_TABLA" | a2_norm)
  A2_MALB=$(printf '%s\n' "$A2_TECHO" | grep . | a2_valida)
  if [ -n "$A2_MALB" ]; then echo "  ❌ la tabla de la base verificada no tiene la forma de la tabla:"; printf '%s\n' "$A2_MALB" | head -3; A2_FAIL=1; fi
  A2_TXT_TECHO="la tabla de la base verificada, $(git rev-parse --short "$A2_BASE")"
elif case "$(GIT_NO_REPLACE_OBJECTS=1 git show "$A2_BASE:check-doc-sync.bash" 2>/dev/null)" in *a2-deuda.tsv*) true ;; *) false ;; esac; then
  # (la base ya la conocía y no la tiene: alguien la borró; el techo es cero)
  # ⚠️ Sin tubería a `grep -q`: con `pipefail`, grep sale al primer acierto, `git show` muere de SIGPIPE y la tubería
  # da FALSO; así salía «no la conoce» con una base que sí (lo cazó el juguete de ADR-169 §8).
  A2_TXT_TECHO="CERO: la base verificada, $(git rev-parse --short "$A2_BASE"), conoce la tabla y no la tiene"
else
  echo "  ⚠️  la base verificada no conoce $A2_TABLA: es la que se crea, y no se compara con nada."
fi
if [ -n "$A2_TXT_TECHO" ]; then
  A2_SOBRE=$(LC_ALL=C awk -F'\t' 'FILENAME == ARGV[1] { if (NF >= 4) t[$1 "\t" $2 "\t" $3] = $4; next }
      $0 != "" { k = $1 "\t" $2 "\t" $3; if (!(k in t) || $4 + 0 > t[k] + 0) print }' \
      <(printf '%s\n' "$A2_TECHO") <(printf '%s\n' "$A2_TAB"))
  echo "  techo: $A2_TXT_TECHO ($A2_BASE_REF)"
  if [ -n "$A2_SOBRE" ]; then
    echo "  ❌ $A2_TABLA tiene entradas por ENCIMA del techo (sólo baja):"
    printf '%s\n' "$A2_SOBRE" | head -5 | sed 's/^/      /'; A2_FAIL=1
  fi
fi
rm -rf "$A_DIR"
echo "  deuda declarada: $(printf '%s\n' "$A2_TAB" | LC_ALL=C awk -F'\t' 'NF >= 4 { s += $4 } END { print s + 0 }') líneas en $(printf '%s\n' "$A2_TAB" | grep -c . || true) entradas; hoy, $(printf '%s\n' "$A2_HOY" | LC_ALL=C awk -F'\t' 'NF >= 4 { s += $4 } END { print s + 0 }')"
[ "$A2_FAIL" = "0" ] && echo "  ✓ ninguna cifra vieja nueva en el cuerpo, y la deuda cuadra con la tabla" || FAIL=1

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
# ✏️ 2026-10-31 (T24, ADR-233): DOS tablas, porque son dos deudas distintas. E_DEUDA es la de CONTENIDO: el documento
# tiene su marca y es más vieja que su último commit (su cuerpo no se ha revisado desde entonces). E_DEUDA_FORMATO, la de
# FORMATO: no tiene marca (o la tenía en español, «Última actualización», que [E] no lee). Cada documento tiene que
# fallar por la razón de su tabla. La de formato se pagó el 2026-10-31 con la fecha de la última revisión REAL de cada
# documento —la suya, si la decía en español; si no, la de su último commit con diez líneas nuevas o más, sin las tres
# pasadas en lote de notas y rótulos (ADR-134, ADR-196, ADR-225)—, nunca la de hoy: así pasan a la de contenido, que es
# lo que son. Y un TECHO, como el de [B] desde ADR-167: las dos tablas juntas no pueden tener un documento que no tenga
# la base verificada (un número de tope dejaba cambiar uno por otro).
read -r -d '' E_DEUDA <<'EOF'
REFERENCE.md
# CURRENT-STATUS-PROJECT.md — SALDADA el 2026-10-21 (ADR-182, T26): reescrito entero, con su marca.
# DEPENDENCIES.md — SALDADA el 2026-11-02 (ADR-238, T30): lo GENERA gen-dependencies.py, y la CI comprueba su --check.
# README.md — SALDADA el 2026-10-21 (ADR-183, T25): reescrito contra el árbol, con su marca.
AXIOMS.md
# GODEL-STATUS.md — SALDADA el 2026-10-21 (ADR-185, T28): reescrito entero, con su marca.
doc/REFERENCE-Arithmetic.md
doc/REFERENCE-Full.md
doc/REFERENCE-Incompleteness.md
doc/REFERENCE-Kernel.md
cuarentena/README.md
# ── ampliación del universo, 2026-09-22 (ADR-084): los 21 defectos de los 25
#    documentos que `[E]` nunca había mirado. La cifra sólo puede BAJAR.
# .claude/commands/docsync.md — SALDADA el 2026-10-31 (ADR-235, T21): revisado entero, cada afirmación contra el código.
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
# PLAN-PRUEBAS.md — SALDADA el 2026-10-21 (ADR-185, T28): en AUTHORITATIVE, revisado, con su marca.
PLAN-SORTES.md
Sobre_el_libro.md
# TEOREMAS-E-HIPOTESIS.md — SALDADA el 2026-10-02 (ADR-115): reescrito entero, con su marca.
THOUGHTS.md
TuplasFuncionesYListas.md
# WORKFLOW.md — SALDADA el 2026-10-28 (ADR-212): la Parte 4, con el orden del bump; su marca, al día.
# ── y estas TRES las cazó el propio control, no la medición a mano: `comm` con
#    locales distintos se las había comido. 🔑 Mi red era la estrecha esta vez.
doc/PLAN-COMPLETITUD-FINITISTA.md
ESCALANDO_EL_PROYECTO.md
NAMING-CONVENTIONS.md
EOF
read -r -d '' E_DEUDA_FORMATO <<'EOF'
# ── vacía desde el 2026-10-31 (T24, ADR-233): los 18 que no tenían marca la llevan, con la fecha de su última revisión
#    real, y están en E_DEUDA. Un documento sin marca nuevo no se declara aquí: se le pone la suya.
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
E_DECL=0     # deuda declarada que sigue vigente (de contenido)
E_DECL_F=0   # deuda declarada que sigue vigente (de formato)
for d in $(printf '%s\n' $E_UNIVERSO | sort -u); do
  [ -e "$d" ] || continue
  GIT_DATE=$(git log -1 --format=%ad --date=short -- "$d" 2>/dev/null)
  # ⛔ 2026-10-05 (ADR-121): [E] estaba CIEGO antes del commit. Comparaba la marca con la fecha del último commit
  # que tocó el documento, y un documento editado en el árbol de trabajo sin subir su marca pasaba en local y daba
  # ROJO en la CI del commit (medido: ADR-120, `doc/REFERENCE-Godelization.md`). Si el documento tiene cambios sin
  # commitear, la fecha que cuenta es la de HOY: la que va a tener el commit.
  if [ -n "$(git status --porcelain -- "$d" 2>/dev/null)" ]; then GIT_DATE=$(date +%F); fi
  # ✏️ 2026-10-20 (T04c, ADR-177): el sello de CABECERA, que es el primero del documento aunque vaya a mitad de línea, y
  # la fecha que le sigue (no la primera fecha de la línea). Antes se leía el primer `**Last updated` a PRINCIPIO de
  # línea, y en doc/REFERENCE-Arithmetic.md, -Full.md y -Kernel.md, cuya cabecera lo lleva a mitad de línea, eso era
  # el sello de una SECCIÓN (de junio): una deuda que no se podía saldar subiendo la cabecera. Medido: sólo esos tres
  # documentos cambian de fecha. Uno citado entre comillas invertidas («`**Last updated:**`») no es un sello.
  LU=$(grep -m1 -iE '(^|[^`])\*\*Last updated' "$d" 2>/dev/null \
       | grep -oiE '(^|[^`])\*\*Last updated[^0-9]{0,12}20[0-9]{2}[-‑][0-9]{2}[-‑][0-9]{2}' | head -1 \
       | grep -ohE "20[0-9]{2}[-‑][0-9]{2}[-‑][0-9]{2}" | sed "s/‑/-/g" | head -1)
  EN_TABLA=0
  while IFS= read -r t; do
    [ -n "$t" ] || continue
    [ "$t" = "$d" ] && EN_TABLA=1
  done <<< "$E_DEUDA"
  EN_FORMATO=0
  while IFS= read -r t; do
    [ -n "$t" ] || continue
    [ "$t" = "$d" ] && EN_FORMATO=1
  done <<< "$E_DEUDA_FORMATO"

  ESTADO="ok"
  MOTIVO=""
  if [ -z "$LU" ]; then
    ESTADO="mal"; MOTIVO="sin marca \`**Last updated:**\`"
  elif [ -z "$GIT_DATE" ]; then
    ESTADO="mal"; MOTIVO="sin historia en git"
  elif [ "$LU" \< "$GIT_DATE" ]; then
    ESTADO="mal"; MOTIVO="la marca dice $LU y el último commit que lo tocó es $GIT_DATE (hoy, si tiene cambios sin commitear)"
  fi

  if [ "$ESTADO" = "mal" ] && [ "$EN_TABLA" = "0" ] && [ "$EN_FORMATO" = "0" ]; then
    echo "  ❌ $d: $MOTIVO"
    E_BAD=$((E_BAD+1))
  elif [ "$ESTADO" = "mal" ] && [ "$EN_TABLA" = "1" ] && [ -z "$LU" ]; then
    echo "  ❌ $d: no tiene marca: es deuda de FORMATO, no de contenido. Ponle la de su última revisión real (T24)."
    E_BAD=$((E_BAD+1))
  elif [ "$ESTADO" = "mal" ] && [ "$EN_FORMATO" = "1" ] && [ -n "$LU" ]; then
    echo "  ❌ $d: ya tiene marca: su deuda es de CONTENIDO. Pásalo de E_DEUDA_FORMATO a E_DEUDA."
    E_BAD=$((E_BAD+1))
  elif [ "$ESTADO" = "mal" ] && [ "$EN_FORMATO" = "1" ]; then
    E_DECL_F=$((E_DECL_F+1))
  elif [ "$ESTADO" = "mal" ]; then
    E_DECL=$((E_DECL+1))
  elif [ "$EN_TABLA" = "1" ] || [ "$EN_FORMATO" = "1" ]; then
    echo "  ❌ $d: la deuda ESTÁ SALDADA — quítalo de su tabla (E_DEUDA o E_DEUDA_FORMATO) de este script."
    E_SALDADA=$((E_SALDADA+1))
  fi
done
# el TECHO (T24, ADR-233): las dos tablas juntas, contenidas en las de la base verificada (la misma que [A2] y [B]); sin
# ella, rojo. De la base se leen las dos (la de formato no existía antes del 2026-10-31: vacía).
e_lista() { LC_ALL=C awk -v v="$1" '$0 ~ ("^read -r -d .. " v " <<") { f = 1; next } f && /^EOF$/ { exit } f' \
              | grep -v '^#' | grep . | LC_ALL=C sort -u; }
E_HOY=$( { printf '%s\n' "$E_DEUDA" | grep -v '^#'; printf '%s\n' "$E_DEUDA_FORMATO" | grep -v '^#'; } | grep . | LC_ALL=C sort -u)
E_BASE_REF="${B_BASE_REF:-refs/remotes/origin/master}"
case "$E_BASE_REF" in 0000000*) E_BASE_REF=refs/remotes/origin/master ;; esac
E_BASE=$(GIT_NO_REPLACE_OBJECTS=1 git rev-parse -q --verify "$E_BASE_REF^{commit}" 2>/dev/null)
E_TECHO_TXT=""
if [ -z "$E_BASE" ]; then
  echo "  ❌ no hay BASE VERIFICADA ($E_BASE_REF): sin ella la deuda de [E] no tiene techo (¿falta un git fetch?)."
  E_BAD=$((E_BAD+1))
elif ! git merge-base --is-ancestor "$E_BASE" HEAD 2>/dev/null; then
  echo "  ❌ HEAD no desciende de la base verificada ($E_BASE_REF): rebase sobre ella."
  E_BAD=$((E_BAD+1))
else
  E_BASE_SCRIPT=$(GIT_NO_REPLACE_OBJECTS=1 git show "$E_BASE:check-doc-sync.bash" 2>/dev/null)
  E_TECHO=$( { printf '%s\n' "$E_BASE_SCRIPT" | e_lista E_DEUDA; printf '%s\n' "$E_BASE_SCRIPT" | e_lista E_DEUDA_FORMATO; } \
             | grep . | LC_ALL=C sort -u)
  # (una base con la tabla VACÍA —la meta de la deuda— da un techo vacío, que vale: lo que no se puede medir es una base
  # SIN la tabla. La revisión adversarial de T21 lo vio: con `-z "$E_TECHO"` la deuda saldada habría dado «no pude medir».)
  if ! grep -q "^read -r -d '' E_DEUDA <<" <<< "$E_BASE_SCRIPT"; then
    echo "  ❌ NO PUDE MEDIR el techo: la base verificada $(git rev-parse --short "$E_BASE") no tiene la tabla E_DEUDA."
    E_BAD=$((E_BAD+1))
  else
    E_SUBE=$(LC_ALL=C comm -23 <(printf '%s\n' "$E_HOY") <(printf '%s\n' "$E_TECHO"))
    if [ -n "$E_SUBE" ]; then
      echo "  ❌ la deuda de [E] SUBE: estos documentos no están en las tablas de la base verificada ($(git rev-parse --short "$E_BASE")):"
      printf '%s\n' "$E_SUBE" | sed 's/^/      /'
      E_BAD=$((E_BAD+1))
    fi
    E_TECHO_TXT=" · techo: los $(printf '%s\n' "$E_TECHO" | grep -c .) de la base verificada, $(git rev-parse --short "$E_BASE")"
  fi
fi
echo "  deuda declarada: $E_DECL de contenido y $E_DECL_F de formato$E_TECHO_TXT   ·   sin declarar: $E_BAD   ·   saldadas sin quitar: $E_SALDADA"
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
echo "════ [B] CITAS MUERTAS — ROJO, con trinquete POR CITA (T04, ADR-166) ════"
# ⛔⛔ REHECHO EL 2026-10-18 (T04, ADR-166). Lo que había (ADR-084, ADR-116, ADR-142) tenía tres agujeros, medidos por
# la auditoría y re-medidos (`scripts/pruebas/b/b_medir_t04.bash`, doc/registro/2026-10-18-t04/):
#   (1) el MARCADOR contaba en cualquier punto de la línea: el «falta» de «faltaban» absolvía cinco citas muertas de
#       la fila M-11, y una fecha ISO en cualquier sitio absolvía la línea entera;
#   (2) el UNIVERSO eran siete prefijos (`prf_`, `pcc_`, `goedel_`, `godel`, `d1_…d3_`, `repr_`, `ax_`): un módulo
#       retirado, un teorema con otro nombre o un fichero borrado no los miraba nadie;
#   (3) las RUTAS no las miraba nadie: `FOL/MetaRules.lean` se citaba como vigente con el fichero borrado.
# Ahora el núcleo es `b-citas.awk` y la lógica `b-control.bash`, los dos IDÉNTICOS en FOL (se comparan aquí, byte a
# byte): toda cita con forma de identificador o de ruta; viva si existe; absuelta sólo por un marcador de ESTADO a 100
# bytes o menos, sin cruzar una celda de tabla; la FECHA ya no absuelve, ni un verbo corriente. Los detalles, en la
# cabecera de los dos. Dos revisiones adversariales (ADR-166 §3) encontraron dieciocho vías de verde falso o de trinquete
# débil en las dos primeras versiones, arregladas.
# 🔑 La deuda es POR CITA (`doc/control/b-deuda.tsv`), con TECHO: la tabla de la BASE VERIFICADA (el master protegido),
# que tiene que ser antepasado de HEAD; sólo baja, salvo lo que un cambio del núcleo vea de más sobre los documentos de
# la base (b-control.bash lo explica). ✏️ ADR-167: antes el techo rehacía la historia de la tabla, y la tercera revisión
# adversarial lo subió con la CI en verde con commits intermedios y fusiones; con la base verificada no cuentan.
B_GITS=". ../FOL"   # la historia de los nombres: la de RPP (con lo que aún no está en git) y la de FOL
# la BASE VERIFICADA del techo: el master protegido (ADR-136), lo último que la CI aprobó (ADR-167), con su nombre
# ENTERO (una etiqueta `origin/master` le ganaría a la forma corta)
B_BASE_REF="${B_BASE_REF:-refs/remotes/origin/master}"
# (un objeto reemplazado con `git replace` no engaña a las entradas de [B], que salen de git: ni a las rutas ni a los
# sondeos archivados)
export GIT_NO_REPLACE_OBJECTS=1
B_SUBE_ADR=""   # (ADR-192 lo usó una vez, la primera, para las citas de la historia de lo retirado) sólo si un ADR NUEVO (que no está en la base) deja subir la tabla: «ADR-NNN», con «`clave` · documento · citas»
b_adr_texto() { awk -v a="## $1:" '/^## / { en = (index($0, a) == 1) } en' DECISIONS.md; }
b_adr_texto_base() { git show "$B_BASE:DECISIONS.md" 2>/dev/null | awk -v a="## $1:" '/^## / { en = (index($0, a) == 1) } en'; }
B_DOCS_LISTA="REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md AXIOMS.md GODEL-STATUS.md NEXT-STEPS.md"
# (2026-10-14, ADR-135; T09: TEOREMAS-E-HIPOTESIS.md entra en el universo: es normativo y nadie lo miraba)
B_DOCS_LISTA="$B_DOCS_LISTA TEOREMAS-E-HIPOTESIS.md"
# (2026-11-01, ADR-235; T21: PLAN-PRUEBAS.md entra, con sus citas muertas adjudicadas —catorce, cada una con su
# marcador de estado o en texto plano—; ADR-185 lo había dejado fuera hasta entonces)
B_DOCS_LISTA="$B_DOCS_LISTA PLAN-PRUEBAS.md"
# (la lista es EXPLÍCITA: un documento que desaparece es rojo, no sale del universo con su deuda; y un REFERENCE nuevo
# tiene que entrar en ella)
B_DOCS_LISTA="$B_DOCS_LISTA doc/REFERENCE-Arithmetic.md doc/REFERENCE-Full.md doc/REFERENCE-Godelization.md"
B_DOCS_LISTA="$B_DOCS_LISTA doc/REFERENCE-Incompleteness.md doc/REFERENCE-Kernel.md cuarentena/README.md sondeos/README.md"
B_FAIL=0
for d in doc/REFERENCE-*.md; do
  [ -f "$d" ] || continue
  case " $B_DOCS_LISTA " in *" $d "*) ;; *) echo "  ❌ $d no está en la lista de [B] (B_DOCS_LISTA): un REFERENCE nuevo entra en ella."; B_FAIL=1 ;; esac
done
# el núcleo, igual en los dos repos
for f in strip-lean.awk b-citas.awk b-control.bash; do
  if [ ! -f "../FOL/$f" ]; then
    echo "  ❌ falta ../FOL/$f: no puedo comprobar que las dos copias sean la misma."
    B_FAIL=1
  elif [ "$f" = strip-lean.awk ]; then
    # (strip-lean.awk tiene una cabecera propia en cada repo: se comparan sus líneas de código)
    cmp -s <(grep -v '^#' "$f" | tr -d '\r') <(grep -v '^#' "../FOL/$f" | tr -d '\r') \
      || { echo "  ❌ $f y ../FOL/$f ya no tienen el mismo código: unifícalos."; B_FAIL=1; }
  else
    cmp -s <(tr -d '\r' < "$f") <(tr -d '\r' < "../FOL/$f") \
      || { echo "  ❌ $f y ../FOL/$f ya no son el mismo fichero, byte a byte: unifícalos."; B_FAIL=1; }
  fi
done
DECL_RE="(^|[^A-Za-z0-9_'.])(theorem|lemma|def|abbrev|axiom|opaque|instance|structure|inductive|class) +[^[:space:]:({[]+"
# el nombre entero y su último componente; `prf_univ.{u}` → `prf_univ`
NOMBRES='{n = $NF; sub(/[.]$/, "", n); if (n == "") next; print n; k = n; sub(/.*[.]/, "", k); if (k != n && k != "") print k}'
DECLS=$(mktemp); DECLS_SOND=$(mktemp); B_ENV=$(mktemp); B_MOD=$(mktemp); B_RUT=$(mktemp)
# (DECLS y DECLS_SOND las usan también [M] y [T]: se borran allí; si el script se corta antes, este trap)
trap 'rm -rf "$DECLS" "$DECLS_SOND" "$B_ENV" "$B_MOD" "$B_RUT"' EXIT
# las declaraciones (ADR-116: del código SIN comentarios ni cadenas, con el nombre entero y su último componente),
# también las de cuarentena/ —existen, aunque fuera del build— y las de FOL
find ROBINSON_PlusPlus/ ROBINSON_PlusPlus.lean cuarentena/ ../FOL/FOL/ ../FOL/TheoryFramework/ ../FOL/FOL.lean -name '*.lean' ! -path '*/.lake/*' -print0 2>/dev/null \
  | xargs -0 env LC_ALL=C awk -f strip-lean.awk | LC_ALL=C grep -oE "$DECL_RE" | LC_ALL=C awk "$NOMBRES" | LC_ALL=C sort -u > "$DECLS"
# «nombre|fichero» de cada declaración de un sondeo; una cita que nombra su sondeo queda exenta
find sondeos/ -name '*.lean' 2>/dev/null | sort | while IFS= read -r f; do
  LC_ALL=C awk -f strip-lean.awk "$f" | LC_ALL=C grep -oE "$DECL_RE" | LC_ALL=C awk "$NOMBRES" | LC_ALL=C awk -v f="$f" '{print $0 "|" f}'
done | LC_ALL=C sort -u > "$DECLS_SOND"
# ✏️ 2026-10-16 (ADR-141): los sondeos ARCHIVADOS (en la etiqueta `archivo/sondeos-2026-10`) siguen declarando lo que
# declaraban, y una cita que nombra su sondeo sigue exenta. Sin la etiqueta no se puede medir, y lo dice abajo.
SOND_ARCH=archivo/sondeos-2026-10
if git rev-parse -q --verify "refs/tags/$SOND_ARCH" >/dev/null 2>&1; then
  git ls-tree -r --name-only "$SOND_ARCH" -- sondeos/ 2>/dev/null | grep '^sondeos/[^/]*\.lean$' | while IFS= read -r f; do
    [ -e "$f" ] && continue
    git show "$SOND_ARCH:$f" | LC_ALL=C awk -f strip-lean.awk | LC_ALL=C grep -oE "$DECL_RE" | LC_ALL=C awk "$NOMBRES" \
      | LC_ALL=C awk -v f="$SOND_ARCH:$f" '{print $0 "|" f}'
  done | LC_ALL=C sort -u >> "$DECLS_SOND"
fi
# los MÓDULOS (cada tramo de su nombre con puntos): el cierre de las librerías de RPP y de FOL —no todo `.lean`
# versionado: una librería retirada en cuarentena no es un módulo—, los sondeos y los scripts
{ printf '%s\n' "$CIERRE"; bash ../FOL/cierre-imports.bash 2>/dev/null; git ls-files 'sondeos/*.lean' 'scripts/*.lean'; } \
  | grep . | sed 's/[.]lean$//; s|/|.|g' \
  | LC_ALL=C awk '{ n = split($0, z, "."); for (i = 1; i <= n; i++) { s = z[i]; print s; for (j = i + 1; j <= n; j++) { s = s "." z[j]; print s } } }' \
  | LC_ALL=C sort -u > "$B_MOD"
# las RUTAS: lo versionado en RPP y en FOL (FOL también con `FOL/` delante, que es como lo cita RPP), las etiquetas y,
# de cada etiqueta, «etiqueta:ruta». Las librerías RETIRADAS (`cuarentena/librerias-retiradas/`) entran sólo con su
# ruta entera (y la de sus directorios), con «=»: `FOLPure/Soundness.lean` a secas ya no es un fichero vivo
{ git ls-files; git -C ../FOL ls-files; git -C ../FOL ls-files | sed 's|^|FOL/|'; git tag; git -C ../FOL tag
  for t in $(git tag); do git ls-tree -r --name-only "$t" | sed "s|^|$t:|"; done
  for t in $(git -C ../FOL tag); do git -C ../FOL ls-tree -r --name-only "$t" | sed "s|^|$t:|"; done
} | sed -E 's#^((FOL/)?cuarentena/librerias-retiradas/)#=\1#' \
  | LC_ALL=C awk '{ print } /^=/ { p = substr($0, 2); while (sub(/\/[^\/]*$/, "", p)) print "=" p }' | LC_ALL=C sort -u > "$B_RUT"
B_MEDIDO=1
# los testigos: `goedel_first_prf` y `derives0_soundness` (las declaraciones), `esAC` (un sondeo del árbol),
# `prf_wfAll_objList` (uno archivado, en la etiqueta)
if [ "$(wc -l < "$DECLS" | tr -d ' ')" -lt 1000 ] || ! grep -qxF goedel_first_prf "$DECLS" \
   || ! grep -qxF derives0_soundness "$DECLS" || ! grep -q '^esAC|sondeos/' "$DECLS_SOND" \
   || ! grep -q "^prf_wfAll_objList|$SOND_ARCH:sondeos/" "$DECLS_SOND"; then
  echo "  ❌ NO PUDE MEDIR [B]: las declaraciones salen vacías o sin \`goedel_first_prf\`, \`derives0_soundness\`,"
  echo "      \`esAC\` (de un sondeo) o \`prf_wfAll_objList\` (de uno archivado, en la etiqueta $SOND_ARCH)."
  B_FAIL=1; B_MEDIDO=0
fi
B_DECLS_OK=$B_MEDIDO   # [M] sólo necesita las listas de declaraciones
# el entorno de Lean (constantes, con «P» las del proyecto; opciones; módulos de Lean): lo vuelca
# scripts/VolcarEntorno.lean sobre el build hecho. Sin `lake` en el PATH no se puede medir: desde PowerShell.
if [ "$B_MEDIDO" = "1" ]; then
  if ! command -v lake >/dev/null 2>&1; then
    echo "  ❌ NO PUDE MEDIR [B]: 'lake' no está en el PATH (el entorno de Lean lo vuelca scripts/VolcarEntorno.lean)."
    B_FAIL=1; B_MEDIDO=0
  elif ! VOLCADO="$(cygpath -m "$B_ENV" 2>/dev/null || printf '%s' "$B_ENV")" lake env lean scripts/VolcarEntorno.lean > /dev/null 2>&1 \
       || [ "$(wc -l < "$B_ENV" | tr -d ' ')" -lt 100000 ] || ! grep -q '^ROBINSON_PlusPlus\.Meta\.Hilbert\.Prf\.listInd	P$' "$B_ENV" \
       || ! grep -q '^Init\.Classical	M$' "$B_ENV"; then
    echo "  ❌ NO PUDE MEDIR [B]: el volcado del entorno de Lean salió corto o sin \`Prf.listInd\` (¿el build no está hecho?)."
    B_FAIL=1; B_MEDIDO=0
  fi
fi
if [ "$B_MEDIDO" = "1" ]; then
  B_DECLS=$DECLS; B_SOND=$DECLS_SOND
  B_FAIL_PREVIO=$B_FAIL
  source ./b-control.bash
  [ "$B_FAIL_PREVIO" = "1" ] && B_FAIL=1
fi
rm -f "$B_ENV" "$B_MOD" "$B_RUT"
# (las listas $DECLS y $DECLS_SOND las usa también [M]: se borran allí)
[ "$B_FAIL" = "0" ] && [ "$B_MEDIDO" = "1" ] && echo "  ✓ ninguna cita muerta nueva, y la deuda por cita cuadra con la tabla" || FAIL=1

# ─── 2ter. [I] FRASES QUE UN TEOREMA VIVO DESMIENTE ─────────────────────────
# ⭐ 2026-10-19 (T04b, ADR-169). [A] y [A2] miran cifras; nadie miraba la PROSA que afirma que algo no existe o sigue
# abierto cuando el build lo tiene. Medido ese día: «la mitad `⊬¬G` NO está cerrada» (CURRENT-STATUS-PROJECT.md),
# «NO está en la cadena real» (AXIOMS.md), con `goedel_I_neg` vivo desde ADR-121.
# Cada regla: un SÍMBOLO, una frase prohibida (ERE sobre la línea normalizada) y qué la desmiente. Todos los símbolos de
# las reglas tienen que estar declarados en el árbol (si uno cambia de nombre, rojo: la regla no se apaga en silencio).
# Se miran los documentos autoritativos y los `.lean` de la librería, el barril incluido (T31).
# La línea se NORMALIZA: minúsculas (también Á…Ö), espacios duros, negrita y comillas invertidas fuera, «∼», «~»,
# `\neg` y `\nvdash` a «¬» y «⊬», y lo que haya entre «⊬» y «¬G» (espacios, un paréntesis), fuera. Lo citado entre «…»
# sale, salvo que NOMBRE el símbolo de una regla sin contener la frase: entonces se quitan las comillas y su contenido
# cuenta (un «⊬¬G» entre comillas no esconde nada; un «pendiente» suelto es una etiqueta, y la frase citada la dice otro).
# Lo tachado (~~…~~), fuera. La ventana de una regla no cruza el fin de una frase («. », «;», «|»; «cf.» y «p. ej.» no
# lo son), y se mira también cada PAR de líneas seguidas (una frase partida en dos).
# No cuentan: el código de las vallas (CommonMark: la que cierra, del mismo carácter y al menos igual de larga); una
# sección de registro (su título, de nivel 2 o más y que no sea un ADR, dice como PALABRA registro, histórico, legacy o
# superado, o lleva 🗄️ o 🗑️); un documento que se declara «**DOCUMENTO HISTÓRICO**» (en negrita) en sus diez primeras
# líneas; y una línea con un marcador como PALABRA (histórico, registro, era, falso, «ya no», antes, previo,
# corrección, corregido, inexacto) o con ✏️. Autotest de salida exacta, con cada evasión de la revisión adversarial.
echo ""
echo "════ [I] FRASES QUE UN TEOREMA VIVO DESMIENTE — ROJO (T04b, ADR-169) ════"
I_REGLAS=$(mktemp); I_AUTO=$(mktemp -d)
# (cada regla: símbolo, cómo se escribe en el texto, lo de DELANTE, cuántos bytes como mucho entre los dos, lo de
# DETRÁS, y qué la desmiente)
printf '%s\n' \
  'goedel_I_neg	⊬¬g	⊬¬g	60	(no existe|no est(a|á)[^a-z]|sigue abiert|abiert[oa]|falta|pendiente|sin cerrar)	«⊬¬G» está demostrada: goedel_I_neg (ADR-121)' \
  'goedel_I_neg	⊬¬g	(no existe|sigue abiert|abiert[oa]|falta|pendiente)	60	⊬¬g	«⊬¬G» está demostrada: goedel_I_neg (ADR-121)' \
  'rosser	[^a-z0-9_]rosser	[^a-z0-9_]rosser	30	(pendiente|por hacer|por construir|no est(a|á) (hecho|demostrad|cerrad))	Rosser está demostrado: rosser y rosser_ext (ADR-157)' \
  'lob	[^a-z0-9_]l(ö|o)b[^a-z0-9]	[^a-z0-9_]l(ö|o)b[^a-z0-9]	30	(pendiente|por hacer|por construir|no est(a|á) (hecho|demostrad|cerrad))	Löb está demostrado: lob (ADR-159)' \
  'consistencia	[^a-z0-9_]consistencia[^a-z0-9_]	[^a-z0-9_]consistencia[^a-z0-9_]	50	(sin probar|sin demostrar|sin modelo|no est(a|á) (probad|demostrad))	la consistencia de T_Prf está demostrada: consistencia (ADR-120; CRI-05, T32)' \
  'consistencia	[^a-z0-9_]consistencia[^a-z0-9_]	(sin probar|sin demostrar|sin modelo)	50	[^a-z0-9_]consistencia[^a-z0-9_]	la consistencia de T_Prf está demostrada: consistencia (ADR-120; CRI-05, T32)' \
  'consistencia	[^a-z0-9_]consistenth[^a-z0-9_]	[^a-z0-9_]consistenth[^a-z0-9_]	50	(sin probar|sin demostrar|no est(a|á) (probad|demostrad))	«ConsistentH» está demostrada: consistencia (ADR-120; CRI-05, T32)' \
  'consistencia	[^a-z0-9_]consistenth[^a-z0-9_]	(sin probar|sin demostrar)	50	[^a-z0-9_]consistenth[^a-z0-9_]	«ConsistentH» está demostrada: consistencia (ADR-120; CRI-05, T32)' \
  > "$I_REGLAS"
# (la ventana se mira a mano, no con un intervalo `{0,60}` ni con «[^TAB]?» repetido: mawk, el awk de la CI, retrocede
# y con una expresión así no acaba; el fin de frase se vuelve un TAB, y la ventana no lo cruza)
I_AWK='
function bajar(s) { s = tolower(s); gsub(/Á/, "á", s); gsub(/É/, "é", s); gsub(/Í/, "í", s); gsub(/Ó/, "ó", s)
  gsub(/Ú/, "ú", s); gsub(/Ñ/, "ñ", s); gsub(/Ö/, "ö", s); return s }
function ventana(s, P, n, Q,   r, a, b, resto, t) {
  r = s
  while (match(r, P)) { a = RSTART; b = RSTART + RLENGTH; resto = substr(r, b); t = index(resto, "\t")
    if (t) resto = substr(resto, 1, t - 1)
    if (match(resto, Q) && RSTART - 1 <= n) return 1
    r = substr(r, a + 1) }
  return 0 }
function choca(s,   i) { s = " " s " "; for (i = 1; i <= nr; i++) if ((SIM[i] in vivo) && ventana(s, DEL[i], N[i], DET[i])) return i; return 0 }
function nombra(s,   i) { s = " " s " "; for (i = 1; i <= nr; i++) if ((SIM[i] in vivo) && s ~ SRE[i]) return 1; return 0 }
function norm(s,   p, r, q, c) {
  s = bajar(s); gsub(/\t/, " ", s); gsub(NBSP, " ", s); gsub(NNBSP, " ", s)
  gsub(/~~[^~]*~~/, " ", s); gsub(/[*][*]/, "", s); gsub(/`/, "", s)
  gsub(/∼/, "¬", s); gsub(/\\neg/, "¬", s); gsub(/\\nvdash/, "⊬", s)
  gsub(/⊬[ (]*(¬|~)[ ]*/, "⊬¬", s); gsub(/  +/, " ", s)
  while ((p = index(s, "«")) > 0) { r = substr(s, p + 2); q = index(r, "»"); if (!q) break
    c = substr(r, 1, q - 1); s = substr(s, 1, p - 1) (!choca(c) && nombra(c) ? c : " ") substr(r, q + 2) }
  return s }
function frases(s) { gsub(/cf[.] /, "cf ", s); gsub(/p[.] ej[.]?/, "p ej", s); gsub(/[.] /, "\t", s); gsub(/[.] *$/, "\t", s)
  gsub(/[;|]/, "\t", s); return s }
BEGIN { NBSP = sprintf("%c%c", 194, 160); NNBSP = sprintf("%c%c%c", 226, 128, 175)
  MARC = "[^a-z0-9_](hist(o|ó)ric(o|a|os|as)|registros?|era|eran|fals(o|a|os|as)|ya no|antes|previ(o|a|os|as)|correcci(o|ó)n(es)?|corregid(o|a|os|as)|inexact(o|a|os|as))[^a-z0-9_]"
  REGH = "[^a-z0-9_](registros?|hist(o|ó)ric(o|a|os|as)|legacy|superad(o|a|os|as))[^a-z0-9_]|🗄|🗑" }
FILENAME == ARGV[1] { split($0, z, "\t"); nr++; SIM[nr] = z[1]; SRE[nr] = z[2]; DEL[nr] = z[3]; N[nr] = z[4] + 0; DET[nr] = z[5]
  POR[nr] = z[6]; next }
FILENAME == ARGV[2] { vivo[$0] = 1; next }
FNR == 1 { valla = 0; reg = 0; lean = (FILENAME ~ /[.]lean$/); hist_doc = 0; prev = "" }
FNR <= 10 && /[*][*]DOCUMENTO HIST(O|Ó)RICO/ { hist_doc = 1 }
hist_doc { next }
!lean { f = $0; sub(/^ ? ? ?/, "", f)
  if (valla) {
    if (substr(f, 1, 1) == vc) { if (vc == "`") match(f, /^`+/); else match(f, /^~+/)
      if (RLENGTH >= vn && substr(f, RLENGTH + 1) ~ /^[ \t]*$/) valla = 0 }
    prev = ""; next }
  if (f ~ /^```/ || f ~ /^~~~/) { vc = substr(f, 1, 1); if (vc == "`") match(f, /^`+/); else match(f, /^~+/)
    vn = RLENGTH; valla = 1; prev = ""; next } }
!lean && /^##?#?#?#?#? / { match($0, /^#+/); lv = RLENGTH
  if (reg && lv <= reg) reg = 0
  if (!reg && lv >= 2 && $0 !~ /^## ADR-/ && (" " bajar($0) " ") ~ REGH) reg = lv
  prev = ""; next }
reg { next }
/^[ \t]*$/ { prev = ""; next }
{ s = norm($0); ex = (index($0, "✏") > 0) || ((" " s " ") ~ MARC); s = frases(s)
  hit = ex ? 0 : choca(s)
  if (hit) print FILENAME ":" FNR ": " POR[hit] "\t" substr($0, 1, 140)
  else if (!ex && prev != "" && !prevhit && (i = choca(prev " " s))) print FILENAME ":" prevn ": " POR[i] "\t" substr(prevraw, 1, 140)
  if (ex) prev = ""; else { prev = s; prevn = FNR; prevraw = $0; prevhit = hit } }'
# autotest: cada frase que tiene que salir, cada exención, y las evasiones de la revisión adversarial de ADR-169
printf '%s\n' goedel_I_neg lob rosser consistencia > "$I_AUTO/vivos4"
printf '%s\n' goedel_I_neg > "$I_AUTO/vivos1"
printf '%s\n' '# Doc' 'La mitad ⊬¬G no existe todavía.' 'Lo que sigue abierto es ⊬¬G.' 'Rosser está pendiente.' \
  'LÖB ESTÁ PENDIENTE.' 'Se dijo «la mitad ⊬¬G no existe».' 'La mitad «⊬¬G» no existe.' '~~⊬¬G no existe~~ ya no.' \
  '✏️ ⊬¬G falta (corrección).' 'Fuera de duda: ⊬ (¬G) sigue abierta.' $'La mitad \xe2\x8a\xac\xc2\xa0\xc2\xacG, cf. el §3.2, no existe.' \
  'La mitad ⊬¬G está demostrada; lo que falta es Con.' 'La mitad ⊬¬G' 'no existe aún.' '```' '~~~' '⊬¬G no existe' '```' \
  '## Notas y registro' '⊬¬G no existe aquí.' '## Hoy' '⊬¬G falta otra vez.' 'Un global pendiente.' \
  'Rosser_ext no está demostrado.' 'El control «`⊬¬G` (Rosser)» y la marca «pendiente», hecho.' \
  '`⊬¬G` **no** está cerrado.' 'La consistencia de T_Prf sigue sin probar.' 'Sin modelo no hay consistencia que valga.' \
  '`ConsistentH` sigue sin demostrar.' 'La consistencia está demostrada; lo sin probar es otro asunto.' \
  'La inconsistencia sigue sin probar.' 'ConsistentH y un cierre sin modelo.' > "$I_AUTO/doc.md"
printf '%s\n' 'Rosser está pendiente.' 'La mitad ⊬¬G no existe.' > "$I_AUTO/doc2.md"
printf '%s\n' '> ⚠️ **DOCUMENTO HISTÓRICO.**' '⊬¬G no existe.' > "$I_AUTO/doc3.md"
printf '%s\n' 'Este no es un documento histórico.' '⊬¬G no existe.' > "$I_AUTO/doc4.md"
I_AUTO_SAL=$( (cd "$I_AUTO" && LC_ALL=C awk "$I_AWK" "$I_REGLAS" vivos4 doc.md doc3.md doc4.md && LC_ALL=C awk "$I_AWK" "$I_REGLAS" vivos1 doc2.md) \
  | cut -d: -f1,2 | tr '\n' ';')
I_AUTO_OK='doc.md:2;doc.md:3;doc.md:4;doc.md:5;doc.md:7;doc.md:10;doc.md:11;doc.md:13;doc.md:22;doc.md:24;doc.md:26;doc.md:27;doc.md:28;doc.md:29;doc4.md:2;doc2.md:2;'
I_FAIL=0
I_FALTAN=$(cut -f1 "$I_REGLAS" | LC_ALL=C sort -u | while IFS= read -r s; do grep -qxF "$s" "$DECLS" 2>/dev/null || printf ' %s' "$s"; done)
I_LEAN=$(printf '%s\n' "$CIERRE" | grep -E '^ROBINSON_PlusPlus(/.*)?[.]lean$')
I_FICH=""
for f in $DOCS $I_LEAN; do [ -e "$f" ] && I_FICH="$I_FICH $f"; done
if [ "$I_AUTO_SAL" != "$I_AUTO_OK" ]; then
  echo "  ❌ NO PUDE MEDIR [I]: el autotest no da lo esperado ($I_AUTO_OK), da: $I_AUTO_SAL"
  I_FAIL=1
elif [ "${B_DECLS_OK:-0}" != "1" ] || [ -n "$I_FALTAN" ]; then
  # (sin las declaraciones, o sin el símbolo de una regla, la regla no valdría y saldría verde sin mirar nada)
  echo "  ❌ NO PUDE MEDIR [I]: las declaraciones de [B] no están, o no tienen el símbolo de una regla:${I_FALTAN:- (sin declaraciones)}."
  I_FAIL=1
elif [ -n "${A_MAL:-}" ]; then
  echo "  ❌ NO PUDE MEDIR [I]: documentos que no son UTF-8 válido o llevan NUL (ver [A])."
  I_FAIL=1
elif ! I_HITS=$(LC_ALL=C awk "$I_AWK" "$I_REGLAS" "$DECLS" $I_FICH); then
  echo "  ❌ NO PUDE MEDIR [I]: el awk falló."
  I_FAIL=1
elif [ -n "$I_HITS" ]; then
  printf '%s\n' "$I_HITS" | sed 's/^/  ❌ /; s/\t/\n      /'
  I_FAIL=1
fi
rm -rf "$I_REGLAS" "$I_AUTO"
[ "$I_FAIL" = "0" ] && echo "  ✓ ninguna frase que un teorema vivo desmienta ($(printf '%s\n' "$I_LEAN" | grep -c .) .lean y los documentos)" || FAIL=1

# ─── [N] CITAS POR NÚMERO DE LÍNEA — ROJO ──────────────────────────────────────
# ⭐ AÑADIDO el 2026-10-28 (T34, ADR-209). Los documentos de referencia citan por SÍMBOLO, nunca por número de línea
# (decisión del propietario). Una cita «fichero:línea» se desplaza en cuanto el fichero cambia, y se actualizaba
# «por desplazamiento» sin mirar el destino: nueve documentos citaban `ax_tc_cons` en la línea 827 de Minimal/Axioms
# cuando estaba en la 902 (la auditoría, T34), y de las 43 que quedaban, una docena ya apuntaba a otra declaración.
# Mira los documentos AUTORITATIVOS salvo DECISIONS.md y NEXT-STEPS.md, que son REGISTRO fechado (un ADR cita lo que
# había ese día), y rompe con: un fichero con extensión seguido de «:N», «:LN» o «#LN» (también con la comilla
# invertida de por medio), una cita suelta «`:N`» (la línea de un fichero citado antes) y un «`Módulo:N`» sin
# extensión. (En su primera ejecución vio 46 que el primer recuento, sólo de «fichero.ext:N», no veía.)
# ⚠️ Lo que NO mira: los comentarios de los .lean (no son documentos de referencia; corregirlos recompila sus módulos).
# ⭐ Con AUTOTEST: siete líneas sintéticas —cuatro citas que tiene que ver y tres que no— deben dar exactamente 4.
echo ""
echo "════ [N] CITAS POR NÚMERO DE LÍNEA — ROJO (T34, ADR-209) ════"
N_RE='[A-Za-z0-9_./-]*\.[A-Za-z]+`?(:|#)L?[0-9]|`:[0-9]+|`[A-Z][A-Za-z0-9_]*:[0-9]'
N_FAIL=0
N_AUTO=$(printf '%s\n' 'la cita `Minimal/Axioms.lean:902` se mueve' 'y su vecina (`:443`) también' \
  'un enlace https://github.com/x/y/blob/master/README.md#L10' 'por símbolo: `ax_tc_cons` en `Minimal/Axioms.lean`' \
  'una hora, 12:30, no es una línea' 'un sitio: `EvalPredPrf:128`' 'Lean v4.35.0: la versión' | grep -cE "$N_RE")
if [ "$N_AUTO" != "4" ]; then
  echo "  ❌ NO PUDE MEDIR [N]: el autotest da $N_AUTO citas y debían ser 4 (¿otro grep?)."
  N_FAIL=1
else
  N_DOCS=""
  for d in $AUTHORITATIVE; do
    case "$d" in DECISIONS.md|NEXT-STEPS.md) continue ;; esac
    [ -f "$d" ] && N_DOCS="$N_DOCS $d"
  done
  # shellcheck disable=SC2086
  N_HAY=$(grep -nE "$N_RE" $N_DOCS /dev/null || true)
  if [ -n "$N_HAY" ]; then
    echo "  ✗ citas por número de línea ($(printf '%s\n' "$N_HAY" | grep -c .)): cítese el símbolo (y su fichero, sin línea)"
    printf '%s\n' "$N_HAY" | head -15 | cut -c1-200 | sed 's/^/      /'
    N_FAIL=1
  else
    echo "  ✓ ninguna cita por número de línea en $(printf '%s\n' $N_DOCS | grep -c .) documentos de referencia (autotest: 4 de 4)"
  fi
fi
[ "$N_FAIL" = "0" ] || FAIL=1

# ─── 4. PROYECCIÓN: ¿está cada módulo en el catálogo? ────────────────────────
echo
echo "════ [C] PROYECCIÓN (AI-GUIDE §1/§14) ════"
C_FAIL=0
# ✏️ 2026-10-18 (T15, ADR-163): el dominio es el cierre de imports (los módulos de las capas), no cuatro `ls`.
# ✏️ 2026-10-20 (T04c, ADR-177): por PALABRA y DENTRO de §1, el catálogo. Antes `grep -q "$m" REFERENCE.md` casaba por
# subcadena y en todo el documento: `Rosser` quedaba absuelto por `RosserW1`, y `Godel` por cualquier frase que lo
# nombrara. Medido: los 118 están hoy en §1 como palabra. Sin §1, rojo: un dominio vacío no absuelve a nadie.
C_CATALOGO=$(sed -n '/^## 1 · Catálogo de módulos/,/^## 2 /p' REFERENCE.md 2>/dev/null)
if [ -z "$C_CATALOGO" ]; then
  echo "  ❌ REFERENCE.md no tiene la sección «## 1 · Catálogo de módulos»: [C] no puede comprobar nada."
  C_FAIL=1
fi
for f in $(printf '%s\n' "$CIERRE" | grep '^ROBINSON_PlusPlus/[^/]*/'); do
  [ -e "$f" ] || continue
  m=$(basename "$f" .lean)
  case "$C_CATALOGO" in
    # (sin tubería a `grep -q`: con `pipefail`, el productor muere de SIGPIPE y daría un «no» falso, como en [A2], ADR‑169)
    *"$m"*) grep -qE "(^|[^A-Za-z0-9_])$m([^A-Za-z0-9_]|\$)" <<< "$C_CATALOGO" && continue ;;
  esac
  echo "  ✗ $m NO aparece en el catálogo REFERENCE.md §1"
  C_FAIL=1
done
# ⛔⛔ AÑADIDO el 2026-09-17. Hasta hoy este control SOLO miraba los modulos de
# ROBINSON_PlusPlus contra SU REFERENCE.md: los de FOL no los miraba NADIE, y por eso
# veintiseis modulos llevaban dias sin proyectar en FOL/REFERENCE.md §6 sin que saltara
# nada. Y se comprueba contra §6 (Exports), que es lo que AI-GUIDE §14 exige de verdad
# -- no basta con que el nombre aparezca en la tabla de modulos.
# ✏️ 2026-10-18 (T15, ADR-163): el dominio es el cierre de imports de FOL (`../FOL/cierre-imports.bash`), sus
# ficheros de `FOL/`, a cualquier profundidad. Antes eran `FOL/*.lean` y `FOL/Theorems/*.lean`, y un `continue`
# pensado para el barril dejaba fuera `FOL/FOL.lean`, el módulo `FOL.FOL`: el barril está en la raíz de FOL.
FOLCIERRE=""
if [ -f ../FOL/REFERENCE.md ] && [ ! -f ../FOL/cierre-imports.bash ]; then
  echo "  ❌ falta ../FOL/cierre-imports.bash: no sé qué módulos tiene FOL (alcance REDUCIDO)."
  C_FAIL=1
elif [ -f ../FOL/REFERENCE.md ]; then
  FOLCIERRE=$(bash ../FOL/cierre-imports.bash 2>/dev/null) \
    || { echo "  ❌ el cierre de imports de FOL no sale: bash ../FOL/cierre-imports.bash"; C_FAIL=1; }
fi
if [ -n "$FOLCIERRE" ]; then
  FOLEXP=$(sed -n '/^## 6\. Exports/,/^## 7\./p' ../FOL/REFERENCE.md)
  for f in $(printf '%s\n' "$FOLCIERRE" | grep '^FOL/' | sed 's|^|../FOL/|'); do
    [ -e "$f" ] || continue
    m=${f#../FOL/FOL/}; m=${m%.lean}
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

# ─── [M] MANDATORIES: lo que nombra la columna «Verificación», existe ───────────────
echo '════ [M] MANDATORIES — la columna «Verificación» nombra cosas que EXISTEN (ROJO) ════'
# ⛔ POR QUÉ EXISTE (2026-10-12, ADR-133; T03 de doc/AUDITORIA-SUELO-2026-10-12.md): la tabla de lectura
# obligatoria de DECISIONS.md verificaba M-10 con `derives_completo` y `hgi_es_refutar`, que no tenían
# declaración desde ADR-115, y ningún control lo veía: [B] sólo mira citas con siete prefijos y absuelve por
# marcador. Aquí no hay marcador que valga.
# Cada fila `| **M…** |` debe ocupar UNA línea y tener 4 columnas: si no, ROJO (la M-11 vieja, partida en 16
# líneas, escondía así su verificación). En la ÚLTIMA columna, cada cita entre comillas invertidas se comprueba
# según su forma:
#   · una ORDEN (lleva espacios): sus palabras con forma de ruta deben existir (`bash X` → X); las que tienen
#     forma de nombre Lean con `_` (sin comillas pegadas: un patrón de grep no cuenta) deben estar declaradas,
#     y si acaban en `_`, como familia (por prefijo);
#   · una RUTA (lleva `/` o acaba en .bash/.lean/.md/.yml/.awk/.py; se quita `:línea`): debe existir, mirada
#     desde la raíz, desde ROBINSON_PlusPlus/, desde ../FOL/ y desde ../FOL/FOL/;
#   · un NÚMERO (un run de CI): no se comprueba;
#   · un SUFIJO (`_rhs` tras `substCodeT_hole_lhs`, en la MISMA fila): se arma con la cita anterior;
#   · una palabra clave de Lean (M_KW: `axiom`, `export`, `rfl`): no se comprueba;
#   · un MÓDULO (`FOL.Skolem0`): debe existir su fichero; si no, se trata como un nombre;
#   · un NOMBRE: debe estar DECLARADO (el nombre entero o su último componente) en el build, en FOL o en un
#     sondeo — las listas de [B]; si acaba en `_`, es una familia y basta uno con ese prefijo.
# ⚠️ Lo que NO mira: lo que no va entre comillas invertidas, y si la verificación verifica de verdad la regla.
# ⭐ Con AUTOTEST: dos filas sintéticas —una con un nombre, una ruta y un nombre‑en‑orden inexistentes, más uno
#    que sólo declara un sondeo y que debe pasar; otra partida en dos líneas— deben dar exactamente 4 fallos; si
#    no, el control no mide y lo dice. Se estrenó con el fallo puesto (ADR-133): ver ese ADR.
# 🔧 Para probarlo contra otra versión de la tabla: M_DOC=fichero bash check-doc-sync.bash. Es un MODO DE
#    PRUEBA: dice qué fichero miró y nunca da verde.
M_FAIL=0
M_KW=" axiom export rfl "
M_IDRE="^[A-Za-z_][A-Za-z0-9_.'!?]*$"
m_tokens() {   # stdin: líneas de la tabla → «fila<TAB>cita»; una fila mal formada → «fila<TAB>@@FILA»
  LC_ALL=C awk '
    /^\| \*\*M/ {
      s = $0; sub(/[ \t\r]+$/, "", s)
      id = s; sub(/^\| \*\*/, "", id); sub(/\*\*.*$/, "", id)
      if (s !~ /\|$/) { print id "\t@@FILA"; next }
      sub(/^\| /, "", s); sub(/ \|$/, "", s)
      n = split(s, c, / \| /)
      if (n != 4) { print id "\t@@FILA"; next }
      v = c[4]
      while (match(v, /`[^`]+`/)) { print id "\t" substr(v, RSTART + 1, RLENGTH - 2); v = substr(v, RSTART + RLENGTH) }
    }'
}
m_ruta() {
  local r="${1%%:*}"; r="${r%/}"
  local p
  for p in "" "ROBINSON_PlusPlus/" "../FOL/" "../FOL/FOL/"; do [ -e "$p$r" ] && return 0; done
  return 1
}
m_declarado() {   # sin tuberías: con `pipefail`, un `grep -q` que corta a su productor daba 141 (falso «no»)
  LC_ALL=C grep -qxF -- "$1" "$DECLS" && return 0
  LC_ALL=C awk -F'|' -v n="$1" '$1 == n { f = 1; exit } END { exit !f }' "$DECLS_SOND"
}
m_familia() {     # algún nombre declarado empieza por $1
  LC_ALL=C awk -v p="$1" 'index($0, p) == 1 { f = 1; exit } END { exit !f }' "$DECLS" && return 0
  LC_ALL=C awk -F'|' -v p="$1" 'index($1, p) == 1 { f = 1; exit } END { exit !f }' "$DECLS_SOND"
}
m_modulo() {
  local p="${1//.//}.lean" q
  for q in "" "../FOL/"; do [ -f "$q$p" ] && return 0; done
  return 1
}
m_revisa() {   # stdin: líneas de la tabla → stdout: «fila|cita|motivo» por cada fallo
  local prev="" f0="" fila tok w cand
  m_tokens | while IFS=$'\t' read -r fila tok; do
    if [ "$fila" != "$f0" ]; then prev=""; f0="$fila"; fi
    if [ "$tok" = "@@FILA" ]; then echo "$fila|(la fila)|no ocupa UNA línea con 4 columnas"; continue; fi
    case "$tok" in
      *" "*)
        read -ra M_PALABRAS <<< "$tok"
        for w in "${M_PALABRAS[@]}"; do
          case "$w" in
            \'*|*\'|\"*|*\") : ;;
            */*|*.bash|*.lean|*.md|*.yml|*.awk|*.py) m_ruta "$w" || echo "$fila|$tok|ruta inexistente: $w" ;;
            *)
              w="${w%[,;:)]}"; w="${w#[(]}"
              if [[ "$w" =~ $M_IDRE ]] && [[ "$w" == *_* ]]; then
                if [[ "$w" == *_ ]]; then m_familia "$w" || echo "$fila|$tok|familia sin ningún nombre declarado: $w"
                elif ! m_declarado "$w" && ! m_declarado "${w##*.}"; then echo "$fila|$tok|no declarado: $w"; fi
              fi ;;
          esac
        done ;;
      */*|*.bash|*.lean|*.md|*.yml|*.awk|*.py) m_ruta "$tok" || echo "$fila|$tok|ruta inexistente" ;;
      [0-9]*) : ;;
      _*) if [ -n "$prev" ]; then cand="${prev%_*}$tok"; m_declarado "$cand" || echo "$fila|$tok|no declarado: $cand"
          else echo "$fila|$tok|sufijo sin nombre delante en su fila"; fi ;;
      *)
        if [[ "$M_KW" == *" $tok "* ]]; then :
        elif [[ "$tok" == *_ ]]; then m_familia "$tok" || echo "$fila|$tok|familia sin ningún nombre declarado"
        elif [[ "$tok" == *.* ]] && m_modulo "$tok"; then :
        elif m_declarado "$tok" || m_declarado "${tok##*.}"; then prev="$tok"
        else echo "$fila|$tok|no declarado"; fi ;;
    esac
  done
}
M_FICH="${M_DOC:-DECISIONS.md}"
if [ -n "${M_DOC:-}" ]; then echo "  ⚠️ MODO DE PRUEBA: la tabla se lee de $M_FICH (en este modo [M] nunca da verde)"; fi
if [ "$B_DECLS_OK" != "1" ]; then
  echo "  ❌ NO PUDE MEDIR [M]: sin las listas de declaraciones de [B]."
  M_FAIL=1
elif [ ! -f "$M_FICH" ]; then
  echo "  ❌ NO PUDE MEDIR [M]: no existe $M_FICH."
  M_FAIL=1
else
  M_AUTO=$(printf '%s\n' \
    '| **M-0** | prueba | — | `no_existe_jamas_m0`, `ROBINSON_PlusPlus/NoExiste_m0.lean`, `#print axioms muerto_m0_zz`, `goedel_first_prf` y `prf_wfAll_objList` |' \
    '| **M-00** | prueba partida | — | `goedel_first_prf`' \
    '  y su continuación |' | m_revisa | wc -l | tr -d ' ')
  M_TABLA=$(awk '/^## ⚠️ MANDATORIES/{f=1; next} f && /^## /{exit} f && /^\| \*\*M/{print}' "$M_FICH")
  M_NF=$(printf '%s\n' "$M_TABLA" | grep -c '^| \*\*M' || true)
  M_NT=$(printf '%s\n' "$M_TABLA" | m_tokens | grep -vc '@@FILA$' || true)
  if [ "$M_AUTO" != "4" ]; then
    echo "  ❌ NO PUDE MEDIR [M]: el autotest debía dar 4 fallos y da $M_AUTO."
    M_FAIL=1
  elif [ "$M_NF" -lt 10 ] || [ "$M_NT" -lt 20 ]; then
    echo "  ❌ NO PUDE MEDIR [M]: sólo $M_NF filas y $M_NT citas en la tabla MANDATORIES (¿cambió su cabecera?)."
    M_FAIL=1
  else
    M_ROJO=$(printf '%s\n' "$M_TABLA" | m_revisa)
    if [ -n "$M_ROJO" ]; then
      printf '%s\n' "$M_ROJO" | while IFS='|' read -r f t m; do echo "  ✗ $f: \`$t\` — $m"; done
      M_FAIL=1
    else
      echo "  ✓ las $M_NT citas de la columna «Verificación» ($M_NF filas) nombran cosas que existen"
    fi
  fi
fi
[ -n "${M_DOC:-}" ] && M_FAIL=1
rm -f "$DECLS" "$DECLS_SOND"
[ "$M_FAIL" = "0" ] || FAIL=1

# ─── [T] TITULARES: cada uno tiene su fila en TEOREMAS-E-HIPOTESIS.md ───────────────
echo '════ [T] TITULARES — cada uno tiene su fila en TEOREMAS-E-HIPOTESIS.md, y cada fila es un titular (ROJO) ════'
# ⛔ POR QUÉ EXISTE (2026-10-14, ADR-135; T09 de doc/AUDITORIA-SUELO-2026-10-12.md): la regla de ese documento
# —«una fila AUSENTE es un fallo»— se cumplía a mano, y el documento llegó a decir que `⊬¬G` no existía con la
# fila de `goedel_I_neg` diez líneas más arriba. El universo de titulares se DECLARA aquí, en T_UNIVERSO: la
# tabla de check-footprints.bash no sirve, porque tiene filas que no son titulares (`consistentH_de`,
# `V₀_eq_codigo`, `v_ancla`).
# La FILA de un titular es una fila de tabla de §1 o de §3 con su nombre en negrita y entre comillas invertidas,
# **`x`**, en la columna del nombre: la PRIMERA en §1 y la SEGUNDA en §3 (la primera es «D1»/«D2»/«D3»). Un nombre
# en otra columna (la hipótesis, quién la descarga) no cuenta, ni uno tachado (~~…~~). Mira: (1) cada nombre del
# universo está DECLARADO en el build de RPP; (2) tiene su fila; (3) ninguno tiene dos; (4) cada nombre con fila está
# en el universo. ✏️ 2026-10-18 (T07, ADR-165): y (5) T_UNIVERSO es EXACTAMENTE la lista `TITULARES` de
# `Meta/ContratoTitulares.lean`, la que fija el contrato de los enunciados: si se separan, un titular nuevo se quedaría
# sin contrato, o el contrato vigilaría a uno que ya no lo es.
# ⚠️ Lo que NO mira: que la columna «¿qué usa la prueba?» sea la medida (eso lo mide `#modelo` de
# `sondeos/InduccionTitulares.lean`, y lo mecanizará T08 en el build), ni que un teorema NUEVO deba ser titular:
# eso lo decide quien lo añade, y en el mismo commit lo pone aquí y le da su fila. Una fila partida en dos líneas
# sale como «no tiene fila», sin diagnóstico propio.
# ⭐ Con AUTOTEST de salida EXACTA (no por cuenta: un extractor que no extrae nada daba también la cuenta esperada,
#    revisión adversarial de ADR-135): un documento sintético con un nombre en la columna de la hipótesis, uno
#    tachado, uno tras el fin de §1, una fila de §3, una intrusa y una repetida, y un universo con un nombre sin
#    declarar, deben dar exactamente los cinco fallos esperados; si no, el control no mide y lo dice.
# 🔧 Para probarlo contra otra versión del documento: T_DOC=fichero bash check-doc-sync.bash. Es un MODO DE
#    PRUEBA: dice qué fichero miró y nunca da verde.
T_FAIL=0
T_UNIVERSO="goedel_first_prf goedel_second_prf prf_con_imp_godel prf_godelCN_fixedpoint prf_tarski
  goedel_I goedel_II tarski goedel_I_neg godelCN_indecidible modelo_prov_iff godelCN_verdadera con_verdadera
  tarski_semantico consistencia repr_pos'_prf d2_prf d3_prf_real rosser_ext rosser lob
  prf_godel_iff_con goedel_second_formalizado con_indecidible
  prf_of_prov_de modelo_prov_iff_de godelCN_verdadera_de con_verdadera_de
  tarski_semantico_de goedel_I_fol goedel_I_neg_fol goedel_II_fol"
t_filas() {   # stdin: el documento → un nombre por cada aparición en la columna del nombre de §1 (1.ª) o §3 (2.ª)
  LC_ALL=C awk '
    /^## 1 · / { s = 1; next }
    /^## 3 · / { s = 3; next }
    /^## /     { s = 0 }
    s && /^\|/ {
      n = split($0, c, "|")
      k = (s == 1) ? 2 : 3
      if (k > n) next
      v = c[k]
      gsub(/~~[^~]*~~/, "", v)
      while (match(v, /\*\*`[^`]+`\*\*/)) { print substr(v, RSTART + 3, RLENGTH - 6); v = substr(v, RSTART + RLENGTH) }
    }'
}
t_revisa() {   # $1 = universo, $2 = documento, $3 = lista de declaraciones → «nombre|motivo» por cada fallo
  local todas filas u
  todas=$(t_filas < "$2")
  filas=$(printf '%s\n' "$todas" | LC_ALL=C sort -u)
  for u in $1; do
    LC_ALL=C grep -qxF -- "$u" "$3" || echo "$u|no está declarado en el build de RPP"
    printf '%s\n' "$filas" | LC_ALL=C grep -qxF -- "$u" || echo "$u|no tiene fila en las tablas de §1 o §3"
  done
  printf '%s\n' "$todas" | LC_ALL=C sort | LC_ALL=C uniq -d | while IFS= read -r u; do
    [ -n "$u" ] && echo "$u|tiene más de una fila"
  done
  printf '%s\n' "$filas" | while IFS= read -r u; do
    [ -n "$u" ] || continue
    case " $(printf '%s' "$1" | tr '\n' ' ') " in *" $u "*) : ;; *) echo "$u|tiene fila y no está en T_UNIVERSO" ;; esac
  done
}
T_FICH="${T_DOC:-TEOREMAS-E-HIPOTESIS.md}"
if [ -n "${T_DOC:-}" ]; then echo "  ⚠️ MODO DE PRUEBA: el documento se lee de $T_FICH (en este modo [T] nunca da verde)"; fi
T_DECLS=$(mktemp); T_AUTODOC=$(mktemp)
trap 'rm -f "$DECLS" "$DECLS_SOND" "$T_DECLS" "$T_AUTODOC"' EXIT
find ROBINSON_PlusPlus/ ROBINSON_PlusPlus.lean -name '*.lean' ! -path '*/.lake/*' -print0 2>/dev/null \
  | xargs -0 env LC_ALL=C awk -f strip-lean.awk | LC_ALL=C grep -oE "$DECL_RE" | LC_ALL=C awk "$NOMBRES" \
  | LC_ALL=C sort -u > "$T_DECLS"
printf '%s\n' '## 1 · prueba' '' '| teorema | hipótesis | quién |' '|---|---|---|' \
  '| **`goedel_first_prf`** (`Meta/GodelTwoPrf.lean`) | **`tarski`**, en la hipótesis, no cuenta | **`tarski`**, tampoco |' \
  '| ~~**`tachado_t0`**~~ | — | — |' '| **`intruso_t0`** | — | — |' '| **`d2_prf`** | — | — |' '' \
  '## 2 · fuera' '| **`fuera_t0`** | — | — |' '' '## 3 · D' '| | teorema | hipótesis |' '|---|---|---|' \
  '| **D2** | **`d2_prf`** (`Meta/DerivCondPrf.lean`) | ninguna |' '' '## 4 · fin' > "$T_AUTODOC"
T_AUTO=$(t_revisa "goedel_first_prf no_existe_jamas_t0 tarski d2_prf" "$T_AUTODOC" "$T_DECLS" | LC_ALL=C sort | tr '\n' ';')
T_ESPERADO="d2_prf|tiene más de una fila;intruso_t0|tiene fila y no está en T_UNIVERSO;no_existe_jamas_t0|no está declarado en el build de RPP;no_existe_jamas_t0|no tiene fila en las tablas de §1 o §3;tarski|no tiene fila en las tablas de §1 o §3;"
t_cuenta() { echo $#; }
T_NU=$(t_cuenta $T_UNIVERSO)
if [ "$(wc -l < "$T_DECLS" | tr -d ' ')" -lt 1000 ] || ! LC_ALL=C grep -qxF goedel_first_prf "$T_DECLS"; then
  echo "  ❌ NO PUDE MEDIR [T]: las declaraciones del build salen vacías o sin \`goedel_first_prf\` (¿strip-lean.awk?)."
  T_FAIL=1
elif [ "$T_AUTO" != "$T_ESPERADO" ]; then
  echo "  ❌ NO PUDE MEDIR [T]: el autotest no da los cinco fallos esperados; da: $T_AUTO"
  T_FAIL=1
elif [ "$T_NU" -lt 10 ]; then
  echo "  ❌ NO PUDE MEDIR [T]: T_UNIVERSO tiene sólo $T_NU nombres (¿se vació?)."
  T_FAIL=1
elif [ ! -f "$T_FICH" ]; then
  echo "  ❌ NO PUDE MEDIR [T]: no existe $T_FICH."
  T_FAIL=1
else
  T_ROJO=$(t_revisa "$T_UNIVERSO" "$T_FICH" "$T_DECLS")
  if [ -n "$T_ROJO" ]; then
    printf '%s\n' "$T_ROJO" | while IFS='|' read -r n m; do echo "  ✗ \`$n\` — $m"; done
    T_FAIL=1
  else
    echo "  ✓ los $T_NU titulares de T_UNIVERSO están declarados y tienen UNA fila en $T_FICH, y ninguna fila sobra"
  fi
fi
# (5) T_UNIVERSO = `TITULARES` (T07). Los nombres de la lista son ``A.B.c``; se compara el último componente.
T_LEAN=ROBINSON_PlusPlus/Meta/ContratoTitulares.lean
T_LISTA=$(awk '/^def TITULARES : List Name := \[/{f=1} f{print} f && /\]$/{exit}' "$T_LEAN" 2>/dev/null \
  | grep -oE '``[A-Za-z0-9_.'"'"']+' | sed 's/^``//; s/.*\.//' | LC_ALL=C sort || true)
T_UNI_ORD=$(printf '%s\n' $T_UNIVERSO | LC_ALL=C sort)
if [ -z "$T_LISTA" ]; then
  echo "  ❌ NO PUDE MEDIR [T](5): no encuentro la lista TITULARES en $T_LEAN."
  T_FAIL=1
elif [ "$T_LISTA" != "$T_UNI_ORD" ]; then
  echo "  ✗ T_UNIVERSO y TITULARES ($T_LEAN, el contrato de T07) no son la misma lista:"
  diff <(printf '%s\n' "$T_UNI_ORD") <(printf '%s\n' "$T_LISTA") | grep '^[<>]' \
    | sed 's/^< /    sólo en T_UNIVERSO: /; s/^> /    sólo en TITULARES: /'
  T_FAIL=1
else
  echo "  ✓ y son los $T_NU de TITULARES ($T_LEAN), los que fija el contrato de los enunciados (T07)"
fi
rm -f "$T_DECLS" "$T_AUTODOC"
[ -n "${T_DOC:-}" ] && T_FAIL=1
[ "$T_FAIL" = "0" ] || FAIL=1

# ─── [G] DEUDAS ENUNCIADAS QUE YA TIENEN TESTIGO — ROJO (T32, ADR-237) ──────────────────────────────────────────
# ⭐ 2026-11-02 (T32, ADR-237): PORTADO de FOL (su [G], ADR-072 de este repo; su [G.2], 2026-09-23). Ningún control de RPP
# miraba lo que un docstring AFIRMA QUE FALTA: el patrón de FOL daba 137 líneas en 14 ficheros de RPP (la auditoría,
# T32), 48 en D3ChainDotPrf.lean, que anunciaba pendiente lo que ya era teorema.
# [G] (el de FOL, con la forma de RPP): una deuda se ENUNCIA como `Prop` —en RPP, `abbrev DEUDA_X : Prop :=` o
# `def X : Prop :=`, sin binders— y se paga con un `theorem W : X :=` sin binders delante (un consumidor con hipótesis no
# paga nada). Si el docstring de la deuda la anuncia ABIERTA (⬜, «DEUDA» como palabra, «no está hecha»…, «sin probar»,
# «sin modelo») sin decir que está PAGADA, y ya tiene ese testigo, ROJO: se corrige la CABECERA, no el teorema.
# (La afirmación de que la CONSISTENCIA sigue sin probar —CRI-05 de la auditoría— la vigila [I], que es donde están las
# frases que un teorema vivo desmiente: su regla de `consistencia`.)
echo ""
echo "════ [G] DEUDAS ENUNCIADAS QUE YA TIENEN TESTIGO — ROJO (T32, ADR-237) ════"
G_SRC="ROBINSON_PlusPlus"
G_DEBT="⬜|DEUDAS?([^_A-Za-z0-9]|$)|[Nn]o está hecha|[Nn]o está hecho|NO se paga aquí|[Nn]o existe nada|sin probar|sin modelo"
G_PAID="PAGADA|PAGADO|RESUELTA|RESUELTO|SALDADA|SALDADO|🏁"
G_FAIL=0
G_PROPS=$(mktemp)
grep -rnE "^(def|abbrev) +[A-Za-z_][A-Za-z0-9_'₀₁₂ⁿ]* *: *Prop" $G_SRC --include=*.lean > "$G_PROPS" 2>/dev/null
G_NPROPS=$(grep -c . "$G_PROPS"); G_NPROPS=${G_NPROPS:-0}
G_NDEBT=0
while IFS= read -r gp; do
  [ -z "$gp" ] && continue
  GF=${gp%%:*}; grest=${gp#*:}; GL=${grest%%:*}
  GNAME=$(printf '%s' "$grest" | sed 's/^[0-9]*://' | awk '{print $2}')
  [ -z "$GNAME" ] && continue
  # el docstring INMEDIATAMENTE anterior, hasta su `-/` (no hasta una línea en blanco: un docstring largo las lleva)
  gi=$((GL-1)); GBLK=""
  while [ "$gi" -gt 0 ]; do
    gln=$(sed -n "${gi}p" "$GF")
    case "$gln" in *"-/"*) [ -n "$GBLK" ] && break ;; esac
    GBLK="$gln
$GBLK"; gi=$((gi-1))
    [ $((GL-gi)) -gt 40 ] && break
  done
  # ⚠️ LC_ALL=C: el grep 3.0 de msys, en UTF-8, NO casa 🏁 (fuera del plano básico); el de la CI sí. Byte a byte, igual
  # en los dos (los patrones no llevan multibyte dentro de corchetes).
  printf '%s' "$GBLK" | LC_ALL=C grep -qE "$G_DEBT" || continue
  G_NDEBT=$((G_NDEBT + 1))
  printf '%s' "$GBLK" | LC_ALL=C grep -qE "$G_PAID" && continue
  GWIT=$(grep -rnE "^(private +|protected +)?theorem +[A-Za-z_][A-Za-z0-9_'₀₁₂ⁿ.]* *: *$GNAME *:=" $G_SRC --include=*.lean 2>/dev/null | head -1)
  if [ -n "$GWIT" ]; then
    echo "  ❌ $GF:$GL — \`$GNAME\` se anuncia como DEUDA y YA TIENE TESTIGO INCONDICIONAL:"
    echo "        $(printf '%s' "$GWIT" | cut -c1-130)"
    G_FAIL=1
  fi
done < "$G_PROPS"
rm -f "$G_PROPS"
if [ "$G_NPROPS" = "0" ]; then
  echo "  ❌ SIN MEDIR: no encontré ningún \`def\`/\`abbrev … : Prop\` en $G_SRC (¿cambió la forma?)."
  G_FAIL=1
elif [ "$G_FAIL" = "0" ]; then
  echo "  ✓ ninguna deuda enunciada tiene ya testigo incondicional ($G_NPROPS enunciados sin binders; $G_NDEBT con su cabecera de deuda)"
else
  echo "      ⚠️ La deuda está PAGADA y la cabecera sigue anunciándola abierta: corrige la CABECERA, no el teorema."
fi
[ "$G_FAIL" = "0" ] || FAIL=1

# ─── [G.2] CENSO DE MARCADORES DE DEUDA — ROJO, en los DOS sentidos (T32, ADR-237) ─────────────────────────────────
# [G] sólo lee el docstring pegado a un `Prop`. [G.2] mira TODO marcador de deuda de la prosa de los `.lean` de la
# librería (⬜, «DEUDA» como palabra, «no está hecha», «no medido»…) y exige que alguien lo haya MIRADO y CLASIFICADO:
#   ABIERTA   — deuda real y viva; la nota dice qué falta;
#   DIFERIDA  — se puede hacer y se decidió no hacerlo ahora; la nota dice por qué;
#   OFERTA    — no es deuda: una alternativa ofrecida al propietario;
#   HISTORIAL — el marcador cita una deuda pasada (una tabla fechada, una nota ✏️, un título de lo ya pagado); la nota
#               dice quién la pagó.
# Rompe en los DOS sentidos: un marcador sin fila, ROJO (clasifícalo); una fila que ya no casa, ROJO (la deuda se pagó o
# el texto cambió); un ancla que casa dos veces, ROJO (ambigua: no se absuelve por subcadena).
# ⚠️ Diferencia con FOL: «DEUDA» cuenta como PALABRA, no dentro de un identificador. Los `DEUDA_X` de RPP son los
# enunciados mismos —y sus pagos—, código y no prosa (con el patrón de FOL eran 112 de las 135 líneas); de ellos se ocupa
# [G]. Medido el 2026-11-02: 23 marcadores en 7 ficheros, los 23 HISTORIAL.
echo ""
echo "════ [G.2] CENSO DE MARCADORES DE DEUDA — ROJO (T32, ADR-237) ════"
G2_SRC="ROBINSON_PlusPlus"
G2_PAT="⬜|DEUDAS?([^_A-Za-z0-9]|$)|[Nn]o está hecha|[Nn]o está hecho|NO se paga aquí|[Nn]o existe nada|ÚNICA DEUDA|[Nn]o medido|[Nn]o está medid[oa]|[Nn]o están medid[oa]s"
G2_FAIL=0
G2_TAB=$(mktemp); G2_CUR=$(mktemp)
# ── LA TABLA ──  fichero § ancla (subcadena ÚNICA entre los marcadores de ese fichero) § clase § nota
cat > "$G2_TAB" <<'G2EOF'
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§sus «queda», «falta» y ⬜ son registro§HISTORIAL§la nota de cabecera (ADR‑134): D3 es teorema, `d3_prf_real`
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§⬜ `pcc_eval_lenc` ya existe§HISTORIAL§la tabla de §3 es del 2026‑09‑10; `pcc_eval_lenc` existe
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§`hbody` (a) · reflexión§HISTORIAL§los siete reflectores, C3 cerrado (`pcc_lineWF_tracked`, 2026‑09‑10)
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§`hbody` (b) · reflexión de `boundedPremsIn`§HISTORIAL§`premsBody_deuda` (`Meta/PremsBdAllPrf.lean`) la paga
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§registro — las dos ⬜ están pagadas§HISTORIAL§la nota de ADR‑134: `hPsiId` en §11, `hbody` en `d3_prf_real`
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§| **`hPsiId`** | ⬜ ver abajo |§HISTORIAL§`hPsiId`, pagada en §11 (la nota de ADR‑134 de la tabla)
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§| **`hbody`** | ⬜ el contenido real§HISTORIAL§`hbody`, pagada: `d3_prf_real` (la nota de ADR‑134 de la tabla)
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§⬜ **no depende de C3**§HISTORIAL§la tabla de §12.1 es del 2026‑09‑10; D3 está demostrada (`d3_prf_real`)
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§**`hbody`**(a) — reflexión§HISTORIAL§los siete reflectores, C3 cerrado (`pcc_lineWF_tracked`)
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§**`hbody`**(b) — reflexión de `boundedPremsIn`§HISTORIAL§`premsBody_deuda` la paga
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§| **(a)** reflexión de `lineWF`§HISTORIAL§los siete reflectores, `ind` y `listInd` incluidos (C3 cerrado, 2026‑09‑10)
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§| **(b)** reflexión de `boundedPremsIn` | ⬜ núcleo probado sobre argumentos ABSTRACTOS§HISTORIAL§`premsBody_deuda` la ensambla
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§con B1 aún ⬜§HISTORIAL§la propia frase fecha las dos tablas (2026‑09‑10); `d3_prf_real` cierra D3
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§⬜ **tres** piezas nombradas§HISTORIAL§la tabla del 2026‑09‑10 (§13); las tres piezas están, `d3_prf_real`
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§· **B1** ⬜ ·§HISTORIAL§la tabla del 2026‑09‑10 (§13); B1 pagada (`d3_prf_real`)
ROBINSON_PlusPlus/Meta/DiagonalTwo.lean§sigue ⬜.)§HISTORIAL§nota fechada el 2026‑10‑14; Rosser está demostrado desde ADR‑157 (`Meta/Rosser.lean`)
ROBINSON_PlusPlus/Meta/EvalLiftfcPrf.lean§LA DEUDA, ENUNCIADA (cero `axiom`)§HISTORIAL§`DEUDA_evalLiftfc`, pagada por `pcc_eval_liftfc` (§11)
ROBINSON_PlusPlus/Meta/EvalLiftfcPrf.lean§LA OTRA DEUDA DE `liftfc`§HISTORIAL§`DEUDA_hasWitF_liftfc`, pagada por `deuda_hasWitF_liftfc` (`Meta/LiftfcWitnessPrf.lean`)
ROBINSON_PlusPlus/Meta/EvalLiftfcPrf.lean§**LA DEUDA**, 🏁 **SALDADA el 2026‑09‑10**§HISTORIAL§la misma línea dice que está saldada
ROBINSON_PlusPlus/Meta/HasWitFTrackedPrf.lean§`hGuard` SIN DEUDAS.§HISTORIAL§el título de un resultado: `hGuard` sin las dos deudas de `Meta/LineWFGuardPrf.lean`
ROBINSON_PlusPlus/Meta/LiftfcWitnessPrf.lean§🏁 **LA DEUDA, SALDADA.**§HISTORIAL§la misma línea dice que está saldada
ROBINSON_PlusPlus/Meta/LineWFGuardPrf.lean§`hGuard` CERRADA A PARTIR DE LAS DOS DEUDAS§HISTORIAL§las dos deudas las paga `Meta/HasWitFTrackedPrf.lean` (`hGuard` sin ellas)
ROBINSON_PlusPlus/Meta/SolidezVerificador.lean§decía «`⊬R ∧ ⊬¬R` sólo con `ConsistentH`, ⬜»§HISTORIAL§nota ✏️ de ADR‑175: Rosser, desde ADR‑157
G2EOF

LC_ALL=C grep -rnE "$G2_PAT" $G2_SRC --include=*.lean 2>/dev/null > "$G2_CUR"
G2_N=$(grep -c . "$G2_CUR"); G2_N=${G2_N:-0}
G2_D=$(grep -c . "$G2_TAB"); G2_D=${G2_D:-0}
# (i) cada fila declarada casa EXACTAMENTE una vez, y su clase es una de las cuatro
while IFS= read -r g2row; do
  [ -z "$g2row" ] && continue
  g2f=$(printf '%s' "$g2row" | awk -F'§' '{print $1}')
  g2a=$(printf '%s' "$g2row" | awk -F'§' '{print $2}')
  g2c=$(printf '%s' "$g2row" | awk -F'§' '{print $3}')
  case "$g2c" in ABIERTA|DIFERIDA|OFERTA|HISTORIAL) ;;
    *) echo "  ❌ $g2f — clase desconocida «$g2c» (ABIERTA, DIFERIDA, OFERTA o HISTORIAL)"; G2_FAIL=1 ;; esac
  g2hits=$(LC_ALL=C grep -F -- "$g2a" "$G2_CUR" | grep -c "^$g2f:")   # LC_ALL=C: el 🏁 de dos anclas (ver [G])
  if [ "$g2hits" = "0" ]; then
    echo "  ❌ $g2f — la fila declarada ($g2c) YA NO CASA con ningún marcador:"
    echo "        ancla: $g2a"
    echo "        ⇒ o la deuda se pagó (quita la fila) o el texto cambió (ajusta el ancla)."
    G2_FAIL=1
  elif [ "$g2hits" != "1" ]; then
    echo "  ❌ $g2f — ancla AMBIGUA ($g2hits marcadores): $g2a"
    G2_FAIL=1
  fi
done < "$G2_TAB"
# (ii) ningún marcador sin declarar, y el recuento CUADRA (cero y cero también es verde: es la meta)
if [ "$G2_N" != "$G2_D" ]; then
  echo "  ❌ marcadores en el árbol: $G2_N · filas declaradas: $G2_D"
  while IFS= read -r g2l; do
    [ -z "$g2l" ] && continue
    g2lf=${g2l%%:*}; g2found=0
    while IFS= read -r g2row; do
      [ -z "$g2row" ] && continue
      g2f=$(printf '%s' "$g2row" | awk -F'§' '{print $1}')
      [ "$g2f" = "$g2lf" ] || continue
      g2a=$(printf '%s' "$g2row" | awk -F'§' '{print $2}')
      case "$g2l" in *"$g2a"*) g2found=1; break ;; esac
    done < "$G2_TAB"
    [ "$g2found" = "0" ] && echo "        SIN DECLARAR → $(printf '%s' "$g2l" | cut -c1-118)"
  done < "$G2_CUR"
  G2_FAIL=1
fi
G2_AB=$(awk -F'§' '$3 == "ABIERTA"' "$G2_TAB" | grep -c .); G2_AB=${G2_AB:-0}
rm -f "$G2_TAB" "$G2_CUR"
if [ -z "$(find $G2_SRC -name '*.lean' 2>/dev/null | head -1)" ]; then
  echo "  ❌ SIN MEDIR: no hay ningún .lean en $G2_SRC."
  G2_FAIL=1
elif [ "$G2_FAIL" = "0" ]; then
  echo "  ✓ los $G2_N marcadores de deuda están TODOS clasificados ($G2_AB abiertos)"
else
  echo "      ⚠️ Un marcador sin clasificar es una deuda que nadie ha mirado: clasifícalo en la TABLA de [G.2]."
fi
[ "$G2_FAIL" = "0" ] || FAIL=1


# ─── [P] FOOTPRINTS EN LA PROSA — ROJO, con trinquete en los DOS sentidos (T39, ADR-240) ─────────────────────────────
# ⭐ 2026-11-02 (T39, ADR-240). Los `.lean` de FOL y de RPP publican footprints en su PROSA («`lindenbaum_lemma₀` y
# `henkin_completion₀` miden `[propext, Quot.sound]`»), y nadie los comparaba con lo medido: `check-footprints.bash`
# vigila sus FILAS, no lo que dice un docstring. Medido el 2026-11-02: un docstring de RPP llevaba desde ADR-189 (T61) un
# `Classical.choice` que su fila ya no tenía (`prf_hasWitF_liftfc`; corregido el mismo día).
# Qué compara: cada lista entre corchetes de `propext`, `Quot.sound` y `Classical.choice` de `../FOL/FOL/`,
# `../FOL/TheoryFramework/` y `ROBINSON_PlusPlus/`, con cada cita entre comillas invertidas de SU TRAMO (lo que va desde el
# último «; », «. », «— » o «(» de la línea hasta la lista) que tenga fila en la TABLA de `check-footprints.bash` (por su
# nombre entero o por un final de nombre que sólo tenga una fila). Si no coinciden, es una DISCREPANCIA.
# ⚠️ Lo que NO mira: una cita y su lista en líneas distintas, y las frases sin corchetes («ningún axioma», que a menudo
# quiere decir «ningún `axiom` del proyecto»). Es un cruce por tramo: puede emparejar mal, y para eso está la tabla.
# 🔑 El trinquete, como el de [G.2]: cada discrepancia tiene su fila, clasificada (HISTORIAL: el texto cuenta lo que se
# medía antes; ATRIBUCION: el cruce empareja la lista con una cita a la que no se refiere), y cada fila casa con una
# discrepancia de hoy, por fichero, cita y lista (no por número de línea). Una discrepancia que sea un error de hoy no se
# declara: se corrige el texto.
echo ""
echo "════ [P] FOOTPRINTS EN LA PROSA — ROJO, trinquete (T39, ADR-240) ════"
P_FAIL=0
P_FILAS=$(mktemp); P_TAB=$(mktemp); P_HOY=$(mktemp); P_AUTO=$(mktemp -d)
LC_ALL=C awk "/^read -r -d '' TABLA <<'EOF'/{f=1;next} f&&/^EOF\$/{exit} f" check-footprints.bash > "$P_FILAS" 2>/dev/null
P_AWK='
function norm(s,   n, z, i, j, t, out) {
  gsub(/[][` ]/, "", s); n = split(s, z, ",")
  for (i = 1; i <= n; i++) for (j = i + 1; j <= n; j++) if (z[j] < z[i]) { t = z[i]; z[i] = z[j]; z[j] = t }
  out = ""; for (i = 1; i <= n; i++) if (z[i] != "") out = out (out == "" ? "" : ",") z[i]
  return out == "" ? "-" : out }
BEGIN { FP = "\\[(propext|Quot[.]sound|Classical[.]choice)(, *(propext|Quot[.]sound|Classical[.]choice))*\\]"
  while ((getline l < FILAS) > 0) { if (split(l, p, "|") < 2) continue; nm = p[1]; full[nm] = norm(p[2] == "-" ? "" : p[2])
    k = nm; while (sub(/^[^.]*[.]/, "", k)) { if ((k in suf) && suf[k] != nm) amb[k] = 1; suf[k] = nm } } }
{ linea = $0; resto = linea; base = 0
  while (match(resto, FP)) {
    ms = RSTART; ml = RLENGTH; fp = norm(substr(resto, ms, ml)); seg = substr(linea, 1, base + ms - 1)
    while (match(seg, /(; |[.] |— |\()/)) seg = substr(seg, RSTART + RLENGTH)
    while (match(seg, /`[^` ]+`/)) {
      id = substr(seg, RSTART + 1, RLENGTH - 2); seg = substr(seg, RSTART + RLENGTH)
      nm = (id in full) ? id : (((id in suf) && !(id in amb)) ? suf[id] : "")
      if (nm == "") continue
      pares++
      if (full[nm] != fp) print FILENAME "§" FNR "§" id "§" fp "§" nm "§" full[nm]
    }
    base += ms + ml - 1; resto = substr(resto, ms + ml) } }
END { print "PARES§" pares + 0 }'
# autotest de salida exacta: una cita que cuadra, una que no, una por su final de nombre, un final ambiguo, dos citas
# con una lista, una lista sin cita, una cita de OTRO tramo, y una lista de una línea con dos tramos
printf '%s\n' 'A.B.bien|propext' 'A.B.mal|-' 'A.C.amb|-' 'A.D.amb|-' 'A.E.dos|Quot.sound,propext' 'A.E.tres|Quot.sound,propext' \
  'A.F.lejos|-' > "$P_AUTO/filas"
printf '%s\n' '`A.B.bien`, `[propext]`.' '`mal` mide `[propext, Quot.sound]`.' '`amb`, `[propext]`.' \
  '`dos` y `tres` miden `[propext, Quot.sound]`.' 'A lo sumo `[Classical.choice]` en todo el módulo.' \
  '`lejos` no; en cambio `[propext]`.' '`bien`, `[propext]`; `mal`, `[propext, Classical.choice, Quot.sound]`.' > "$P_AUTO/doc.lean"
P_AUTO_SAL=$( (cd "$P_AUTO" && LC_ALL=C awk -v FILAS=filas "$P_AWK" doc.lean) | tr '\n' ';')
P_AUTO_OK='doc.lean§2§mal§Quot.sound,propext§A.B.mal§-;doc.lean§7§mal§Classical.choice,Quot.sound,propext§A.B.mal§-;PARES§6;'
# ── LA TABLA ──  fichero § cita (tal cual en el texto) § la lista de la prosa (ordenada) § clase § nota
cat > "$P_TAB" <<'PEOF'
../FOL/FOL/Compacity0.lean§evalTerm_updateCsts§Quot.sound,propext§HISTORIAL§«medidos (con `String`)»: D7 la dejó en ningún axioma, y lo dice la nota ✏️ de debajo
../FOL/FOL/Rename.lean§derives0_rename_conservative§Classical.choice,Quot.sound,propext§HISTORIAL§«Hasta el 2026‑09‑27 aquí decía»: la nota de la auditoría de constructividad
PEOF
P_FICH=$( { find ../FOL/FOL ../FOL/TheoryFramework -name '*.lean' 2>/dev/null; find ROBINSON_PlusPlus -name '*.lean' 2>/dev/null; } | LC_ALL=C sort)
if [ "$P_AUTO_SAL" != "$P_AUTO_OK" ]; then
  echo "  ❌ NO PUDE MEDIR [P]: el autotest no da lo esperado ($P_AUTO_OK), da: $P_AUTO_SAL"; P_FAIL=1
elif [ "$(grep -c '|' "$P_FILAS")" -lt 100 ]; then
  echo "  ❌ NO PUDE MEDIR [P]: la TABLA de check-footprints.bash da $(grep -c '|' "$P_FILAS") filas (¿cambió su forma?)."; P_FAIL=1
elif ! printf '%s\n' "$P_FICH" | grep -q '^\.\./FOL/FOL/' || ! printf '%s\n' "$P_FICH" | grep -q '^ROBINSON_PlusPlus/'; then
  echo "  ❌ NO PUDE MEDIR [P]: faltan los .lean de ../FOL o de ROBINSON_PlusPlus."; P_FAIL=1
elif ! printf '%s\n' "$P_FICH" | tr '\n' '\0' | xargs -0 env LC_ALL=C awk -v FILAS="$P_FILAS" "$P_AWK" > "$P_HOY"; then
  echo "  ❌ NO PUDE MEDIR [P]: el awk falló."; P_FAIL=1
else
  # (xargs puede partir la lista: los PARES se suman)
  P_PARES=$(LC_ALL=C awk -F'§' '$1 == "PARES" { s += $2 } END { print s + 0 }' "$P_HOY")
  P_DIS=$(LC_ALL=C grep -v '^PARES§' "$P_HOY")
  if [ "$P_PARES" = "0" ]; then
    echo "  ❌ NO PUDE MEDIR [P]: ninguna cita con footprint casa con una fila (¿cambió la forma de la prosa o de la tabla?)."; P_FAIL=1
  fi
  # (i) cada fila de la tabla casa con EXACTAMENTE una discrepancia de hoy, y su clase es una de las dos
  while IFS= read -r prow; do
    [ -z "$prow" ] && continue
    pf=$(printf '%s' "$prow" | LC_ALL=C awk -F'§' '{print $1}'); pc=$(printf '%s' "$prow" | LC_ALL=C awk -F'§' '{print $2}')
    pl=$(printf '%s' "$prow" | LC_ALL=C awk -F'§' '{print $3}'); pk=$(printf '%s' "$prow" | LC_ALL=C awk -F'§' '{print $4}')
    case "$pk" in HISTORIAL|ATRIBUCION) ;; *) echo "  ❌ $pf — clase desconocida «$pk» (HISTORIAL o ATRIBUCION)"; P_FAIL=1 ;; esac
    pn=$(printf '%s\n' "$P_DIS" | LC_ALL=C awk -F'§' -v f="$pf" -v c="$pc" -v l="$pl" '$1 == f && $3 == c && $4 == l' | grep -c .)
    if [ "$pn" = "0" ]; then
      echo "  ❌ $pf — la fila declarada ($pk) YA NO CASA: \`$pc\` con [$pl]. ⇒ el texto cambió o la fila de la TABLA: quita la fila."; P_FAIL=1
    elif [ "$pn" != "1" ]; then
      echo "  ❌ $pf — la fila declarada casa con $pn discrepancias: \`$pc\` con [$pl] (ambigua)."; P_FAIL=1
    fi
  done < "$P_TAB"
  # (ii) ninguna discrepancia sin su fila
  P_SIN=$(printf '%s\n' "$P_DIS" | grep . | while IFS= read -r pd; do
    pf=$(printf '%s' "$pd" | LC_ALL=C awk -F'§' '{print $1 "§" $3 "§" $4}')
    LC_ALL=C awk -F'§' '{print $1 "§" $2 "§" $3}' "$P_TAB" | grep -qxF -- "$pf" || printf '%s\n' "$pd"
  done)
  if [ -n "$P_SIN" ]; then
    printf '%s\n' "$P_SIN" | LC_ALL=C awk -F'§' '{ printf "  ❌ %s:%s — `%s` dice [%s] y su fila (%s) dice [%s]\n", $1, $2, $3, $4, $5, $6 }'
    echo "      ⇒ si el texto afirma el footprint de HOY, corrígelo; si cuenta el de antes, márcalo y declara la fila en la tabla de [P]."
    P_FAIL=1
  fi
  [ "$P_FAIL" = "0" ] && echo "  ✓ $P_PARES citas con footprint en la prosa (FOL, TheoryFramework y RPP), comparadas con su fila: $((P_PARES - $(grep -c . "$P_TAB"))) cuadran, y las $(grep -c . "$P_TAB") que no, declaradas"
fi
rm -rf "$P_FILAS" "$P_TAB" "$P_HOY" "$P_AUTO"
[ "$P_FAIL" = "0" ] || FAIL=1


# ─── [R] REGISTRO DE HALLAZGOS: cada ID de las auditorías, con su estado — ROJO (T37, ADR-241) ───────────────────────
# ⭐ 2026-11-02 (T37, ADR-241). Los hallazgos de las auditorías (las rondas 1, 2 y 3, los 163 candidatos del suelo y su
# crítico, las tres auditorías de ADR-121…127 y las tres viejas) vivían en sus artefactos, y en el repositorio aparecían
# identificadores sin estado. `doc/control/hallazgos.tsv` tiene una fila por ID —origen, resumen, veredicto, estado, dónde
# y evidencia—, leída contra el árbol el 2026-11-02 (las citas fichero:línea de su evidencia son de ese día: RPP 6cdd2dd,
# FOL b5c5e1c). Este bloque exige:
#   (1) que los IDs del registro sean EXACTAMENTE los que se extraen hoy de las fuentes versionadas (los JSON de
#       `doc/registro/` y las tres auditorías viejas de `doc/`), en los dos sentidos; las dos auditorías sin IDs propios
#       (A121, A123: el registro les da uno por posición) van con su lista fija y el sha256 de su fuente;
#   (2) un estado a cada fila: «hecho» con un ADR que exista (o «sin ADR: commit <sha>» / «sin ADR: FOL <sha>», de antes
#       de esa disciplina, con el commit en su repo), «sustituido» con un T de la auditoría del suelo que exista,
#       «pendiente» con «sin dueño» o un T que exista, «descartado» con su razón; y que todo ADR-NNN y todo Txx que nombre
#       la columna «dónde» exista.
# Lo que NO mira: que el estado sea CIERTO (eso es leer el ADR), ni la evidencia, que es texto de su día.
echo ""
echo "════ [R] REGISTRO DE HALLAZGOS — ROJO (T37, ADR-241) ════"
R_FAIL=0
R_TSV=doc/control/hallazgos.tsv
R_DIR=$(mktemp -d)
R_REG=doc/registro
# los IDs de las fuentes, como los escribe el registro (el guion U+2011 de los .md, a «-»). Cada fuente nombra un ID
# varias veces (el hallazgo y su verificación): `sort -u` POR FUENTE; un ID que salga de dos fuentes es una colisión.
r_extrae() {
  LC_ALL=C grep -oE '"id": "L[1-5]-[0-9]{1,2}"' "$R_REG/2026-10-02-auditoria-base/ronda1/salida_workflow_ronda1.json" | cut -d'"' -f4 | LC_ALL=C sort -u
  LC_ALL=C grep -oE '"id": "(R2-[1-5]-[0-9]{1,2}|R22-[0-9]{1,2})"' "$R_REG/2026-10-02-auditoria-base/ronda2/salida_workflow_ronda2.json" | cut -d'"' -f4 | LC_ALL=C sort -u
  LC_ALL=C grep -oE '"id": "R3-[1-5]-(H[0-9]|[0-9]{2})"' "$R_REG/2026-10-28-ronda3/resultado.json" | cut -d'"' -f4 | LC_ALL=C sort -u
  LC_ALL=C awk -F'"' '/^  "dim": /{ d = $4 } /^  "id": /{ p = (d == "medida") ? "MED" : (d == "fundamentos") ? "FUN" : (d == "subterraneo") ? "SUB" : (d == "ruta") ? "RUT" : (d == "fol") ? "FOL" : "DOC"; print p ":" $4 }' \
    "$R_REG/2026-10-12-auditoria-suelo/candidatos.json" | LC_ALL=C sort -u
  LC_ALL=C grep -oE '"id":"CRI-[0-9]{2}"' "$R_REG/2026-10-12-auditoria-suelo/workflow-cierre.json" | cut -d'"' -f4 | LC_ALL=C sort -u
  LC_ALL=C grep -oE '\\n\*\*C[0-9]+\.' "$R_REG/2026-10-05-auditoria-adr124-126/workflow.json" | LC_ALL=C sed 's/^\\n\*\*/A124:/; s/\.$//' | LC_ALL=C sort -u
  LC_ALL=C grep -oE '\\nC[0-9]+\. ' "$R_REG/2026-10-05-auditoria-adr124-126/workflow.json" | LC_ALL=C sed 's/^\\n/A125:/; s/\. $//' | LC_ALL=C sort -u
  LC_ALL=C grep -E '^### F(-|‑)[0-9]+b? · ' doc/AUDITORIA-2026-09-11.md | LC_ALL=C sed 's/^### //; s/ · .*//; s/‑/-/' | LC_ALL=C sort -u
  LC_ALL=C grep -E '^\*\*[AMBRD](-|‑)[0-9]+ · ' doc/AUDITORIA-FOL-2026-09-12.md | LC_ALL=C sed 's/^\*\*//; s/ · .*//; s/‑/-/; s/^/FOL0912:/' | LC_ALL=C sort -u
  LC_ALL=C grep -E '^### [AG][0-9] · ' doc/AUDITORIA-2026-09-18.md | LC_ALL=C sed 's/^### //; s/ · .*//; s/^/AUD0918:/' | LC_ALL=C sort -u
  # sin IDs propios en su fuente: la lista fija del registro, y el sha256 de la fuente (si cambia, se vuelve a mirar)
  printf 'A121:%s\n' G1 G2 G3 G4 G5 G6 G7 G8 W1 W2 W3 W4 W5 W6 W7 T1 T2 T3 T4 T5 T6 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10
  printf 'A123:%s\n' R1 R2 R3 R4 R5 R6 R7 R8 R9 D1 D2 S1
  # (sin fuente versionada: la auditoría del 2026-09-28, que citan ADR-114…118)
  echo AUD0928:F1
}
R_SHA_A121=64e0959c7a158850e75be82287c90d2ed2e4bffd2d6502df81b9863a1bd86bc3
R_SHA_A123=28f8b89e1940b5065def7e3e38674929556d1520a0bd0380a51bb034f70d5229
# la comprobación de cada fila (awk): campos, estado, y lo que nombra «dónde»; ARGV[1] los ADR que existen, ARGV[2] los T
R_AWK='
FILENAME == ARGV[1] { adr[$0] = 1; next }
FILENAME == ARGV[2] { t[$0] = 1; next }
FNR == 1 { next }
{ id = $1; e = $5; d = $6
  if (NF != 7) { print id ": " NF " campos (son 7)"; next }
  if (e != "hecho" && e != "pendiente" && e != "descartado" && e != "sustituido") { print id ": estado «" e "» (hecho, pendiente, descartado o sustituido)"; next }
  if (d == "") { print id ": «dónde» vacío"; next }
  r = d; while (match(r, /ADR-[0-9]+/)) { a = substr(r, RSTART, RLENGTH); r = substr(r, RSTART + RLENGTH); if (!(a in adr)) print id ": " a " no existe" }
  r = d; while (match(r, /(^|[^A-Za-z0-9_])T[0-9][0-9][a-z]?([^A-Za-z0-9_]|$)/)) { x = substr(r, RSTART, RLENGTH); r = substr(r, RSTART + RLENGTH - 1)
    gsub(/[^A-Za-z0-9]/, "", x); if (!(x in t)) print id ": " x " no es un T de la auditoría" }
  if (e == "hecho" && d !~ /^ADR-[0-9]+/ && d !~ /^sin ADR: (commit|FOL) [0-9a-f]+$/) print id ": «hecho» sin ADR (ni «sin ADR: commit <sha>»)"
  if (e == "sustituido" && d !~ /(^|[^A-Za-z0-9_])T[0-9][0-9][a-z]?([^A-Za-z0-9_]|$)/) print id ": «sustituido» sin el T que lo absorbe"
  if (e == "pendiente" && d !~ /^sin dueño/ && d !~ /(^|[^A-Za-z0-9_])T[0-9][0-9][a-z]?([^A-Za-z0-9_]|$)/) print id ": «pendiente» sin dueño ni T"
  if (e == "hecho" && d ~ /^sin ADR: /) { n = split(d, z, " "); print "SHA\t" id "\t" z[3] "\t" z[4] } }'
# autotest de salida exacta: una fila de cada fallo
printf '%s\n' ADR-001 ADR-120 > "$R_DIR/adr"; printf '%s\n' T10 T61b > "$R_DIR/t"
{ printf 'id\torigen\tresumen\tveredicto\testado\tdónde\tevidencia\n'
  printf 'X1\to\tr\tv\thecho\tADR-120\te\n'
  printf 'X2\to\tr\tv\thecho\tADR-999\te\n'
  printf 'X3\to\tr\tv\tcerrado\tADR-120\te\n'
  printf 'X4\to\tr\tv\tpendiente\t\te\n'
  printf 'X5\to\tr\tv\tsustituido\tT99\te\n'
  printf 'X6\to\tr\tv\tsustituido\tT61b (y ADR-001)\te\n'
  printf 'X7\to\tr\tv\thecho\tsin ADR: commit abc1234\te\n'
  printf 'X8\to\tr\tv\tpendiente\tya veremos\te\n'
  printf 'X9\to\tr\tv\thecho\tla nota de ADR-120\te\n'
  printf 'X10\to\tr\n'; } > "$R_DIR/tsv"
R_AUTO=$(cd "$R_DIR" && LC_ALL=C awk -F'\t' "$R_AWK" adr t tsv | tr '\t\n' '|;')
R_AUTO_OK='X2: ADR-999 no existe;X3: estado «cerrado» (hecho, pendiente, descartado o sustituido);X4: «dónde» vacío;X5: T99 no es un T de la auditoría;SHA|X7|commit|abc1234;X8: «pendiente» sin dueño ni T;X9: «hecho» sin ADR (ni «sin ADR: commit <sha>»);X10: 3 campos (son 7);'
if [ "$R_AUTO" != "$R_AUTO_OK" ]; then
  echo "  ❌ NO PUDE MEDIR [R]: el autotest no da lo esperado ($R_AUTO_OK), da: $R_AUTO"; R_FAIL=1
elif [ ! -f "$R_TSV" ]; then
  echo "  ❌ falta $R_TSV."; R_FAIL=1
else
  r_extrae 2>/dev/null | LC_ALL=C sort > "$R_DIR/fuentes"
  LC_ALL=C awk -F'\t' 'NR > 1 { print $1 }' "$R_TSV" | LC_ALL=C sort > "$R_DIR/registro"
  R_NF=$(grep -c . "$R_DIR/fuentes"); R_NR=$(grep -c . "$R_DIR/registro")
  R_DUP=$(LC_ALL=C uniq -d "$R_DIR/registro"); R_DUPF=$(LC_ALL=C uniq -d "$R_DIR/fuentes")
  [ -n "$R_DUP" ] && { echo "  ❌ IDs repetidos en $R_TSV: $(printf '%s ' $R_DUP)"; R_FAIL=1; }
  [ -n "$R_DUPF" ] && { echo "  ❌ IDs que salen de DOS fuentes (una colisión: ¿cambió una?): $(printf '%s ' $R_DUPF)"; R_FAIL=1; }
  R_FALTAN=$(LC_ALL=C comm -23 "$R_DIR/fuentes" "$R_DIR/registro"); R_SOBRAN=$(LC_ALL=C comm -13 "$R_DIR/fuentes" "$R_DIR/registro")
  [ -n "$R_FALTAN" ] && { echo "  ❌ IDs de las fuentes SIN FILA en $R_TSV: $(printf '%s ' $R_FALTAN)"; R_FAIL=1; }
  [ -n "$R_SOBRAN" ] && { echo "  ❌ filas de $R_TSV que NO SALEN de ninguna fuente: $(printf '%s ' $R_SOBRAN)"; R_FAIL=1; }
  for p in "A121 $R_REG/2026-10-05-auditoria-adr120-121/workflow.json $R_SHA_A121" "A123 $R_REG/2026-10-05-auditoria-adr123/workflow.json $R_SHA_A123"; do
    set -- $p
    [ "$(sha256sum "$2" 2>/dev/null | cut -c1-64)" = "$3" ] \
      || { echo "  ❌ la fuente de $1 ($2) cambió (o falta): su lista fija ya no vale; vuelve a leerla."; R_FAIL=1; }
  done
  if [ "$R_NF" -lt 400 ]; then echo "  ❌ NO PUDE MEDIR [R]: las fuentes dan $R_NF IDs (¿cambió su forma?)."; R_FAIL=1; fi
  # los ADR que existen (los de hoy y los de antes de ADR-131, en el histórico) y los T de la auditoría
  LC_ALL=C grep -ohE '^## ADR-[0-9]+' DECISIONS.md doc/historia/DECISIONS-001-130.md 2>/dev/null | cut -c4- | LC_ALL=C sort -u > "$R_DIR/adr"
  LC_ALL=C grep -oE '^#### T[0-9][0-9][a-z]? ' doc/AUDITORIA-SUELO-2026-10-12.md | LC_ALL=C sed 's/^#### //; s/ $//' | LC_ALL=C sort -u > "$R_DIR/t"
  if [ "$(grep -c . "$R_DIR/adr")" -lt 200 ] || [ "$(grep -c . "$R_DIR/t")" -lt 80 ]; then
    echo "  ❌ NO PUDE MEDIR [R]: $(grep -c . "$R_DIR/adr") ADR y $(grep -c . "$R_DIR/t") T (¿cambió la forma de DECISIONS.md o de la auditoría?)."; R_FAIL=1
  else
    R_MAL=$(LC_ALL=C awk -F'\t' "$R_AWK" "$R_DIR/adr" "$R_DIR/t" "$R_TSV")
    R_SHAS=$(printf '%s\n' "$R_MAL" | grep '^SHA	'); R_MAL=$(printf '%s\n' "$R_MAL" | grep -v '^SHA	' | grep .)
    if [ -n "$R_MAL" ]; then printf '%s\n' "$R_MAL" | head -20 | sed 's/^/  ❌ /'; R_FAIL=1; fi
    # «sin ADR: commit <sha>» en RPP, «sin ADR: FOL <sha>» en ../FOL: el commit existe
    while IFS="$(printf '\t')" read -r _ rid rk rsha; do
      [ -z "$rid" ] && continue
      if [ "$rk" = "FOL" ]; then
        [ -d ../FOL/.git ] || { echo "  ❌ NO PUDE MEDIR [R]: $rid cita un commit de FOL y no está ../FOL."; R_FAIL=1; continue; }
        git -C ../FOL cat-file -e "$rsha^{commit}" 2>/dev/null || { echo "  ❌ $rid: el commit $rsha no está en FOL."; R_FAIL=1; }
      else
        git cat-file -e "$rsha^{commit}" 2>/dev/null || { echo "  ❌ $rid: el commit $rsha no está en RPP."; R_FAIL=1; }
      fi
    done <<< "$R_SHAS"
  fi
  if [ "$R_FAIL" = "0" ]; then
    R_EST=$(LC_ALL=C awk -F'\t' 'NR > 1 { n[$5]++ } END { printf "%d hechos, %d pendientes, %d descartados, %d sustituidos", n["hecho"], n["pendiente"], n["descartado"], n["sustituido"] }' "$R_TSV")
    echo "  ✓ los $R_NR IDs de las auditorías tienen su fila y su estado, y son los de sus fuentes ($R_EST)"
  fi
fi
rm -rf "$R_DIR"
[ "$R_FAIL" = "0" ] || FAIL=1


# ─── [S] LAS CITAS DE SONDEOS DEL BUILD: EVIDENCIA O PROCEDENCIA — ROJO (T10, ADR-243) ─────────────────────────────────
# ⭐ 2026-11-02 (T10, ADR-243). Los `.lean` del build citan sondeos (`sondeos/X.lean`) de dos maneras que se confundían:
# como EVIDENCIA («lo refuta `sondeos/X.lean`») y como PROCEDENCIA («promovido de», «copia de», «lo que probó en su día»).
# La auditoría (T10) midió 89 de 114 citas a sondeos que no compilaban, y tres que decían en presente que uno «probó»
# algo. Desde ADR-141 cada sondeo tiene clase (CONTROL, REGISTRO, REPARAR, ARCHIVADO; `sondeos/README.md`). La regla:
#   · una cita a un sondeo de CONTROL (`sondeos/CONTROLES.txt`, que la CI compila en cada push) puede ser evidencia;
#   · una cita a un sondeo ARCHIVADO lleva su etiqueta (`archivo/sondeos-2026-10:sondeos/X.lean`), y el fichero tiene que
#     estar en ella;
#   · una cita a cualquier otro sondeo del árbol (REGISTRO, REPARAR) es PROCEDENCIA, y está DECLARADA en la tabla de
#     abajo, por fichero y sondeo con su número de citas: alguien la leyó y vio que no sostiene nada de hoy. Una que sí lo
#     sostenga no se declara: el sondeo pasa a CONTROL;
#   · una cita a un sondeo que no está en el árbol ni en su etiqueta, ROJO.
# La tabla rompe en los DOS sentidos, como la de [G.2]: una cita nueva sin fila, o una fila que ya no cuadra, ROJO.
echo ""
echo "════ [S] CITAS DE SONDEOS DEL BUILD: EVIDENCIA O PROCEDENCIA — ROJO (T10, ADR-243) ════"
S_FAIL=0
S_TAB=$(mktemp); S_HOY=$(mktemp)
# ── LA TABLA ──  fichero § sondeo (sin `.lean`) § citas § por qué es procedencia
cat > "$S_TAB" <<'SEOF'
ROBINSON_PlusPlus/Meta/CodeWitnessPrf.lean§AcotarEsLaMismaObligacion§1§los consumidores de la firma que quedan en el sondeo
ROBINSON_PlusPlus/Meta/D3ChainDotPrf.lean§A3IsFCBTracked§2§lo que aplicó y lo que no necesitó en su día (nota ✏️ de ADR‑134; REPARAR: no compila)
ROBINSON_PlusPlus/Meta/HasWitTrackedPrf.lean§A3IsFCBTracked§3§lo que reflejó, su §2 citada y cómo define su PsiF (REPARAR)
ROBINSON_PlusPlus/Meta/HilbertDeduction.lean§PrfHMono§2§el rescate de la deuda B6b (2026‑09‑11) y su copia; PrfH_w1 está en el build
ROBINSON_PlusPlus/Meta/LineWFGuardPrf.lean§SegundoMuro§1§una de las copias de la pieza antes de entrar en el build
ROBINSON_PlusPlus/Meta/ModeloCodigo.lean§ModeloNat§1§de dónde se promovió el modelo (ADR‑119)
ROBINSON_PlusPlus/Meta/Rosser.lean§ExtensionPorReduccion§2§de dónde se promovió su §1 (ADR‑144)
ROBINSON_PlusPlus/Meta/RosserGuardNeg.lean§RosserHasWitF§1§el esquema de su §4, hecho general aquí
ROBINSON_PlusPlus/Meta/Sigma1AtomPrf.lean§D3Sigma1Vacuo§1§la refutación de hbI, fechada (ADR‑132); el teorema vacuo salió del build (ADR‑161)
ROBINSON_PlusPlus/Meta/Sigma1CorePrf.lean§D3Sigma1Vacuo§1§la refutación de hI, «compilado el 2026‑10‑12» (ADR‑132)
ROBINSON_PlusPlus/Meta/Sigma1Prf.lean§D3Sigma1Vacuo§1§la refutación de hI, «compilado el 2026‑10‑12» (ADR‑132)
ROBINSON_PlusPlus/Meta/SolidezPrf.lean§CantorSobreyectivo§1§de dónde se copió wN
ROBINSON_PlusPlus/Meta/SubstfcWitnessPrf.lean§MergeTestigos§2§de dónde se copió la fusión de testigos, y la copia que sigue fuera
ROBINSON_PlusPlus/Meta/TrackedAtomsPrf.lean§A3IsFCBTracked§3§de dónde se promovió el kit genérico, lo que probó y su idioma de bdInB (REPARAR)
SEOF
S_CTRL=$(grep -v '^#' sondeos/CONTROLES.txt 2>/dev/null | grep . | sed 's/[.]lean$//' | LC_ALL=C sort -u)
S_CITAS=$(LC_ALL=C grep -rnoE '(archivo/[A-Za-z0-9_.-]+:)?sondeos/[A-Za-z0-9_]+[.]lean' ROBINSON_PlusPlus --include=*.lean 2>/dev/null)
S_N=$(printf '%s\n' "$S_CITAS" | grep -c .); S_EV=0; S_AR=0
if [ -z "$S_CTRL" ]; then
  echo "  ❌ NO PUDE MEDIR [S]: sondeos/CONTROLES.txt vacío o ausente."; S_FAIL=1
elif [ "$S_N" -lt 20 ]; then
  echo "  ❌ NO PUDE MEDIR [S]: $S_N citas de sondeos en el build (¿cambió su forma?)."; S_FAIL=1
else
  while IFS= read -r sc; do
    [ -z "$sc" ] && continue
    sf=${sc%%:*}; sr=${sc#*:}; sl=${sr%%:*}; sm=${sr#*:}
    case "$sm" in
      archivo/*)
        st=${sm%%:sondeos/*}; sp=${sm#"$st":}
        if git cat-file -e "$st:$sp" 2>/dev/null; then S_AR=$((S_AR+1))
        else echo "  ❌ $sf:$sl — \`$sm\`: el fichero no está en esa etiqueta (¿falta un git fetch --tags?)."; S_FAIL=1; fi ;;
      *)
        sx=${sm#sondeos/}; sx=${sx%.lean}
        if printf '%s\n' "$S_CTRL" | grep -qxF -- "$sx"; then S_EV=$((S_EV+1))
        elif [ -e "$sm" ]; then printf '%s§%s\n' "$sf" "$sx" >> "$S_HOY"
        else echo "  ❌ $sf:$sl — cita \`$sm\`, que no está en sondeos/: si está archivado, cítalo con su etiqueta (\`archivo/sondeos-2026-10:$sm\`)."; S_FAIL=1; fi ;;
    esac
  done <<< "$S_CITAS"
  S_AGR=$(LC_ALL=C sort "$S_HOY" | LC_ALL=C uniq -c | LC_ALL=C awk '{ n = $1; $1 = ""; sub(/^ /, ""); print $0 "§" n }')
  S_DECL=$(LC_ALL=C awk -F'§' 'NF >= 3 { print $1 "§" $2 "§" $3 }' "$S_TAB" | LC_ALL=C sort)
  S_SIN=$(LC_ALL=C comm -23 <(printf '%s\n' "$S_AGR" | grep . | LC_ALL=C sort) <(printf '%s\n' "$S_DECL"))
  S_SOBRA=$(LC_ALL=C comm -13 <(printf '%s\n' "$S_AGR" | grep . | LC_ALL=C sort) <(printf '%s\n' "$S_DECL"))
  if [ -n "$S_SIN" ]; then
    echo "  ❌ citas a sondeos que no son de CONTROL, sin declarar como procedencia (fichero § sondeo § citas):"
    printf '%s\n' "$S_SIN" | sed 's/^/      /'
    echo "      ⇒ si la cita dice de dónde viene algo, decláralo en la tabla de [S]; si sostiene algo de HOY, el sondeo pasa a CONTROL."
    S_FAIL=1
  fi
  if [ -n "$S_SOBRA" ]; then
    echo "  ❌ filas de la tabla de [S] que ya no cuadran con el build (la cita cambió o se fue: ajusta o quita la fila):"
    printf '%s\n' "$S_SOBRA" | sed 's/^/      /'
    S_FAIL=1
  fi
  [ "$S_FAIL" = "0" ] && echo "  ✓ $S_N citas de sondeos en el build: $S_EV a sondeos de CONTROL, $S_AR a archivados con su etiqueta y $(grep -c . "$S_HOY") de procedencia, declaradas ($(grep -c . "$S_TAB") filas)"
fi
rm -f "$S_TAB" "$S_HOY"
[ "$S_FAIL" = "0" ] || FAIL=1

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
