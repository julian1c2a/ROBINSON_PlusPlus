#!/usr/bin/env bash
# check-estratos.bash — el CENSO DE ESTRATOS: por cada noción de derivabilidad, cuántos
# constructores tiene y cuántos `axiom` la HABITAN. ROMPE si no cuadra con lo declarado.
#
# ⛔⛔ POR QUÉ EXISTE (2026-09-16)
#
# El proyecto tiene CINCO nociones de derivabilidad, y hasta el 2026-09-14 nadie podía decir,
# mirando el árbol, cuál era HERRAMIENTA y cuál SUJETO. NADA medía que `Derives` estuviera
# habitado por axiomas, y con ellos en el entorno `FOL.soundness` daba `False` sin hipótesis.
#
# ✏️ 2026-10-02 (ADR-114 §2, ADR-115): aquello se leyó al revés. El recursor cubre a TODO
# habitante, también a los que fabrica un axioma: un teorema probado por inducción sobre un
# inductivo habitado es VÁLIDO (`FOL.soundness` lo era). Lo que puede ser falso es el AXIOMA:
# si contradice lo que la inducción demuestra, Lean + él ⊢ `False`. Así eran los cuatro de
# `FOL/MetaRules.lean`, borrados. M-11 («no inducir») evitaba ESCRIBIR la contradicción, no la quitaba.
#
# ⚠️ `#print axioms` NO lo ve: el footprint de un teorema probado por inducción no lleva los
#    axiomas que habitan el inductivo. Por eso hace falta este censo aparte.
#
# 🔑 Lo que este control mide: cuántos `axiom` HABITAN cada inductivo, y lo mide por el TIPO de
#    cada axioma —la cabeza de su conclusión—, no por grep sobre los nombres. Con 0, nada que se
#    demuestre por inducción puede chocar con un postulado sobre ese inductivo.
#
# ⭐ Rompe en LOS DOS SENTIDOS, y el que importa es el de subida: si alguien declara un `axiom`
#    que habita `Prfᵢ`, este control lo dice, y lo primero es comprobar que lo ya probado por
#    inducción sobre `Prfᵢ` (su solidez, por ejemplo) no lo refuta.
#
# 🔧 EJECUTAR DESDE POWERSHELL (desde Bash, `lake` no está en el PATH — y el script lo DICE).
# ⛔ Desde la raíz de ROBINSON_PlusPlus, NUNCA `cd FOL && lake ...`.
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

# ── LA TABLA DECLARADA ─────────────────────────────────────────────────────────────────────
# nombre | constructores | axiomas que lo HABITAN | teorema de solidez EN EL BUILD ('-' = ninguno)
# ⚠️ Esta tabla es la misma de `REFERENCE.md` §0bis. Si cambia una, cambian las dos.
# 2026-10-02 (ADR-115): `Derives` baja de 4 a 0 al borrarse `FOL/MetaRules.lean`, y gana su solidez
# en el build (`FOL/Inconsistencia.lean` §1).
read -r -d '' ESTRATOS <<'EOF'
Derives|22|0|FOL.Inconsistencia.derives_soundness
Derives₀|21|0|FOL.Metamath.Soundness0.derives0_soundness
Derives₁|20|0|-
Derives₂|22|0|-
LK₀|14|0|-
LKc|15|0|-
LKh|14|0|-
ROBINSON_PlusPlus.Meta.Hilbert.Prf|7|0|ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound
ROBINSON_PlusPlus.Meta.Hilbert.Prfᵢ|17|0|ROBINSON_PlusPlus.Meta.SolidezPrf.prfI_sound
ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH|8|0|-
EOF

TMP=$(mktemp -d)
LEANFILE="$TMP/Estratos.lean"
# ⛔⛔ 2026-10-03 (ADR-116): dos huecos de este censo, cerrados. (1) No importaba `TheoryFramework`, la
# otra librería del build de FOL: un `axiom` allí no lo veía nadie por entorno. Ahora se importan todos
# sus módulos, y se exige verlos (`@TF`, abajo): un import que no carga nada no es un control. (2) Saltaba
# los nombres `isInternal` también para los AXIOMAS, y un `private axiom` se llama `_private.…`: no lo
# contaba. Ahora el filtro sólo se aplica a los inductivos.
{
  echo "import Lean"
  echo "import ROBINSON_PlusPlus"
  echo "import FOL"
  for f in $(find ../FOL/TheoryFramework -name '*.lean' ! -path '*/.lake/*' 2>/dev/null | sort); do
    m="${f#../FOL/}"; m="${m%.lean}"; echo "import ${m//\//.}"
  done
  cat <<'LEANEOF'

open Lean

def esNuestro (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    (`FOL).isPrefixOf m || m == `FOL
      || (`ROBINSON_PlusPlus).isPrefixOf m || m == `ROBINSON_PlusPlus
      || (`TheoryFramework).isPrefixOf m || m == `TheoryFramework

/-- La cabeza de la CONCLUSIÓN del tipo: el inductivo que el axioma HABITA. -/
def cabeza (e : Expr) : Name :=
  match e.getForallBody.getAppFn with
  | .const c _ => c
  | _ => `desconocida

run_cmd do
  let env ← Lean.getEnv
  let mut tf := 0
  let mut nuestras := 0
  -- los tres axiomas de Lean que el proyecto acepta; cualquier OTRO axioma ajeno que use una constante
  -- nuestra (`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, …) es @TRUST
  let estandar : NameSet := ((({} : NameSet).insert ``propext).insert ``Classical.choice).insert ``Quot.sound
  for (n, ci) in env.constants.toList do
    if !(esNuestro env n) then continue
    nuestras := nuestras + 1
    if let some idx := env.getModuleIdxFor? n then
      if (`TheoryFramework).isPrefixOf env.header.moduleNames[idx.toNat]! then tf := tf + 1
    match ci with
    | .axiomInfo ax => logInfo m!"@HAB {cabeza ax.type} {n}"
    | .inductInfo ind => if !n.isInternal then logInfo m!"@CTORS {n} {ind.ctors.length}"
    | _ => pure ()
    -- tipo y valor, también el de un teorema (`getUsedConstantsAsSet` lee con `allowOpaque`)
    let usadas := ci.getUsedConstantsAsSet
    if usadas.contains ``sorryAx then logInfo m!"@SORRY {n}"
    for u in usadas do
      if let some (.axiomInfo _) := env.find? u then
        if !estandar.contains u && u != ``sorryAx && !(esNuestro env u) then logInfo m!"@TRUST {n} {u}"
    if (Lean.Compiler.getImplementedBy? env n).isSome || Lean.isExtern env n then logInfo m!"@NATIVO {n}"
  logInfo m!"@TF {tf}"
  logInfo m!"@NUESTRAS {nuestras}"
  -- ¿alguna librería cargada que ningún censo mira? (una nueva, importada por FOL o por RPP, quedaría fuera)
  for m in env.header.moduleNames do
    if !([`Init, `Std, `Lean, `Lake, `FOL, `TheoryFramework, `ROBINSON_PlusPlus].contains m.getRoot) then
      logInfo m!"@AJENO {m}"
LEANEOF
} > "$LEANFILE"

# ⛔ 2026-10-02 (ADR-115): la cuarta columna, la SOLIDEZ, se declaraba y NO se comprobaba: el
# bloque que la «miraba» era un `:` vacío, y un nombre inventado daba verde. Ahora, por cada
# fila con solidez, el fichero busca el teorema en el entorno y exige que su TIPO mencione el
# inductivo de la fila; si no, no imprime su marca y el control rompe.
while IFS='|' read -r NOMBRE _ _ SOLIDEZ; do
  { [ -n "$NOMBRE" ] && [ "$SOLIDEZ" != "-" ]; } || continue
  cat >> "$LEANFILE" <<SOLEOF

run_cmd do
  let env ← Lean.getEnv
  match env.find? (String.toName "$SOLIDEZ") with
  | none => pure ()
  | some ci =>
    if ci.type.getUsedConstants.contains (String.toName "$NOMBRE") then
      logInfo m!"@SOL $NOMBRE $SOLIDEZ"
SOLEOF
done <<< "$ESTRATOS"

echo "════ CENSO DE ESTRATOS ════"

if ! command -v lake >/dev/null 2>&1; then
  echo "  ⚠️  SIN MEDIR — 'lake' no está en el PATH de este shell."
  echo "      Lánzalo desde PowerShell. Un control que no se ejecuta NO es un control."
  rm -rf "$TMP"; exit 2
fi

SALIDA=$(lake env lean "$LEANFILE" 2>&1)
PLANA=$(printf '%s' "$SALIDA" | tr '\n' ' ' | tr -s ' ')
rm -rf "$TMP"

FAIL=0
N=0

# ── 1 · por cada estrato declarado, contrastar constructores y habitantes ──────────────────
while IFS='|' read -r NOMBRE CTORS HABS SOLIDEZ; do
  [ -n "$NOMBRE" ] || continue
  N=$((N + 1))
  REAL_C=$(printf '%s' "$PLANA" | grep -oF "@CTORS $NOMBRE " | head -1 >/dev/null 2>&1 \
           && printf '%s' "$PLANA" | sed -E "s/.*@CTORS ${NOMBRE//./\\.} ([0-9]+).*/\1/" || echo "")
  if ! printf '%s' "$PLANA" | grep -qF "@CTORS $NOMBRE "; then
    printf "  ✗ %-46s NO MEDIDO — el inductivo no aparece en la salida\n" "$NOMBRE"
    FAIL=1; continue
  fi
  REAL_H=$(printf '%s' "$PLANA" | grep -oF "@HAB $NOMBRE " | wc -l | tr -d ' ')
  OK=1
  [ "$REAL_C" = "$CTORS" ] || OK=0
  [ "$REAL_H" = "$HABS" ]  || OK=0
  if [ "$OK" = "1" ]; then
    if [ "$HABS" = "0" ]; then
      printf "  ✓ %-46s %3s ctors · %s axiomas ⇒ INDUCCIÓN LEGÍTIMA\n" "$NOMBRE" "$REAL_C" "$REAL_H"
    else
      printf "  ✓ %-46s %3s ctors · %s axiomas ⛔ HABITADO: compruébalos contra lo que la inducción demuestra (ADR-115)\n" "$NOMBRE" "$REAL_C" "$REAL_H"
    fi
  else
    printf "  ✗ %-46s %s ctors / %s axiomas — declarado %s / %s\n" \
      "$NOMBRE" "$REAL_C" "$REAL_H" "$CTORS" "$HABS"
    [ "$REAL_H" -gt "$HABS" ] 2>/dev/null && \
      echo "      ⛔⛔ HAY MÁS AXIOMAS HABITÁNDOLO: si contradicen lo ya probado por inducción, son FALSOS."
    FAIL=1
  fi
  # solidez declarada en el build: la marca `@SOL` sólo sale si el teorema existe y habla de él
  if [ "$SOLIDEZ" != "-" ]; then
    if printf '%s' "$PLANA" | grep -qF "@SOL $NOMBRE $SOLIDEZ"; then
      printf "      └ solidez en el build: %s\n" "$SOLIDEZ"
    else
      printf "  ✗ %-46s solidez declarada '%s': NO está en el entorno, o su tipo no menciona '%s'\n" \
        "$NOMBRE" "$SOLIDEZ" "$NOMBRE"
      FAIL=1
    fi
  fi
done <<< "$ESTRATOS"

# ── 2 · ⛔ ningún axioma puede habitar un inductivo NO declarado ───────────────────────────
echo
echo "════ ¿algún axioma habita un estrato NO DECLARADO? ════"
HUERFANOS=0
# ⛔ 2026-10-04 (ADR-116, segunda revisión): se casa el PRIMER CAMPO entero. Con `grep -F "$CAB|"`,
# un axioma que habitara `Prf` (a secas) pasaba por declarado gracias a `…Hilbert.Prf|`: subcadena.
for CAB in $(printf '%s' "$PLANA" | grep -oE '@HAB [^ ]+' | sed 's/@HAB //' | sort -u); do
  if ! printf '%s\n' "$ESTRATOS" | cut -d'|' -f1 | grep -qxF "$CAB"; then
    echo "  ✗ axiomas habitando \`$CAB\`, que NO está en la tabla"
    HUERFANOS=1; FAIL=1
  fi
done
[ "$HUERFANOS" = "0" ] && echo "  ✓ todos los axiomas habitan estratos declarados"
# Control positivo del alcance (ADR-116): el censo tiene que haber VISTO TheoryFramework.
NTF=$(printf '%s' "$PLANA" | grep -oE '@TF [0-9]+' | grep -oE '[0-9]+' | head -1)
if [ -n "$NTF" ] && [ "$NTF" -gt 0 ] 2>/dev/null; then
  echo "  ✓ el censo incluye TheoryFramework ($NTF constantes suyas en el entorno)"
else
  echo "  ✗ el censo NO vio TheoryFramework (@TF='$NTF'): sus axiomas no los está mirando nadie"
  FAIL=1
fi

# ── 2bis · `sorry` en el ENTORNO ──────────────────────────────────────────────────────────
# ⭐ 2026-10-04 (ADR-116, segunda revisión): el contraste de `check-sorry.bash`, que lee TEXTO. Aquí
# no hay forma de escribir un `sorry` que no se vea: toda constante de RPP, FOL o TheoryFramework cuyo
# tipo o valor nombra `sorryAx`. (Sólo lo que el build compila: los sondeos y `Probe/` no entran.)
echo
echo "════ sorry EN EL ENTORNO (constantes cuyo tipo o valor nombra sorryAx) ════"
NNU=$(printf '%s' "$PLANA" | grep -oE '@NUESTRAS [0-9]+' | grep -oE '[0-9]+' | head -1)
SORRYS=$(printf '%s' "$PLANA" | grep -oE '@SORRY [^ ]+' | sed 's/@SORRY //' | sort -u)
if [ -z "$NNU" ] || [ "$NNU" -le 0 ] 2>/dev/null; then
  echo "  ✗ NO PUDE MEDIR: el censo no vio ninguna constante de los dos repos (@NUESTRAS='$NNU')"
  FAIL=1
elif [ -z "$SORRYS" ]; then
  echo "  ✓ ninguna usa sorryAx  (de $NNU constantes de RPP, FOL y TheoryFramework)"
else
  echo "  ✗ $(printf '%s\n' "$SORRYS" | wc -l | tr -d ' ') constante(s) usan sorryAx:"
  printf '%s\n' "$SORRYS" | head -10 | sed 's/^/      · /'
  FAIL=1
fi

# ── 2ter · CONFIANZA, código NATIVO y librerías AJENAS, en el ENTORNO ─────────────────────────
# ⭐ 2026-10-04 (cuarta revisión de ADR-116): el censo de `sorry` sólo miraba `sorryAx`. Una constante que
# use `Lean.ofReduceBool` (confiar en el compilador: con `implemented_by`, el compilador «demuestra» `False`,
# y el core lo avisa) pasaba por limpia; y una librería nueva, importada por FOL, no la censaba nadie.
echo
echo "════ CONFIANZA (axiomas del core fuera de los tres de Lean) · NATIVO (implemented_by / extern) · AJENO ════"
for par in "TRUST|constante(s) usan un axioma de confianza" "NATIVO|constante(s) con implemented_by o extern" "AJENO|módulo(s) de una librería que ningún censo mira"; do
  var="${par%%|*}"; txt="${par#*|}"
  case "$var" in TRUST) re="@TRUST [^ ]+ [^ ]+" ;; *) re="@$var [^ ]+" ;; esac
  val=$(printf '%s' "$PLANA" | grep -oE "$re" | sed "s/@$var //" | sort -u)
  if [ -z "$val" ]; then
    printf "  ✓ %-8s ninguno\n" "$var"
  else
    printf "  ✗ %-8s %s %s:\n" "$var" "$(printf '%s\n' "$val" | wc -l | tr -d ' ')" "$txt"
    printf '%s\n' "$val" | head -10 | sed 's/^/      · /'
    FAIL=1
  fi
done

# ── 3 · LA ESCALERA DE BINDERS ────────────────────────────────────────────────────────────
# La otra estratificación del proyecto: por NÚMERO DE CUANTIFICADORES. Existe de facto
# (188 usos), y se construyó a reculones — cada peldaño cuando bloqueaba.
#
# ⚠️ Lo que este bloque vigila es el DESFASE: que la escalera del USO no adelante a la de la
# MAQUINARIA sin que nadie se entere. Hoy el desfase es REAL y está declarado: hay tres
# axiomas `forall_5` (`validProofFn`) y la maquinaria llega a 4.
#
# prefijo | máximo peldaño DECLARADO
read -r -d '' ESCALERA <<'EOF'
forall_|5
pcc_thm_inst|4
pcc_axiom_inst|4
PSI_inst|4
psi_lift_form|4
EOF

echo
echo "════ ESCALERA DE BINDERS ════"
MAXUSO=0
MAXMAQ=99
while IFS='|' read -r PREF ESP; do
  [ -n "$PREF" ] || continue
  REAL=0
  for k in 1 2 3 4 5 6 7 8; do
    if grep -rqE "^(theorem|def|abbrev) ${PREF}${k} " ROBINSON_PlusPlus/ --include=*.lean 2>/dev/null; then
      REAL=$k
    fi
  done
  if [ "$REAL" = "$ESP" ]; then
    printf "  ✓ %-18s peldaño máximo %s\n" "$PREF" "$REAL"
  else
    printf "  ✗ %-18s peldaño máximo %s — declarado %s\n" "$PREF" "$REAL" "$ESP"
    echo "      ⇒ o se construyó un peldaño nuevo (⇒ actualizar esta tabla), o se perdió uno."
    FAIL=1
  fi
  if [ "$PREF" = "forall_" ]; then MAXUSO=$REAL
  elif [ "$REAL" -lt "$MAXMAQ" ] 2>/dev/null; then MAXMAQ=$REAL; fi
done <<< "$ESCALERA"

if [ "$MAXUSO" -gt "$MAXMAQ" ] 2>/dev/null; then
  echo "  ⚠️  DESFASE DECLARADO: el uso llega a forall_$MAXUSO y la maquinaria a $MAXMAQ."
  echo "      Es real y conocido — hay axiomas de aridad $MAXUSO sin instanciador de código."
  echo "      ⚠️ La maquinaria crece SUPERLINEALMENTE: medido 6 → 13 → 34 → 64 líneas"
  echo "         (pcc_thm_inst · inst2 · inst3 · inst4). El peldaño 5 NO es una tarde."
  echo "      ⭐ El nivel de las DEFINICIONES sí está cerrado: \`forallN\` + los cinco puentes."
fi

echo
if [ "$N" = "0" ]; then
  echo "❌ LA TABLA ESTÁ VACÍA — el control no comprueba nada."; exit 1
fi
if [ "$FAIL" = "0" ]; then
  echo "✅ LOS $N ESTRATOS CUADRAN."
  echo "   ⚠️  Recordatorio: \`#print axioms\` es CIEGO a esto. El footprint de un teorema probado por"
  echo "       inducción no lleva los axiomas que habitan el inductivo, y el teorema es válido: lo que"
  echo "       puede ser falso es el AXIOMA (ADR-115). Por eso se cuentan aquí."
else
  echo "❌ EL CENSO DE ESTRATOS NO CUADRA."
  echo "   Si subió el número de axiomas de un estrato, lo PRIMERO es mirar qué se demostró"
  echo "   por inducción sobre él: si el axioma nuevo lo contradice, Lean + él ⊢ False."
  echo "   Y si el cambio es correcto, actualizar ESTA tabla Y la de REFERENCE.md §0bis."
fi
exit "$FAIL"
