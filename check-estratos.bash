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
# Desde la raíz de ROBINSON_PlusPlus: mide los dos repos desde aquí (M-3, ADR-205: el mismo toolchain).
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

# ── LA TABLA DECLARADA ─────────────────────────────────────────────────────────────────────
# nombre | constructores | axiomas que lo HABITAN | solidez EN EL BUILD | completitud EN EL BUILD | PUENTE ('-' = ninguno)
# ⚠️ Esta tabla es la misma de `REFERENCE.md` §0bis, y desde T46 (ADR-194) lo comprueba la sección 1bis, abajo: los
# mismos cálculos y los mismos constructores. Si cambia una, cambian las dos.
# ✏️ 2026-10-27 (T46, ADR-194): entra `LKp` (13 constructores; `FOL/Craig0.lean`), que no estaba censado; la solidez de
# `LK₀` y `LKc` (`FOL/SequentSound0.lean`), que estaba en el build y aquí decía «-»; y dos columnas: la COMPLETITUD, con
# nombre desde la hoja `FOL/Estratos0.lean` (sólo `Derives₀` la tenía), y el PUENTE, el teorema que lleva sus
# derivaciones a otro cálculo censado (al sujeto, `Derives₀` o `Prf`, por una cadena de ellos). Las tres, comprobadas
# igual: el teorema existe y su TIPO menciona el inductivo de la fila. `Prf`, `Prfᵢ` y `PrfH` no tienen completitud:
# para ℕ no la hay (Gödel I). ✏️ 2026-10-28 (R3-3-01 de la ronda 3, ADR-212): «menciona» no miraba la DIRECCIÓN, y el
# PUENTE de LKc era `ndToLK`, que ENTRA en LKc (de `Derives₂`); el que sale, `cut_elimination₀` (a `LK₀`), daba rojo,
# porque su tipo es la constante `CutElim₀`. Ahora cada columna se comprueba por su FORMA, con el tipo desplegado
# (`forallTelescopeReducing`): la SOLIDEZ y el PUENTE tienen una hipótesis del inductivo de la fila y una conclusión que
# no lo es (salen de él); la COMPLETITUD concluye en él. Y `Prf` tiene completitud para su teoría, no para ℕ:
# `prf_completo` (ADR-195). Un mutante permanente (`ndToLK` como puente de LKc) tiene que dar rojo. Un cálculo NUEVO (el `DerivesI` intuicionista de X1, si llega) entra con su fila aquí
# y en §0bis. ✏️ 2026-10-28 (T51, ADR-218): llegó; su completitud, «-»: con la semántica de Tarski es falsa.
# 2026-10-02 (ADR-115): `Derives` baja de 4 a 0 al borrarse `FOL/MetaRules.lean`, y gana su solidez
# en el build (`FOL/Inconsistencia.lean` §1).
read -r -d '' ESTRATOS <<'EOF'
Derives|22|0|FOL.Inconsistencia.derives_soundness|FOL.Estratos0.derives_semantic_complete|FOL.Inconsistencia.derives_to_derives0
Derives₀|21|0|FOL.Metamath.Soundness0.derives0_soundness|FOL.Canonical0.completeness₀|-
Derives₁|20|0|FOL.Estratos0.derives1_soundness|FOL.Estratos0.derives1_complete|FOL.Derives1.derives1_to_derives0
Derives₂|22|0|FOL.Estratos0.derives2_soundness|FOL.Estratos0.derives2_complete|FOL.Derives2.derives2_to_derives1
LK₀|14|0|FOL.SequentSound0.lk0_sound|FOL.Estratos0.lk0_complete|FOL.SequentSound0.lk0_to_derives0
LKc|15|0|FOL.SequentSound0.lkc_sound|FOL.Estratos0.lkc_complete|FOL.Hauptsatz0.cut_elimination₀
FOL.Calculus.Derivesᵢ|18|0|FOL.Estratos0.derivesI_soundness|-|FOL.Calculus.derivesI_to_derives0
LKh|14|0|FOL.Estratos0.lkh_sound|FOL.Estratos0.lkh_complete|FOL.Hauptsatz0.lkh_to_lk0
FOL.Craig0.LKp|13|0|FOL.Estratos0.lkp_sound|FOL.Estratos0.lkp_complete|FOL.Craig0.lkp_to_lk0
ROBINSON_PlusPlus.Meta.Hilbert.Prf|7|0|ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound|ROBINSON_PlusPlus.Meta.PuenteFOL.prf_completo|-
ROBINSON_PlusPlus.Meta.Hilbert.Prfᵢ|17|0|ROBINSON_PlusPlus.Meta.SolidezPrf.prfI_sound|-|ROBINSON_PlusPlus.Meta.Hilbert.Prf.incl
ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH|8|0|ROBINSON_PlusPlus.Meta.SolidezPrf.prfH_sound|-|ROBINSON_PlusPlus.Meta.HilbertDeduction.prfH_nil_to_prf
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

/-! ⭐ 2026-10-21 (T13, ADR-179): EL SEÑUELO PERMANENTE. Un censo que no ve nada imprime «✓ ninguno», igual que uno
que ya no sabe mirar (un toolchain que cambia la API, una errata). Aquí, en el propio fichero del censo, una constante
de cada clase que el censo busca; como no tienen módulo, `esNuestro` las descarta, y las mira `esSenuelo`. El script
exige EXACTAMENTE sus marcas (`SENUELOS`, abajo): si una falta, o sale otra, el censo no está midiendo lo que dice. -/
namespace Senuelo
inductive I : Type where
  | c : I
axiom habita : I
def conSorry : Nat := sorry
theorem conNativo : (2 + 2 : Nat) = 4 := by native_decide
-- (✏️ v4.35, T42b: `Lean.ofReduceBool` ya no existe; el axioma AJENO del señuelo es `lcUnreachable`, del core)
noncomputable unsafe def conAjeno : Nat := lcUnreachable
def implReal (n : Nat) : Nat := n
@[implemented_by implReal] def conImplementedBy (n : Nat) : Nat := n
@[extern "senuelo_c"] opaque conExtern : Nat → Nat
partial def conPartial (n : Nat) : Nat := if n = 0 then 0 else conPartial (n - 1)
end Senuelo

def esNuestro (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    (`FOL).isPrefixOf m || m == `FOL
      || (`ROBINSON_PlusPlus).isPrefixOf m || m == `ROBINSON_PlusPlus
      || (`TheoryFramework).isPrefixOf m || m == `TheoryFramework

/-- Las del señuelo de este fichero: sin módulo, y bajo `Senuelo`. -/
def esSenuelo (env : Environment) (n : Name) : Bool :=
  (env.getModuleIdxFor? n).isNone && (`Senuelo).isPrefixOf n

/-- La cabeza de la CONCLUSIÓN del tipo: el inductivo que el axioma HABITA. -/
def cabeza (e : Expr) : Name :=
  match e.getForallBody.getAppFn with
  | .const c _ => c
  | _ => `desconocida

/-- ¿Un axioma de CONFIANZA? Uno ajeno que no sea de los tres de Lean ni `sorryAx` (`Lean.ofReduceBool`,
    `Lean.trustCompiler`…), y —aunque sea del propio módulo— el auxiliar que fabrica `native_decide`
    (`…._native.native_decide.ax_…`): en v4.31 `native_decide` ya no nombra `Lean.ofReduceBool`, sino un axioma
    NUEVO en el módulo que lo usa, que `esNuestro` absolvía (lo destapó el señuelo, 2026-10-21, ADR-179). Las del
    señuelo cuentan aquí como nuestras: así `conNativo` prueba la segunda cláusula, y `conAjeno`, la primera. -/
def esConfianza (env : Environment) (estandar : NameSet) (u : Name) : Bool :=
  match env.find? u with
  | some (.axiomInfo _) =>
    !estandar.contains u && u != ``sorryAx
      && ((!(esNuestro env u) && !(esSenuelo env u)) || u.components.contains `_native)
  | _ => false

run_cmd do
  let env ← Lean.getEnv
  let mut tf : Nat := 0
  let mut nuestras : Nat := 0
  -- los tres axiomas de Lean que el proyecto acepta; cualquier OTRO axioma ajeno que use una constante
  -- nuestra (`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, …) es @TRUST
  let estandar : NameSet := ((({} : NameSet).insert ``propext).insert ``Classical.choice).insert ``Quot.sound
  for (n, ci) in env.constants.toList do
    let sen := esSenuelo env n
    if !(esNuestro env n) && !sen then continue
    -- (las marcas del señuelo llevan «@SENUELO » delante: no se mezclan con las del censo)
    let p := if sen then "@SENUELO " else "@"
    if !sen then
      nuestras := nuestras + 1
      if let some idx := env.getModuleIdxFor? n then
        if (`TheoryFramework).isPrefixOf env.header.moduleNames[idx.toNat]! then tf := tf + 1
    match ci with
    | .axiomInfo ax => logInfo m!"{p}HAB {cabeza ax.type} {n}"
    | .inductInfo ind => if !n.isInternal then logInfo m!"{p}CTORS {n} {ind.ctors.length}"
    -- (un `partial def` es un `opaque` con su `…._unsafe_rec` al lado; T13, ADR-179)
    | .opaqueInfo _ => if env.contains (n ++ `_unsafe_rec) then logInfo m!"{p}PARCIAL {n}"
    | _ => pure ()
    -- tipo y valor, también el de un teorema (`getUsedConstantsAsSet` lee con `allowOpaque`)
    let usadas := ci.getUsedConstantsAsSet
    if usadas.contains ``sorryAx then logInfo m!"{p}SORRY {n}"
    for u in usadas do
      if esConfianza env estandar u then logInfo m!"{p}TRUST {n} {u}"
    if (Lean.Compiler.getImplementedBy? env n).isSome || Lean.isExtern env n then logInfo m!"{p}NATIVO {n}"
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
# ✏️ 2026-10-27 (T46, ADR-194): lo mismo para la completitud (@COMP) y el puente (@PUENTE).
# ✏️ 2026-10-28 (R3-3-01, ADR-212): la FORMA, no la mención (ver la cabecera de la tabla). `direccionOK` despliega el
# tipo, mira las cabezas de las hipótesis y de la conclusión, y decide por la columna.
cat >> "$LEANFILE" <<'DIREOF'

/-- ¿Concluye `e` en el inductivo `ind`? Su cabeza es `ind`, o es un `∃` o un `∧` con `ind` dentro (así concluyen
    `lkh_complete`, `∃ n, LKh n Γ [f]`, y `lkp_complete`, `∃ E, … ∧ LKp (E ++ Γ) [f]`). -/
partial def concluyeEn (ind : Lean.Name) (e : Lean.Expr) : Lean.MetaM Bool := do
  let e ← Lean.Meta.whnf e
  if e.getAppFn.constName? == some ind then return true
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Exists, #[_, p] => Lean.Meta.lambdaTelescope p fun _ b => concluyeEn ind b
  | some ``And, #[a, b] => return (← concluyeEn ind a) || (← concluyeEn ind b)
  | _, _ => return false

/-- ¿Tiene `teo` la forma de su columna para el inductivo `ind`? SOL/PUENTE: una hipótesis cuya cabeza es `ind` y
    una conclusión que NO concluye en él (sale de `ind`); COMP: la conclusión concluye en `ind`. -/
def direccionOK (marca : String) (ind teo : Lean.Name) : Lean.Elab.Command.CommandElabM Bool :=
  Lean.Elab.Command.liftTermElabM do
    match (← Lean.getEnv).find? teo with
    | none => pure false
    | some ci =>
      Lean.Meta.forallTelescopeReducing ci.type fun hs concl => do
        let enConcl ← concluyeEn ind concl
        let mut enHip := false
        for h in hs do
          let t ← Lean.Meta.whnf (← Lean.Meta.inferType h)
          if t.getAppFn.constName? == some ind then enHip := true
        pure (if marca == "COMP" then enConcl else enHip && !enConcl)

-- el mutante permanente: `ndToLK` ENTRA en LKc (desde `Derives₂`); como PUENTE de LKc tiene que dar rojo
run_cmd do
  if ((← Lean.getEnv).find? `FOL.NDtoLK0.ndToLK).isSome then
    if !(← direccionOK "PUENTE" `LKc `FOL.NDtoLK0.ndToLK) then logInfo m!"@MUTANTE_DIRECCION_VISTO"
DIREOF
while IFS='|' read -r NOMBRE _ _ SOLIDEZ COMPLETITUD PUENTE; do
  [ -n "$NOMBRE" ] || continue
  for par in "SOL $SOLIDEZ" "COMP $COMPLETITUD" "PUENTE $PUENTE"; do
    MARCA=${par%% *}; TEO=${par#* }
    [ "$TEO" != "-" ] || continue
    cat >> "$LEANFILE" <<SOLEOF

run_cmd do
  if (← direccionOK "$MARCA" (String.toName "$NOMBRE") (String.toName "$TEO")) then
    logInfo m!"@$MARCA $NOMBRE $TEO"
SOLEOF
  done
done <<< "$ESTRATOS"

echo "════ CENSO DE ESTRATOS ════"

if ! command -v lake >/dev/null 2>&1; then
  echo "  ⚠️  SIN MEDIR — 'lake' no está en el PATH de este shell."
  echo "      Lánzalo desde PowerShell. Un control que no se ejecuta NO es un control."
  rm -rf "$TMP"; exit 2
fi

SALIDA=$(lake env lean "$LEANFILE" 2>&1)
RC=$?
PLANA=$(printf '%s' "$SALIDA" | tr '\n' ' ' | tr -s ' ')
rm -rf "$TMP"
# ✏️ 2026-10-21 (T42b, ADR-181): un ERROR de Lean en el fichero generado no paraba el censo: medía lo que llegara a
# elaborarse, y sólo lo delataba, de rebote, alguna marca ausente. Al subir a v4.35.0 dio errores (una constante del
# señuelo que ya no existe, un `let mut` sin tipo). Ahora es «NO PUDE MEDIR», como en `../FOL/check-axioms.bash`.
if [ "$RC" != "0" ] || printf '%s\n' "$SALIDA" | grep -qE ': error'; then
  echo "  ❌ NO PUDE MEDIR: 'lake env lean' sobre el fichero del censo dio error (código $RC). ¿Está construido el árbol?"
  printf '%s\n' "$SALIDA" | grep -m3 -E 'error' | sed 's/^/      /' | cut -c1-160
  exit 1
fi
# ✏️ 2026-10-28 (R3-3-01, ADR-212): el mutante de dirección tiene que haber dado rojo; si no, la forma no se mira.
if ! printf '%s' "$PLANA" | grep -qF "@MUTANTE_DIRECCION_VISTO"; then
  echo "  ❌ NO PUDE MEDIR: el mutante de dirección (ndToLK como PUENTE de LKc) no dio rojo: la forma no se está mirando."
  exit 1
fi

FAIL=0
N=0

# ── 1 · por cada estrato declarado, contrastar constructores y habitantes ──────────────────
while IFS='|' read -r NOMBRE CTORS HABS SOLIDEZ COMPLETITUD PUENTE; do
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
      # ✏️ 2026-10-12 (ADR-133): decía «⇒ INDUCCIÓN LEGÍTIMA», la lectura vieja de M-11.
      printf "  ✓ %-46s %3s ctors · %s axiomas ⇒ ningún postulado que contrastar\n" "$NOMBRE" "$REAL_C" "$REAL_H"
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
  # (✏️ T46, ADR-194) la completitud y el puente, igual
  for par in "COMP completitud $COMPLETITUD" "PUENTE puente $PUENTE"; do
    MARCA=${par%% *}; resto=${par#* }; QUE=${resto%% *}; TEO=${resto#* }
    [ "$TEO" != "-" ] || continue
    if printf '%s' "$PLANA" | grep -qF "@$MARCA $NOMBRE $TEO"; then
      printf "      └ %s en el build: %s\n" "$QUE" "$TEO"
    else
      printf "  ✗ %-46s %s: '%s': NO está en el entorno, o su tipo no menciona '%s'\n" \
        "$NOMBRE" "$QUE" "$TEO" "$NOMBRE"
      FAIL=1
    fi
  done
done <<< "$ESTRATOS"

# ── 1bis · REFERENCE.md §0bis tiene los MISMOS cálculos, con los mismos constructores (T46, ADR-194) ──────────
# Hasta el 2026-10-27 la tabla de aquí decía ser «la misma de §0bis» y tenía diez filas frente a cinco. Ahora se
# comprueba: de cada fila de §0bis, la primera cita (`Derives₀`, `Prf`…) y su columna de constructores; de cada fila
# de aquí, el último componente del nombre y sus constructores. Los dos conjuntos, iguales en LOS DOS SENTIDOS.
echo
echo "════ ¿§0bis de REFERENCE.md es esta tabla? ════"
REF_0BIS=$(awk '/^## 0bis/ { en = 1; next } en && /^### / { exit } en && /^\| \*\*`/' REFERENCE.md \
  | awk -F'|' '{ n = $2; sub(/^[^`]*`/, "", n); sub(/`.*$/, "", n); c = $4; gsub(/[^0-9]/, "", c); print n "|" c }' | LC_ALL=C sort)
AQUI_0BIS=$(printf '%s\n' "$ESTRATOS" | awk -F'|' 'NF >= 2 { n = $1; sub(/.*[.]/, "", n); print n "|" $2 }' | LC_ALL=C sort)
if [ -z "$REF_0BIS" ]; then
  echo "  ✗ no encuentro la tabla de §0bis en REFERENCE.md: el cruce no comprueba nada"
  FAIL=1
elif [ "$REF_0BIS" = "$AQUI_0BIS" ]; then
  echo "  ✓ §0bis tiene los mismos $(printf '%s\n' "$AQUI_0BIS" | grep -c .) cálculos, con los mismos constructores"
else
  echo "  ✗ §0bis y esta tabla NO cuadran («<» sólo aquí, «>» sólo en §0bis):"
  diff <(printf '%s\n' "$AQUI_0BIS") <(printf '%s\n' "$REF_0BIS") | grep '^[<>]' | sed 's/^/      /'
  FAIL=1
fi

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

# ── 2quater · `partial`, con IGUALDAD (T13, ADR-179) ───────────────────────────────────────────
# Un `partial def` es opaco para el núcleo: no es un agujero por sí solo (no entra en ningún término de prueba
# mientras nadie lo use en una), pero la cifra se vigila con igualdad, como las demás: uno nuevo es rojo, y uno que
# desaparece también, para que la tabla baje. MEDIDOS en el entorno (2026-10-21), cinco: el `termToString` de RPP, los
# dos ayudantes de táctica de FOL (`FOL/Tactics.lean`) y, que el grep no veía, los `Repr` y `BEq` DERIVADOS de
# `TermG` (`FOL/FOL.lean`: un inductivo anidado, y su `deriving` los hace `partial`). La auditoría contaba 1 y 2 por texto.
read -r -d '' PARCIALES <<'EOF'
ROBINSON_PlusPlus.Minimal.Axioms.termToString
getAllPositions
tryMem
instBEqTermG.beq
instReprTermG.repr
EOF
echo
echo "════ partial (opacos para el núcleo; con igualdad) ════"
PARC=$(printf '%s' "$PLANA" | grep -oE '@PARCIAL [^ ]+' | sed 's/@PARCIAL //' | LC_ALL=C sort -u)
PARC_ESP=$(printf '%s\n' "$PARCIALES" | sed '/^$/d' | LC_ALL=C sort -u)
if [ "$PARC" = "$PARC_ESP" ]; then
  echo "  ✓ los $(printf '%s\n' "$PARC" | sed '/^$/d' | wc -l | tr -d ' ') declarados, y ninguno más: $(printf '%s ' $PARC)"
else
  echo "  ✗ los \`partial\` del entorno no son los declarados:"
  diff <(printf '%s\n' "$PARC_ESP" | sed '/^$/d') <(printf '%s\n' "$PARC" | sed '/^$/d') | grep -E '^[<>]' \
    | sed 's/^</      · falta/; s/^>/      · sobra/'
  FAIL=1
fi

# ── 2quinquies · EL SEÑUELO: el censo se ve a sí mismo (T13, ADR-179) ────────────────────────────
# Las marcas que el señuelo del fichero (namespace `Senuelo`) TIENE que dar, una por clase de las que el censo busca.
# Si falta una, el censo ya no sabe ver esa clase (y daría «✓ ninguno» sin mirar); si sale otra, algo cambió en
# cómo Lean fabrica lo que el señuelo usa: se mira y se actualiza esta tabla, con su ADR. MEDIDAS con v4.31.0
# (2026-10-21) y RE‑MEDIDAS con v4.35.0 (T42b, ADR-181: el axioma ajeno pasa a ser `lcUnreachable`). ⚠️ El nombre
# del auxiliar de `native_decide` y su cabeza son de Lean, no nuestros.
read -r -d '' SENUELOS <<'EOF'
@SENUELO CTORS Senuelo.I 1
@SENUELO HAB Senuelo.I Senuelo.habita
@SENUELO HAB Eq Senuelo.conNativo._native.native_decide.ax_1_1
@SENUELO PARCIAL Senuelo.conPartial
@SENUELO SORRY Senuelo.conSorry
@SENUELO TRUST Senuelo.conNativo Senuelo.conNativo._native.native_decide.ax_1_1
@SENUELO TRUST Senuelo.conAjeno lcUnreachable
@SENUELO NATIVO Senuelo.conImplementedBy
@SENUELO NATIVO Senuelo.conExtern
EOF
echo
echo "════ SEÑUELO (el censo tiene que verse a sí mismo: una constante de cada clase) ════"
SEN=$(printf '%s\n' "$SALIDA" | grep -oE '@SENUELO .*' | sed 's/[[:space:]]*$//' | LC_ALL=C sort -u)
SEN_ESP=$(printf '%s\n' "$SENUELOS" | sed '/^$/d' | LC_ALL=C sort -u)
if [ -n "$SEN" ] && [ "$SEN" = "$SEN_ESP" ]; then
  echo "  ✓ las $(printf '%s\n' "$SEN" | wc -l | tr -d ' ') marcas del señuelo, exactas: el censo ve axiomas, constructores, partial, sorry, confianza y nativo"
else
  echo "  ✗ el señuelo no da sus marcas: el censo NO está midiendo lo que dice"
  diff <(printf '%s\n' "$SEN_ESP" | sed '/^$/d') <(printf '%s\n' "$SEN" | sed '/^$/d') | grep -E '^[<>]' \
    | sed 's/^</      · falta/; s/^>/      · sobra/'
  FAIL=1
fi

# ── 3 · LA ESCALERA DE BINDERS ────────────────────────────────────────────────────────────
# La otra estratificación del proyecto: por NÚMERO DE CUANTIFICADORES. Existe de facto
# (188 usos), y se construyó a reculones — cada peldaño cuando bloqueaba.
#
# ⚠️ Lo que este bloque vigila es el DESFASE: que la escalera del USO no adelante a la de la
# MAQUINARIA sin que nadie se entere. Hasta ADR‑192 era REAL y estaba declarado: tres axiomas
# `forall_5` (los de `validProofFn`, el verificador antiguo) y la maquinaria en 4. Con ellos
# salió `forall_5` (2026‑10‑27, T68), y hoy el uso y la maquinaria llegan a 4.
#
# prefijo | máximo peldaño DECLARADO
read -r -d '' ESCALERA <<'EOF'
forall_|4
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
  echo "      ⭐ El nivel de las DEFINICIONES sí está cerrado: \`forallN\` + sus puentes (cuatro desde ADR-192)."
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
