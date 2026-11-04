#!/bin/bash
# check-indice.bash — el ÍNDICE de las constantes de RPP, y lo que nadie usa de FOL (L5-11 y FOL0912:B-5, ADR-254).
#
# ⛔ POR QUÉ EXISTE. «Antes de construir, buscar» se repetía en seis ADR (L5-11, ronda 1 de la auditoría de la base): se
# volvía a construir lo que ya estaba, porque no había dónde buscarlo salvo con grep sobre el texto, que no ve el nombre
# completo que da un `namespace` ni el enunciado que elabora Lean. Y de la librería FOL, 96 de 157 declaraciones no las
# usaba nadie (B-5 de la auditoría de FOL del 2026-09-12), sin que lo dijera ningún sitio. Las dos decisiones del
# propietario (2026-11-04): el índice (nombre, módulo, enunciado) de todas las constantes de RPP y FOL, regenerado y
# comprobado en cada run; y lo que nadie usa de FOL, medido y etiquetado, sin borrar.
#
# QUÉ ESCRIBE. Del entorno de Lean —un fichero generado que importa CADA módulo de RPP, FOL y TheoryFramework, como
# check-choice.bash—, cada constante DECLARADA: con rango de declaración en su fuente y que Lean no genere (ni
# recursores, ni `casesOn`, ni `match_N`, ni ecuaciones, ni `injEq`, ni `ctorElim`…: las reglas de
# `Lean.isAutoDeclOrPrivate_Internal`, de Lean/AutoDecl.lean, salvo que una privada cuenta por su nombre de usuario).
#   doc/indice.tsv               las de RPP, una por línea: «nombre · clase · módulo · enunciado», el enunciado como lo
#                                imprime Lean con los nombres COMPLETOS (`pp.fullNames`: no depende de los `open` ni de
#                                los `export`), en una línea. Las de FOL y TheoryFramework están en
#                                ../FOL/doc/indice.tsv, que genera y comprueba el check-indice.bash de FOL, en su CI.
#   doc/control/fol-sin-uso.tsv  las de FOL y TheoryFramework que NINGUNA otra constante de las tres librerías nombra,
#                                ni en su tipo ni en su valor: «módulo · nombre · clase · etiqueta». Un constructor o un
#                                campo cuentan como su tipo, y lo que Lean genera con una declaración (su `match_N`, sus
#                                ecuaciones, su `proof_N`), como ella. La etiqueta dice por qué puede no ser basura:
#                                  vigilada   tiene fila en check-footprints.bash: un titular, una hoja a propósito
#                                  simp       lleva el atributo: simp puede usarla sin dejar rastro en el término
#                                             (feedback «simp con un lema rfl NO deja prueba»)
#                                  instancia  la usaría la resolución de instancias
#                                  meta       sintaxis o elaborador: la usa el analizador, no un término
#                                  —          ninguna de las anteriores
#                                No se cuentan los sondeos, el libro ni los consumidores archivados (ADR-216); y un
#                                bloque `mutual` se usa a sí mismo.
#
# ⭐ Las dos tablas se comparan con lo que se GENERA, línea a línea: cualquier diferencia es rojo. Se rehacen con
# `--rehacer` en el mismo commit que cambia una declaración (como DEPENDENCIES.md con gen-dependencies.py); un push de
# FOL que cambia lo que nadie usa deja rojo el run de RPP hasta el commit de RPP que lo acompaña (M-12), como
# doc/control/choice.tsv.
#
# 🔑 CALIBRACIÓN (feedback de los controles que no comprueban nada): el fichero generado declara seis constantes de
# prueba —un teorema, otro que lo usa, una privada, un inductivo con dos constructores, una función por casos sobre él y
# una recursiva—; el control exige ver en el índice exactamente esas ocho declaraciones (con los dos constructores) y sus
# enunciados (ni el recursor, ni `casesOn`, ni `match_1`, ni `injEq`), que el filtro de las generadas quite él solo las
# de prueba sin rango (la falta de rango es un segundo filtro, y sin esto no se le vería fallar al primero), que se
# generen al menos cuatro constantes más, y que la medida de uso diga cuáles se usan (la recursiva, no: sólo la nombra
# lo que Lean genera con ella, y sin el «dueño» saldría usada). Si el censo no corre o no llega al final (la línea
# FIN), es rojo.
#
# 🔧 Desde la raíz de RPP, con el build al día (`lake build` y `lake build "@FOL/FOL" "@FOL/TheoryFramework"`), desde
# PowerShell o desde un bash con `lake` en el PATH.
#
#   bash check-indice.bash            # genera y compara con las dos tablas
#   bash check-indice.bash --rehacer  # además, las reescribe con lo generado
#
# Para buscar antes de construir: `grep -i 'patrón' doc/indice.tsv ../FOL/doc/indice.tsv` (AI-GUIDE, «Antes de
# construir, buscar»).

set -uo pipefail
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

INDICE=doc/indice.tsv
SINUSO=doc/control/fol-sin-uso.tsv
REHACER=0
[ "${1:-}" = "--rehacer" ] && REHACER=1

echo "════ EL ÍNDICE DE LAS CONSTANTES DE RPP, Y LO QUE NADIE USA DE FOL ════"

if ! command -v lake >/dev/null 2>&1; then
  echo "  ⚠️  SIN MEDIR — 'lake' no está en el PATH de este shell. Un control que no se ejecuta NO es un control."
  exit 2
fi

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
# (Lean es un programa de Windows en la máquina de desarrollo: las rutas que lee, en su forma; en Linux, tal cual)
win() { cygpath -m "$1" 2>/dev/null || printf '%s' "$1"; }
LEANFILE="$TMP/Indice.lean"
MODS="$TMP/modulos.txt"
{
  ( find ROBINSON_PlusPlus -name '*.lean' ; echo ROBINSON_PlusPlus.lean )
  ( cd ../FOL && find FOL TheoryFramework -name '*.lean' ; echo FOL.lean ; echo TheoryFramework.lean )
} | sed -e 's/\.lean$//' -e 's|/|.|g' | LC_ALL=C sort -u > "$MODS"
NMODS=$(grep -c . "$MODS")
if [ "$NMODS" -lt 100 ]; then
  echo "  ❌ sólo $NMODS módulos: la lista de ficheros no se pudo leer (¿falta ../FOL?)."
  exit 1
fi
# las que tienen fila en check-footprints.bash (la etiqueta «vigilada»)
VIGILADAS="$TMP/vigiladas.txt"
sed -n "/^read -r -d '' TABLA <<'EOF'\$/,/^EOF\$/p" check-footprints.bash | grep '|' | cut -d'|' -f1 > "$VIGILADAS"
NVIG=$(grep -c . "$VIGILADAS")
if [ "$NVIG" -lt 100 ]; then
  echo "  ❌ sólo $NVIG filas de check-footprints.bash: no pude leer su tabla."
  exit 1
fi
{
  echo "import Lean"
  sed 's/^/import /' "$MODS"
  cat <<'EOF'
open Lean Meta

namespace IndiceCalib
-- la calibración: el índice tiene que ver estas ocho declaraciones (con los dos constructores), y no lo que Lean
-- genera con ellas; y la medida de uso, que se usan `calibT` (la usa `calibU`) y `CalibI` (la usa `calibM`), y nada
-- más: `calibR` sólo la nombra lo que Lean genera con ella (su `_sunfold`), y eso es ella misma
theorem calibT (n : Nat) : n + 0 = n := rfl
theorem calibU : 3 + 0 = 3 := calibT 3
private def calibP : Nat := 1
inductive CalibI where
  | uno
  | dos (n : Nat)
def calibM : CalibI → Nat
  | .uno => 0
  | .dos n => n
def calibR : Nat → Nat
  | 0 => 0
  | n + 1 => calibR n
end IndiceCalib

def indiceRaiz (m : Name) : Option String :=
  let r := m.getRoot.toString
  if r == "ROBINSON_PlusPlus" then some "RPP" else if r == "FOL" then some "FOL"
  else if r == "TheoryFramework" then some "TF" else none

/-- ¿la genera Lean? Las reglas de `Lean.isAutoDeclOrPrivate_Internal` (Lean/AutoDecl.lean), salvo que una privada
    cuenta por su nombre de usuario: aquélla las da todas por generadas. -/
partial def indiceGenerada (env : Environment) (d : Name) : Bool :=
  let u := (privateToUserName? d).getD d
  if isPrivateName d && u.isAnonymous then false
  else if d.hasMacroScopes || u.isInternal || isReservedName env d then true
  else match d with
    | .str n s =>
      indiceGenerada env n || s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "unsafe_"
        || s.startsWith "grind_"
        || (env.isConstructor n && ["injEq", "inj", "sizeOf_spec", "elim", "noConfusion"].contains s)
        || (match env.find? n with
            | some (.inductInfo _) =>
              s.startsWith "brecOn_" || s.startsWith "below_"
                || ["casesOn", "recOn", "brecOn", "below", "ndrec", "ndrecOn", "noConfusionType", "noConfusion",
                    "ofNat", "toCtorIdx", "ctorIdx", "ctorElim", "ctorElimType"].contains s
                || (isSubobjectField? env n (.mkSimple s)).isSome
            | _ => false)
    | _ => false

/-- el enunciado en una línea: los saltos y los tabuladores, espacios; los espacios seguidos, uno -/
def indiceLinea (s : String) : String := Id.run do
  let mut out := ""
  let mut esp := false
  for ch in s.toList do
    let ch := if ch == '\n' || ch == '\t' || ch == '\r' then ' ' else ch
    if ch == ' ' then
      unless esp do out := out.push ' '
      esp := true
    else
      out := out.push ch
      esp := false
  return out

#eval show MetaM Unit from do
  let env ← getEnv
  let simps ← getSimpTheorems
  let some rutaI ← IO.getEnv "INDICE_RPP" | throwError "falta INDICE_RPP"
  let some rutaS ← IO.getEnv "INDICE_SINUSO" | throwError "falta INDICE_SINUSO"
  let some rutaV ← IO.getEnv "INDICE_VIGILADAS" | throwError "falta INDICE_VIGILADAS"
  let vigiladas : Std.HashSet String := Std.HashSet.ofList (← IO.FS.lines rutaV).toList
  let repoDe (c : Name) : Option (String × String) := match env.getModuleIdxFor? c with
    | some i =>
      let m := env.header.moduleNames[i.toNat]!
      (indiceRaiz m).map (fun r => (r, m.toString))
    | none => if (`IndiceCalib).isPrefixOf ((privateToUserName? c).getD c) then some ("CALIB", "_calibracion") else none
  -- 1. las declaradas
  let mut decl : Std.HashMap Name (String × String) := {}
  let mut nGen : Std.HashMap String Nat := {}
  let mut sinRango : Array Name := #[]
  for (c, ci) in env.constants.toList do
    let some (repo, modulo) := repoDe c | continue
    let gen := (match ci with | .recInfo _ | .quotInfo _ => true | _ => false)
      || isAuxRecursor env c || isNoConfusion env c || isRecCore env c || isMatcherCore env c || indiceGenerada env c
    if gen then
      nGen := nGen.insert repo ((nGen.getD repo 0) + 1)
      continue
    if (← findDeclarationRanges? c).isNone then
      sinRango := sinRango.push c
      continue
    decl := decl.insert c (repo, modulo)
  -- el dueño de una constante: la declarada a la que pertenece; la de un constructor o un campo, su tipo
  let dueno (c : Name) : Name := Id.run do
    let mut p := c
    while !p.isAnonymous && !decl.contains p do p := p.getPrefix
    if p.isAnonymous then return c
    match env.find? p with
    | some (.ctorInfo v) => return v.induct
    | _ =>
      match env.getProjectionFnInfo? p with
      | some pi =>
        match env.find? pi.ctorName with
        | some (.ctorInfo v) => return v.induct
        | _ => return p
      | none => return p
  -- 2. el uso: qué dueño nombra a qué otro, en el tipo o en el valor (1 RPP, 2 FOL, 4 TF, 8 la calibración)
  let bit (r : String) : Nat := if r == "RPP" then 1 else if r == "FOL" then 2 else if r == "TF" then 4 else 8
  let mut usada : Std.HashMap Name Nat := {}
  let mut sinValor := 0
  for (c, ci) in env.constants.toList do
    let some (repo, _) := repoDe c | continue
    let dc := dueno c
    let val := ci.value? (allowOpaque := true)
    if val.isNone && (ci.isTheorem || ci.isDefinition) then sinValor := sinValor + 1
    for u in ci.type.getUsedConstants ++ ((val.map (·.getUsedConstants)).getD #[]) do
      let du := dueno u
      if du != dc && decl.contains du then
        usada := usada.insert du ((usada.getD du 0) ||| bit repo)
  -- 3. las filas
  let mut indice : Array String := #[]
  let mut sinUso : Array String := #[]
  let mut calib : Array String := #[]
  let mut nDecl : Std.HashMap String Nat := {}
  let mut nUsoRPP : Std.HashMap String Nat := {}
  let mut nUsoDentro : Std.HashMap String Nat := {}
  let mut nSinUso : Std.HashMap String Nat := {}
  let mut nCortados := 0
  for (c, (repo, modulo)) in decl.toList do
    let some ci := env.find? c | continue
    let u := (privateToUserName? c).getD c
    let esMeta := match ci.type.getAppFn.constName? with
      | some h => h.getRoot == `Lean
      | none => false
    let clase := match ci with
      | .thmInfo _ => "teorema"
      | .axiomInfo _ => "axioma"
      | .opaqueInfo _ => "opaca"
      | .ctorInfo _ => "constructor"
      | .inductInfo _ => if isClass env c then "clase" else if isStructure env c then "estructura" else "inductivo"
      | .defnInfo _ =>
        if isInstanceCore env c then "instancia"
        else if (env.getProjectionFnInfo? c).isSome then "campo"
        else if esMeta then "meta" else "def"
      | _ => "otra"
    let clase := if isPrivateName c then clase ++ "·privada" else clase
    nDecl := nDecl.insert repo ((nDecl.getD repo 0) + 1)
    if repo == "RPP" || repo == "CALIB" then
      let f ← withOptions (fun o => pp.fullNames.set o true) (ppExpr ci.type)
      let mut txt := indiceLinea (f.pretty 100000)
      -- (un enunciado de más de 4000 caracteres se corta, y lo dice)
      if txt.length > 4000 then
        nCortados := nCortados + 1
        txt := String.ofList (txt.toList.take 4000) ++ s!" …[+{txt.length - 4000}]"
      let fila := s!"{u}\t{clase}\t{modulo}\t{txt}"
      if repo == "CALIB" then calib := calib.push s!"CALIB\tI\t{fila}" else indice := indice.push fila
    if (repo == "FOL" || repo == "TF" || repo == "CALIB") && dueno c == c then
      let m := usada.getD c 0
      if m &&& 1 != 0 then nUsoRPP := nUsoRPP.insert repo ((nUsoRPP.getD repo 0) + 1)
      else if m != 0 then nUsoDentro := nUsoDentro.insert repo ((nUsoDentro.getD repo 0) + 1)
      if m == 0 then
        nSinUso := nSinUso.insert repo ((nSinUso.getD repo 0) + 1)
        let etiqueta :=
          if vigiladas.contains u.toString then "vigilada"
          else if simps.isLemma (.decl c) then "simp"
          else if clase.startsWith "instancia" then "instancia"
          else if clase.startsWith "meta" then "meta"
          else "—"
        let fila := s!"{modulo}\t{u}\t{clase}\t{etiqueta}"
        if repo == "CALIB" then calib := calib.push s!"CALIB\tS\t{fila}" else sinUso := sinUso.push fila
      else if repo == "CALIB" then calib := calib.push s!"CALIB\tU\t{u}"
  IO.FS.writeFile rutaI ("\n".intercalate indice.toList ++ "\n")
  IO.FS.writeFile rutaS ("\n".intercalate sinUso.toList ++ "\n")
  for l in calib do IO.println l
  for r in ["RPP", "FOL", "TF", "CALIB"] do
    IO.println s!"TOTAL\t{r}\t{nDecl.getD r 0}\t{nGen.getD r 0}\t{nUsoRPP.getD r 0}\t{nUsoDentro.getD r 0}\t{nSinUso.getD r 0}"
  IO.println s!"SINRANGO\t{sinRango.size}\t{" ".intercalate ((sinRango.toList.map toString).take 10)}"
  -- (las de prueba que no tienen rango tiene que verlas generadas el primer filtro: si no, no se le ve fallar)
  let calibSinRango := sinRango.filter (fun c => (`IndiceCalib).isPrefixOf ((privateToUserName? c).getD c))
  IO.println s!"SINRANGOCALIB\t{calibSinRango.size}\t{" ".intercalate (calibSinRango.toList.map toString)}"
  IO.println s!"SINVALOR\t{sinValor}"
  IO.println s!"CORTADOS\t{nCortados}"
  IO.println "FIN"
EOF
} > "$LEANFILE"

GEN_I="$TMP/indice.tsv"; GEN_S="$TMP/sinuso.tsv"
T0=$(date +%s)
SALIDA=$(INDICE_RPP="$(win "$TMP/indice.crudo")" INDICE_SINUSO="$(win "$TMP/sinuso.crudo")" \
  INDICE_VIGILADAS="$(win "$VIGILADAS")" lake env lean "$(win "$LEANFILE")" 2>&1)
RC=$?
T1=$(date +%s)
FAIL=0
# (sin tubería hacia `grep -q`: con pipefail, el SIGPIPE de printf la daría por fallida)
if [ "$RC" != "0" ] || ! grep -qx 'FIN' <<< "$SALIDA"; then
  echo "  ❌ el censo no llegó al final (lake env lean salió con $RC):"
  printf '%s\n' "$SALIDA" | grep -v '^CALIB' | head -20 | sed 's/^/      /'
  exit 1
fi
echo "  censo: $NMODS módulos, $((T1 - T0)) s"
tr -d '\r' < "$TMP/indice.crudo" | grep . | LC_ALL=C sort > "$GEN_I"
tr -d '\r' < "$TMP/sinuso.crudo" | grep . | LC_ALL=C sort > "$GEN_S"

# la calibración: el índice, exactamente estas siete (con su enunciado); el uso, exactamente éste
CAL_I=$(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "CALIB" && $2 == "I" { print $3 "\t" $4 "\t" $6 }' | LC_ALL=C sort)
ESP_I=$(LC_ALL=C sort <<'EOF'
IndiceCalib.CalibI	inductivo	Type
IndiceCalib.CalibI.dos	constructor	Nat → IndiceCalib.CalibI
IndiceCalib.CalibI.uno	constructor	IndiceCalib.CalibI
IndiceCalib.calibM	def	IndiceCalib.CalibI → Nat
IndiceCalib.calibP	def·privada	Nat
IndiceCalib.calibR	def	Nat → Nat
IndiceCalib.calibT	teorema	∀ (n : Nat), n + 0 = n
IndiceCalib.calibU	teorema	3 + 0 = 3
EOF
)
if [ "$CAL_I" = "$ESP_I" ]; then
  echo "  ✓ calibración del índice: las ocho declaraciones de prueba (dos constructores), con su enunciado, y nada más"
else
  echo "  ❌ calibración del índice: no ve exactamente las declaraciones de prueba —no comprueba lo que dice—:"
  diff <(printf '%s\n' "$ESP_I") <(printf '%s\n' "$CAL_I") | sed 's/^/      /'
  FAIL=1
fi
CAL_U=$(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "CALIB" && $2 == "U" { print "usada " $3 } $1 == "CALIB" && $2 == "S" { print "sin uso " $4 }' | LC_ALL=C sort)
ESP_U=$(LC_ALL=C sort <<'EOF'
sin uso IndiceCalib.calibM
sin uso IndiceCalib.calibP
sin uso IndiceCalib.calibR
sin uso IndiceCalib.calibU
usada IndiceCalib.CalibI
usada IndiceCalib.calibT
EOF
)
if [ "$CAL_U" = "$ESP_U" ]; then
  echo "  ✓ calibración del uso: calibT y CalibI, usadas; calibU, calibP, calibM y calibR (la nombra su _sunfold), no"
else
  echo "  ❌ calibración del uso: la medida no dice lo esperado:"
  diff <(printf '%s\n' "$ESP_U") <(printf '%s\n' "$CAL_U") | sed 's/^/      /'
  FAIL=1
fi
SRCAL=$(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "SINRANGOCALIB" { print $2 "\t" $3 }')
if [ "${SRCAL%%	*}" != "0" ]; then
  echo "  ❌ calibración: de las de prueba, éstas sólo las quitó la falta de rango, no el filtro de las generadas: ${SRCAL#*	}"
  FAIL=1
fi
GENCAL=$(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "TOTAL" && $2 == "CALIB" { print $4 }')
if [ "${GENCAL:-0}" -lt 4 ]; then
  echo "  ❌ calibración: sólo ${GENCAL:-0} constantes generadas con las de prueba (el recursor, casesOn, match_1…): el filtro no las ve."
  FAIL=1
fi
SINV=$(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "SINVALOR" { print $2 }')
if [ "${SINV:-x}" != "0" ]; then
  echo "  ❌ $SINV teoremas o definiciones sin valor accesible: la medida de uso no los ve."
  FAIL=1
fi
printf '%s\n' "$SALIDA" | awk -F'\t' '
  $1 == "TOTAL" && $2 != "CALIB" { printf "  %-4s %5d declaradas (%5d generadas, fuera)", $2, $3, $4
    if ($2 != "RPP") printf " · %4d las usa RPP · %4d sólo FOL o TF · %4d nadie", $5, $6, $7
    printf "\n" }
  $1 == "SINRANGO" { printf "  %d constantes sin rango de declaración (generadas), fuera: %s\n", $2, $3 }
  $1 == "CORTADOS" && $2 > 0 { printf "  %d enunciados de más de 4000 caracteres, cortados (lo dice la línea)\n", $2 }'
echo "  lo que nadie usa, por etiqueta: $(awk -F'\t' '{ n[$4]++ } END { for (e in n) printf "%s %d · ", e, n[e] }' "$GEN_S" | sed 's/ · $//')"

if [ "$REHACER" = "1" ]; then
  {
    echo "# doc/indice.tsv — el ÍNDICE de las constantes DECLARADAS de RPP (sin las que genera Lean): nombre, clase, módulo y"
    echo "# enunciado, como lo imprime Lean con los nombres completos, en una línea. Lo genera y lo compara, en cada run de la CI,"
    echo "# check-indice.bash (L5-11, ADR-254); se rehace con «bash check-indice.bash --rehacer» en el commit que cambia una"
    echo "# declaración. Las de FOL y TheoryFramework, en ../FOL/doc/indice.tsv. Para buscar antes de construir:"
    echo "#   grep -i 'patrón' doc/indice.tsv ../FOL/doc/indice.tsv"
    echo "# nombre	clase	módulo	enunciado"
    cat "$GEN_I"
  } > "$INDICE"
  {
    echo "# doc/control/fol-sin-uso.tsv — las declaraciones de FOL y TheoryFramework que NINGUNA otra constante de RPP, FOL o"
    echo "# TheoryFramework nombra, en su tipo o en su valor (un constructor o un campo cuentan como su tipo); medido, no borrado"
    echo "# (FOL0912:B-5, ADR-254). La etiqueta: vigilada (fila de check-footprints: un titular), simp (simp puede usarla sin"
    echo "# rastro), instancia, meta (sintaxis o elaborador) o —. No cuenta los sondeos, el libro ni los consumidores archivados."
    echo "# La genera y la compara check-indice.bash; se rehace con «--rehacer»."
    echo "# módulo	nombre	clase	etiqueta"
    cat "$GEN_S"
  } > "$SINUSO"
  echo "  ✏️  $INDICE ($(grep -c . "$GEN_I") líneas) y $SINUSO ($(grep -c . "$GEN_S")), rehechas."
fi

compara() {  # tabla generado nombre
  if [ ! -f "$1" ]; then
    echo "  ❌ no existe $1."
    FAIL=1
    return
  fi
  local decl="$TMP/declarado.$3"
  grep -v '^#' "$1" | tr -d '\r' | grep . | LC_ALL=C sort > "$decl"
  local nuevas idas
  nuevas=$(LC_ALL=C comm -13 "$decl" "$2")
  idas=$(LC_ALL=C comm -23 "$decl" "$2")
  if [ -z "$nuevas" ] && [ -z "$idas" ]; then
    echo "  ✓ $1: $(grep -c . "$decl") líneas, las que se generan"
  else
    echo "  ❌ $1 NO es lo que se genera ($(printf '%s\n' "$nuevas" | grep -c .) de más en lo generado, $(printf '%s\n' "$idas" | grep -c .) de menos): «bash check-indice.bash --rehacer»"
    printf '%s\n' "$nuevas" | grep . | head -15 | cut -c1-200 | sed 's/^/      + /'
    printf '%s\n' "$idas" | grep . | head -15 | cut -c1-200 | sed 's/^/      - /'
    FAIL=1
  fi
}
compara "$INDICE" "$GEN_I" indice
compara "$SINUSO" "$GEN_S" sinuso

if [ "$FAIL" = "0" ]; then
  echo "✅ EL ÍNDICE Y LO QUE NADIE USA DE FOL, AL DÍA."
else
  echo "❌ EL ÍNDICE O LO QUE NADIE USA DE FOL NO CUADRAN (o la calibración falló)."
  exit 1
fi
