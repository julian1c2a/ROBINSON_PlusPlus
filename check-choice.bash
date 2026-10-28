#!/bin/bash
# check-choice.bash — la CONSTRUCTIVIDAD como control, en los dos repos (T53, ADR-193).
#
# ⛔ POR QUÉ EXISTE. Las cifras de constructividad se midieron una vez y nada las vigilaba: el censo de
# `sondeos/ClassicalChoiceCenso.lean` (2026-09-14), la auditoría de FOL (`../FOL/auditoria/constructividad-2026-09-27/`,
# 84 constantes con choice) y el «cierre de String» de D7 (3 líneas en RPP, 0 en FOL; ADR-129). `check-footprints`
# vigila los TITULARES (lo que el árbol imprime); esto vigila TODAS las constantes de las tres librerías.
#
# QUÉ MIDE. Para cada constante de los módulos `ROBINSON_PlusPlus*`, `FOL*` y `TheoryFramework*` (todos: el fichero
# Lean que genera importa cada módulo de las tres librerías, no sólo los barriles), sin las generadas (detalles
# internos —`match_N`, `proof_N`, `eq_N`, `_…`—, recursores auxiliares y `noConfusion`; una privada, con su nombre de
# usuario), tres marcas:
#   C  su cierre lleva `Classical.choice` (`collectAxioms`, lo mismo que `#print axioms`);
#   N  es `noncomputable`;
#   S  su tipo o su valor nombra DIRECTAMENTE `String` o una constante `String.*` (el «cierre de String» de D7, ahora
#      por constante y no por línea de código).
# Una línea por constante con alguna marca: «módulo · nombre · marcas», en `doc/control/choice.tsv`.
#
# ⭐ Rompe en LOS DOS SENTIDOS (ADR-032 §4: una cota no protege una cifra): una línea NUEVA es rojo, y una que
# DESAPARECE, también, hasta que la tabla baje. La tabla se rehace con `--rehacer`, sólo en el commit de un ADR que
# diga qué cambió y por qué (`git diff` de la tabla lo dice constante a constante).
#
# 🔑 CALIBRACIÓN (feedback de los controles que no comprueban nada): el fichero generado declara tres constantes de
# prueba —una con choice, una noncomputable, una con String— y el control exige verlas con su marca exacta; si el
# censo no corre, no ve nada o no llega al final (la línea FIN), es rojo, no verde.
#
# 🔧 Desde la raíz de RPP, con el build al día (`lake build` y `lake build "@FOL/FOL" "@FOL/TheoryFramework"`).
# Desde PowerShell, o desde Git Bash con `lake` en el PATH. Los objetivos de FOL, desde aquí (`@FOL/…`; M-3, ADR-205).
#
#   bash check-choice.bash            # mide y compara con la tabla
#   bash check-choice.bash --rehacer  # además, reescribe doc/control/choice.tsv con lo medido

set -uo pipefail
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

TABLA=doc/control/choice.tsv
REHACER=0
[ "${1:-}" = "--rehacer" ] && REHACER=1

echo "════ CONSTRUCTIVIDAD (choice · noncomputable · String) EN RPP, FOL Y TheoryFramework ════"

if ! command -v lake >/dev/null 2>&1; then
  echo "  ⚠️  SIN MEDIR — 'lake' no está en el PATH de este shell. Un control que no se ejecuta NO es un control."
  exit 2
fi

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
LEANFILE="$TMP/CensoChoice.lean"
# los módulos: cada fichero de las tres librerías (sus `globs` son `.andSubmodules`: todo el directorio se compila)
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
{
  sed 's/^/import /' "$MODS"
  cat <<'EOF'
open Lean

namespace CensoChoiceCalib
-- la calibración: el censo tiene que ver estas tres con su marca exacta
theorem calibC : ∀ p : Prop, p ∨ ¬p := Classical.em
noncomputable def calibN : Nat := Classical.choice ⟨0⟩
def calibS : String := "a"
end CensoChoiceCalib

def censoRaiz (m : Name) : Option String :=
  let r := m.getRoot.toString
  if r == "ROBINSON_PlusPlus" then some "RPP" else if r == "FOL" then some "FOL"
  else if r == "TheoryFramework" then some "TF" else none

#eval show CoreM Unit from do
  let env ← getEnv
  let mut filas : Array String := #[]
  let mut tot : Std.HashMap String (Nat × Nat × Nat × Nat) := {}
  let mut sinValor := 0
  for (c, ci) in env.constants.toList do
    let info : Option (String × String) := match env.getModuleIdxFor? c with
      | some i =>
        let m := env.header.moduleNames[i.toNat]!
        (censoRaiz m).map (fun r => (m.toString, r))
      | none => if (`CensoChoiceCalib).isPrefixOf c then some ("_calibracion", "CALIB") else none
    let some (modulo, repo) := info | continue
    let u := (privateToUserName? c).getD c
    if u.isInternalDetail || isAuxRecursor env c || isNoConfusion env c || isRecCore env c then continue
    -- (y los lemas que Lean genera con cada constructor)
    if let .str _ s := u then
      if ["noConfusionType", "inj", "injEq", "sizeOf_spec"].contains s then continue
    let axs ← collectAxioms c
    let tC := axs.contains ``Classical.choice
    let tN := isNoncomputable env c
    let val := ci.value? (allowOpaque := true)
    if val.isNone && (ci.isTheorem || ci.isDefinition) then sinValor := sinValor + 1
    let usados := ci.type.getUsedConstants ++ ((val.map (·.getUsedConstants)).getD #[])
    let tS := usados.any (fun d => d.getRoot == `String)
    let (n0, n1, n2, n3) := tot.getD repo (0, 0, 0, 0)
    tot := tot.insert repo (n0 + 1, n1 + (if tC then 1 else 0), n2 + (if tN then 1 else 0), n3 + (if tS then 1 else 0))
    if tC || tN || tS then
      let marcas := (if tC then "C" else "") ++ (if tN then "N" else "") ++ (if tS then "S" else "")
      filas := filas.push s!"FILA\t{modulo}\t{u}\t{marcas}"
  for f in filas do IO.println f
  for (r, (n0, n1, n2, n3)) in tot.toList do
    IO.println s!"TOTAL\t{r}\t{n0}\t{n1}\t{n2}\t{n3}"
  IO.println s!"SINVALOR\t{sinValor}"
  IO.println "FIN"
EOF
} > "$LEANFILE"

T0=$(date +%s)
SALIDA=$(lake env lean "$LEANFILE" 2>&1)
RC=$?
T1=$(date +%s)
FAIL=0
# (sin tubería hacia `grep -q`: con pipefail, el SIGPIPE de printf la daría por fallida)
if [ "$RC" != "0" ] || ! grep -qx 'FIN' <<< "$SALIDA"; then
  echo "  ❌ el censo no llegó al final (lake env lean salió con $RC):"
  printf '%s\n' "$SALIDA" | grep -v '^FILA' | head -20 | sed 's/^/      /'
  exit 1
fi
echo "  censo: $NMODS módulos, $((T1 - T0)) s"

# la calibración
for esp in "CensoChoiceCalib.calibC	C" "CensoChoiceCalib.calibN	CN" "CensoChoiceCalib.calibS	S"; do
  if grep -qxF "FILA	_calibracion	$esp" <<< "$SALIDA"; then
    echo "  ✓ calibración: $(printf '%s' "$esp" | tr '\t' ' ')"
  else
    echo "  ❌ calibración: el censo no ve «$(printf '%s' "$esp" | tr '\t' ' ')» — no comprueba lo que dice."
    FAIL=1
  fi
done
SINV=$(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "SINVALOR" { print $2 }')
if [ "${SINV:-x}" != "0" ]; then
  echo "  ❌ $SINV teoremas o definiciones sin valor accesible: la marca S no los ve."
  FAIL=1
fi

MEDIDO="$TMP/medido.tsv"
printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "FILA" && $2 != "_calibracion" { print $2 "\t" $3 "\t" $4 }' | LC_ALL=C sort > "$MEDIDO"
printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "TOTAL" && $2 != "CALIB" { printf "  %-4s %6d constantes · %4d con choice · %2d noncomputable · %3d con String\n", $2, $3, $4, $5, $6 }' | LC_ALL=C sort

# por módulo, lo que lleva choice (para leer; la comparación es constante a constante)
echo "  con choice, por módulo:"
awk -F'\t' 'index($3, "C") { n[$1]++ } END { for (m in n) printf "      %4d  %s\n", n[m], m }' "$MEDIDO" | LC_ALL=C sort -k2

if [ "$REHACER" = "1" ]; then
  {
    echo "# doc/control/choice.tsv — las constantes de RPP, FOL y TheoryFramework con Classical.choice (C), noncomputable (N)"
    echo "# o String en su tipo o su valor (S); sin las generadas. La mide y la compara check-choice.bash (T53, ADR-193), en"
    echo "# los dos sentidos. Se rehace con «bash check-choice.bash --rehacer», sólo en el commit de un ADR que lo explique."
    echo "# módulo	nombre	marcas"
    cat "$MEDIDO"
  } > "$TABLA"
  echo "  ✏️  $TABLA, rehecha: $(grep -c . "$MEDIDO") líneas."
fi

if [ ! -f "$TABLA" ]; then
  echo "  ❌ no existe $TABLA."
  exit 1
fi
DECL="$TMP/declarado.tsv"
grep -v '^#' "$TABLA" | tr -d '\r' | grep . | LC_ALL=C sort > "$DECL"
NUEVAS=$(LC_ALL=C comm -13 "$DECL" "$MEDIDO")
IDAS=$(LC_ALL=C comm -23 "$DECL" "$MEDIDO")
if [ -n "$NUEVAS" ]; then
  echo "  ❌ medidas y NO declaradas ($(printf '%s\n' "$NUEVAS" | grep -c .)):"
  printf '%s\n' "$NUEVAS" | head -30 | sed 's/^/      + /'
  FAIL=1
fi
if [ -n "$IDAS" ]; then
  echo "  ❌ declaradas y YA NO medidas ($(printf '%s\n' "$IDAS" | grep -c .)): baja la tabla (--rehacer, con su ADR):"
  printf '%s\n' "$IDAS" | head -30 | sed 's/^/      - /'
  FAIL=1
fi
if [ "$FAIL" = "0" ]; then
  echo "✅ LA TABLA CUADRA: $(grep -c . "$DECL") constantes con alguna marca, las mismas en los dos sentidos."
else
  echo "❌ LA CONSTRUCTIVIDAD NO CUADRA CON $TABLA."
  exit 1
fi
