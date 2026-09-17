#!/usr/bin/env bash
# check-footprints.bash — comprueba que los teoremas TITULARES tienen EXACTAMENTE el footprint
# que la documentación publica. ROMPE si alguno no cuadra.
#
# ⛔ POR QUÉ EXISTE (2026-09-14, criterio §9 de doc/PLAN-COMPLETITUD-FINITISTA.md):
# los footprints se imprimen en el build como `info:` — y un `info:` en medio de 145 jobs
# NO ES UN CONTROL: nadie lo lee, y si cambia no rompe nada. `check-axioms.bash` cuenta
# `axiom` declarados; esto mide lo que de verdad importa, que es de qué DEPENDE cada
# teorema.
#
# ⚠️ Un footprint es la única evidencia que este proyecto acepta (feedback_auditoria_footprint).
# Publicar una cifra y no volver a medirla es exactamente lo que ADR-032 §4 llama una
# medición falsa.
#
# 🔧 EJECUTAR DESDE POWERSHELL: desde Bash, `lake` no está en el PATH (y el propio script
#    lo dice en vez de callarse, que es la lección de feedback_controles_que_no_comprueban).
# ⛔ Y desde la raíz de ROBINSON_PlusPlus, NUNCA `cd FOL && lake ...`.
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

# ── La tabla: declaración ⇒ footprint esperado (nombres ORDENADOS alfabéticamente) ─────────
# «-» significa: no depende de ningún axioma.
read -r -d '' TABLA <<'EOF'
Derives₀.rec|propext
derives0_to_derives|propext
FOL.Metamath.Soundness0.derives0_soundness|Classical.choice,Quot.sound,propext
FOL.Metamath.Soundness0.derives0_consistent|Classical.choice,Quot.sound,propext
FOL.Metamath.Soundness0.derives0_not_complete|Classical.choice,Quot.sound,propext
FOL.Metamath.Enumeration.natToFormula_surj|Classical.choice,Quot.sound,propext
FOL.Metamath.Semantics.shift_updateEnv_comm|Quot.sound,propext
FOL.Metamath.Semantics.eval_liftFormula_ext|Quot.sound,propext
FOL.Metamath.Semantics.eval_substFormula_ext|Quot.sound,propext
FOL.Metamath.Semantics.contextSatisfies_lift_zero|Quot.sound,propext
FOL.Rename.derives0_rename|Quot.sound,propext
FOL.Rename.derives0_rename_inv|Quot.sound,propext
FOL.Rename.derives0_rename_iff|Quot.sound,propext
FOL.Rename.derives0_rename_conservative|Classical.choice,Quot.sound,propext
FOL.Eigenvariable.absDerives|Quot.sound,propext
FOL.Eigenvariable.derives0_gen_fresh|Quot.sound,propext
FOL.Eigenvariable.derives0_inst_fresh|Quot.sound,propext
FOL.Lift0.derives0_lift|Quot.sound,propext
FOL.Lift0.derives0_ex_forall_neg_absurd|Quot.sound,propext
FOL.Henkin0.henkin_step_consistent|Classical.choice,Quot.sound,propext
FOL.Fresh0.derivesSet0_shift_inv|Classical.choice,Quot.sound,propext
FOL.Fresh0.shiftTheory_consistent|Classical.choice,Quot.sound,propext
FOL.Fresh0.exists_fresh|Classical.choice,Quot.sound,propext
FOL.HenkinLimit0.not_occurs_henkinAx|-
FOL.HenkinLimit0.henLimit_consistent|Classical.choice,Quot.sound,propext
FOL.HenkinLimit0.henLimit_witness|Classical.choice,Quot.sound,propext
FOL.Lindenbaum0.lindenbaum_lemma|Classical.choice,Quot.sound,propext
FOL.Lindenbaum0.henkin_completion|Classical.choice,Quot.sound,propext
FOL.Eq0.derives0_eq_func_congr|Quot.sound,propext
FOL.Eq0.derives0_atom_congr|Quot.sound,propext
FOL.Canonical0.truth_lemma|Classical.choice,Quot.sound,propext
FOL.Canonical0.eval_pullback_formula|-
FOL.Canonical0.model_existence_lemma₀|Classical.choice,Quot.sound,propext
FOL.Canonical0.completeness₀|Classical.choice,Quot.sound,propext
FOL.Canonical0.derives0_complete_iff|Classical.choice,Quot.sound,propext
FOL.Canonical0.derives0_em|Classical.choice,Quot.sound,propext
FOL.DecEq.instDecidableEqTerm|-
instDecidableEqFormula|-
FOL.Propositional0.derives0_em_ctx|-
FOL.Propositional0.kalmar|propext
FOL.Propositional0.derives0_of_ptaut|Quot.sound,propext
FOL.Propositional0.derives0_of_ptaut_ctx|Quot.sound,propext
FOL.Propositional0.derives0_em_prop|Quot.sound,propext
FOL.Propositional0.derives0_peirce_prop|Quot.sound,propext
FOL.Herbrand0.ptaut_of_check|propext
FOL.Herbrand0.derives0_discharge|-
FOL.Herbrand0.derives0_of_eqInstance|Quot.sound,propext
FOL.Herbrand0.derives0_ex_of_cert|Quot.sound,propext
FOL.Herbrand0.herbrand_iff|Quot.sound,propext
FOL.Herbrand0.ex_igualdad|Quot.sound,propext
Derives₁.rec|-
FOL.Derives1.rewrite_equiv|Quot.sound,propext
FOL.Derives1.rewrite_at_admissible|Quot.sound,propext
FOL.Derives1.derives0_to_derives1|Quot.sound,propext
FOL.Derives1.derives0_iff_derives1|Quot.sound,propext
Derives₂.rec|-
FOL.Derives2.derives2_lift|Quot.sound,propext
FOL.Derives2.eq_substTerm|propext
FOL.Derives2.eq_substFormula|Quot.sound,propext
FOL.Derives2.derives1_to_derives2|Quot.sound,propext
FOL.Derives2.derives0_iff_derives2|Quot.sound,propext
LK₀.rec|-
FOL.Sequent0.quantFree_subst|-
FOL.Sequent0.lk0_herbrand|propext
FOL.Sequent0.lk0_to_lkc|-
FOL.Sequent0.herbrandExtraction_of|Quot.sound,propext
FOL.SequentSound0.lkc_sound|Classical.choice,Quot.sound,propext
FOL.SequentSound0.lk0_to_derives0|Classical.choice,Quot.sound,propext
FOL.SequentSound0.lk0_not_empty|Classical.choice,Quot.sound,propext
FOL.SequentSound0.eqInstance_valid|-
FOL.NDtoLK0.mpLK|-
FOL.NDtoLK0.ndToLK|Quot.sound,propext
FOL.NDtoLK0.herbrandExtraction_of_cutElim|Quot.sound,propext
FOL.Hauptsatz0.cutElim_of|-
FOL.Hauptsatz0.lkh_mono|-
FOL.Hauptsatz0.lkh_to_lk0|-
FOL.Hauptsatz0.lk0_to_lkh|propext
FOL.Hauptsatz0.liftFormula_subst_le|Quot.sound,propext
FOL.Hauptsatz0.substFormula_subst_le|Quot.sound,propext
FOL.Hauptsatz0.eqInstance_subst|-
FOL.Hauptsatz0.lkh_subst|Quot.sound,propext
FOL.derive_eq_func_congr|Quot.sound,propext
FOL.derive_atom_congr|Quot.sound,propext
FOL.substTerm_liftTerm|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Provability.charsCode|-
ROBINSON_PlusPlus.Minimal.Axioms.axiomsCodeT|-
ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf|Classical.choice,Quot.sound,propext
EOF

TMP=$(mktemp -d)
LEANFILE="$TMP/Footprints.lean"
{
  echo "import ROBINSON_PlusPlus"
  echo "import FOL"
  while IFS='|' read -r NOMBRE _; do
    [ -n "$NOMBRE" ] || continue
    echo "#print axioms $NOMBRE"
  done <<< "$TABLA"
} > "$LEANFILE"

echo "════ FOOTPRINTS DE LOS TITULARES ════"

if ! command -v lake >/dev/null 2>&1; then
  echo "  ⚠️  SIN MEDIR — 'lake' no está en el PATH de este shell."
  echo "      Lánzalo desde PowerShell. Un control que no se ejecuta NO es un control."
  rm -rf "$TMP"
  exit 2
fi

SALIDA=$(lake env lean "$LEANFILE" 2>&1)
RC=$?
# ⚠️ `#print axioms` PARTE LA LÍNEA cuando la lista es larga. Se aplasta todo a una sola
# línea antes de buscar: si no, los footprints de tres axiomas no casan nunca.
PLANA=$(printf '%s' "$SALIDA" | tr '\n' ' ' | tr -s ' ')

FAIL=0
N=0
while IFS='|' read -r NOMBRE ESPERADO; do
  [ -n "$NOMBRE" ] || continue
  N=$((N + 1))
  SEG=$(printf '%s' "$PLANA" \
        | grep -oF -e "'$NOMBRE' does not depend on any axioms" -e "'$NOMBRE' depends on axioms: [" \
        | head -1)
  if [ -z "$SEG" ]; then
    # ⛔ La causa raíz de «un verde que no comprueba»: el patrón no aparece. Rompe.
    printf "  ✗ %-55s NO MEDIDO — la declaración no aparece en la salida\n" "$NOMBRE"
    FAIL=1
    continue
  fi
  if printf '%s' "$SEG" | grep -qF 'does not depend'; then
    REAL="-"
  else
    REAL=$(printf '%s' "$PLANA" \
           | sed -E "s/.*'$(printf '%s' "$NOMBRE" | sed 's/[.[\*^$]/\\&/g')' depends on axioms: \[([^]]*)\].*/\1/" \
           | tr -d ' ' )
    REAL=$(printf '%s' "$REAL" | tr ',' '\n' | sort | paste -sd, -)
  fi
  ESP=$(printf '%s' "$ESPERADO" | tr ',' '\n' | sort | paste -sd, -)
  if [ "$REAL" = "$ESP" ]; then
    printf "  ✓ %-55s %s\n" "$NOMBRE" "$REAL"
  else
    printf "  ✗ %-55s dice [%s], esperado [%s]\n" "$NOMBRE" "$REAL" "$ESP"
    FAIL=1
  fi
done <<< "$TABLA"

rm -rf "$TMP"

echo
if [ "$N" = "0" ]; then
  echo "❌ LA TABLA ESTÁ VACÍA — el control no comprueba nada."
  exit 1
fi
if [ "$FAIL" = "0" ]; then
  echo "✅ LOS $N FOOTPRINTS CUADRAN."
else
  echo "❌ ALGÚN FOOTPRINT NO CUADRA."
  echo "   O el código cambió de dependencias (⇒ mirar QUÉ entró, puede ser grave),"
  echo "   o la tabla de este script está obsoleta (⇒ actualizarla Y la documentación)."
  [ "$RC" != "0" ] && echo "   ⚠️  Además, 'lake env lean' salió con código $RC."
fi
exit "$FAIL"
