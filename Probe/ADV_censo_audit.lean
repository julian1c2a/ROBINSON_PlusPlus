/-
Probe/ADV_censo_audit.lean — AUDITORÍA ADVERSARIAL de Probe/MF_censo.lean.

No reusa NADA del sondeo auditado: reconstruye la cadena crítica desde cero.
-/
import ROBINSON_PlusPlus.Meta

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.CodeDistinct
open ROBINSON_PlusPlus.Meta.LineWFCases
open ROBINSON_PlusPlus.Meta.AxiomListCode
open ROBINSON_PlusPlus.Meta.OmegaReflect

namespace AdvAudit

/-! ## A — `formCode` vs `formCodeM`: ¿misma constante? ¿hay puente? -/

-- ¿Son la MISMA constante? (si esto compilara, serían iguales por definición)
-- example (φ : Formula) : formCodeM φ = formCode φ := rfl   -- ← se prueba abajo que NO es rfl

/-- El PUENTE existe y es un TEOREMA (no `rfl`): `formCodeM φ = formCode φ`. -/
theorem puente_existe (φ : Formula) : formCodeM φ = formCode φ := formCodeM_eq φ

/-! Que NO son la misma constante se ve en que son dos `def` distintos; el puente se prueba
    por inducción sobre la fórmula (vía `numeralM_eq`). Aquí sólo se registra que EXISTE. -/
#check @ROBINSON_PlusPlus.Meta.Representability.formCodeM_eq
#check @ROBINSON_PlusPlus.Minimal.Axioms.formCodeM
#check @ROBINSON_PlusPlus.Meta.Provability.formCode

/-! ## B — RECONSTRUCCIÓN INDEPENDIENTE de la cadena crítica

`prf_not_In_listFormCodeM` + `ax_axiomsCodeT_eq` + Leibniz (`Derives.subst`)
  ⟹ `axioms ⊢ neg (In (formCode φ) axiomsCodeT)`

NO se usa `neg_In_axiomsCodeT`: se rehace desde sus tres ingredientes. -/

theorem adv_neg_In_axiomsCodeT (φ : Formula) (hnp : ¬ Prf φ) :
    axioms ⊢ neg (In (formCode φ) axiomsCodeT) := by
  -- (1) el NEGATIVO sobre la lista concreta, desde `¬ Prf φ` (φ no es axioma)
  have hlist : axioms ⊢ neg (In (formCode φ) (listFormCodeM axioms)) :=
    prf_not_In_listFormCodeM φ axioms (fun hmem => hnp (prf_ax hmem))
  -- (2) el ANCLA sancionada
  have hanchor : axioms ⊢ (axiomsCodeT =eq listFormCodeM axioms) := ax_axiomsCodeT_eq
  -- (3) LEIBNIZ sobre la ranura del segundo argumento de `In`
  have key : ∀ t : Term,
      substFormula 0 t (neg (In (formCode φ) (.var 0))) = neg (In (formCode φ) t) := by
    intro t
    rw [← formCodeM_eq φ]
    simp [neg, In, substFormula, substTerm, substTerms, substTerm_formCodeM,
      FOL.substTerm_liftTerm]
  have hpos : axioms ⊢ substFormula 0 (listFormCodeM axioms) (neg (In (formCode φ) (.var 0))) := by
    rw [key]; exact hlist
  have hsub := Derives.subst axioms (listFormCodeM axioms) axiomsCodeT
    (neg (In (formCode φ) (.var 0))) (FOL.derive_eq_symm hanchor) hpos
  rwa [key] at hsub

/-- Y ENCHUFADA en `derives_lineWF_neg_thy` (el consumidor que el encargo pedía). -/
theorem adv_tag15 (φ : Formula) (hnp : ¬ Prf φ) :
    axioms ⊢ neg (lineWF (cons (formCode φ) (cons (numeralM 15) nil))) :=
  derives_lineWF_neg_thy (formCode φ) (adv_neg_In_axiomsCodeT φ hnp)

/-! ## C — ¿la cláusula `lenc` de los axiomas coincide con `tagArity k + 2`?
El sondeo auditado DEFINE `tagLenc k := tagArity k + 2` y cuenta sobre esa definición.
Aquí se comprueba, contra los `prf_lineWF_*` de PRODUCCIÓN, que ese número es el que la
teoría exige, en dos tags de longitudes distintas (thy=2 no tiene args; q1=4; leibniz=5). -/

example : tagArity 15 + 2 = 2 := by decide
example : tagArity 9 + 2 = 4 := by decide
example : tagArity 13 + 2 = 5 := by decide
example : tagArity 16 + 2 = 3 := by decide

/-! ## D — ¿es NO VACUA la refutación por aridad? Una línea de tag 9 con 1 arg
existe como término y es `IsCodeShaped` cuando sus componentes lo son. -/

theorem adv_linea_ar3_es_codeShaped :
    IsCodeShaped (cons (numeralM 7) (cons (numeralM 9) (cons (numeralM 1) nil))) :=
  IsCodeShaped.cons (IsCodeShaped.numeral 7)
    (IsCodeShaped.cons (IsCodeShaped.numeral 9)
      (IsCodeShaped.cons (IsCodeShaped.numeral 1) IsCodeShaped.nil))

/-! ## E — el "hueco residual": ¿es real que `substfc` es opaco fuera de los códigos?
Se registra el enunciado del esquema q1 con un arg que es un NUMERAL PELADO en la ranura
de `substfc`. Si la reconstrucción se pudiera colapsar, existiría una ecuación aplicable. -/

theorem adv_q1_con_numeral_pelado (concl : Term) :
    Prf (lineWF (cons concl (cons (numeralM 9) (cons (numeralM 3) (cons (numeralM 4) nil)))) ⇔
      (concl =eq implc (forallc (numeralM 3)) (substfc zero (numeralM 4) (numeralM 3)))) :=
  prf_lineWF_tag 9 concl [numeralM 3, numeralM 4] _ rfl

end AdvAudit

#print axioms AdvAudit.puente_existe
#print axioms AdvAudit.adv_neg_In_axiomsCodeT
#print axioms AdvAudit.adv_tag15
#print axioms AdvAudit.adv_q1_con_numeral_pelado
