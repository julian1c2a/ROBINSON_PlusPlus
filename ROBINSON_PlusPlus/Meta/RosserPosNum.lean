/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Representability2Prf
import ROBINSON_PlusPlus.Meta.SolidezVerificador
import ROBINSON_PlusPlus.Meta.PurezaComando

/-!
# `Meta/RosserPosNum.lean` — Rosser, etapa 6: PosNum (ADR‑146, ADR‑147, ADR‑149)

**Qué.** `PfF y x`, el predicado de prueba de T con la prueba y la conclusión como términos, y **`posNum`**: si
`Prf φ`, hay un NUMERAL `m̄` con `Prf (PfF m̄ ⌜φ⌝)`. Es D1 con el testigo en forma de numeral, que es lo que pide
Rosser: allí las pruebas se comparan, numeral a numeral, con las de `¬R`.

**Cómo.** D1 (`repr_pos'_prf`) ya construye un término de prueba explícito, `proofCode' rs []`, y prueba sus dos
mitades (`prf_chainOk_track`, `prf_In_runFn_of_mem`). Ese término es un árbol de `cons` cuyas hojas son códigos de
fórmulas y de términos y numerales de etiqueta. Aquí se prueba que ES el numeral de su valor
(`prf_proofCode'_numeral`), con el espejo en ℕ del codificador (`codeNatJustif`, `codeNatLine`, `codeNatProof`, copia
de `Meta/Representability2.lean`), y las dos mitades se transportan por esa igualdad. No hace falta el espejo del
verificador (`ModeloCodigo`): basta que el código de la prueba sea un numeral (ADR‑146 §1).

**Controles.** `prov_of_pfF`: `PfF` es la matriz de `provCodeC'`, así que un testigo da `Prov(⌜φ⌝)`; con `posNum`,
`repr_pos_num` es D1 otra vez, por un numeral. Y el `#pureza` del final: lo de la etapa no nombra la semántica, y
`modelo_prov_iff` —D1 leído en el modelo— sí.

⛔ Ningún código se evalúa: `codeNat`, `codeNatTerm` y `codeNatProof` sólo se mueven por unificación estructural y por
`rw` (ADR‑130).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.HilbertSeq ROBINSON_PlusPlus.Meta.ProofChain ROBINSON_PlusPlus.Meta.Representability2
open ROBINSON_PlusPlus.Meta.Representability2Prf ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf

namespace ROBINSON_PlusPlus.Meta.RosserPosNum

/-! ## §1 · El espejo en ℕ del codificador de pruebas (copia de `Meta/Representability2.lean`) -/

/-- El valor en ℕ de `lineJustif acc r`. -/
def codeNatJustif (acc : List Formula) : Rule → Nat
  | .p1 A B => consN 0 (consN (codeNat A) (consN (codeNat B) 0))
  | .p2 A B C => consN 1 (consN (codeNat A) (consN (codeNat B) (consN (codeNat C) 0)))
  | .c1 A B => consN 2 (consN (codeNat A) (consN (codeNat B) 0))
  | .c2 A B => consN 3 (consN (codeNat A) (consN (codeNat B) 0))
  | .c3 A B => consN 4 (consN (codeNat A) (consN (codeNat B) 0))
  | .j1 A B => consN 5 (consN (codeNat A) (consN (codeNat B) 0))
  | .j2 A B => consN 6 (consN (codeNat A) (consN (codeNat B) 0))
  | .j3 A B C => consN 7 (consN (codeNat A) (consN (codeNat B) (consN (codeNat C) 0)))
  | .efq A => consN 8 (consN (codeNat A) 0)
  | .q1 A t => consN 9 (consN (codeNat A) (consN (codeNatTerm t) 0))
  | .q2 A t => consN 10 (consN (codeNat A) (consN (codeNatTerm t) 0))
  | .q3 A B => consN 11 (consN (codeNat A) (consN (codeNat B) 0))
  | .eqrefl t => consN 12 (consN (codeNatTerm t) 0)
  | .leibniz A t₁ t₂ => consN 13 (consN (codeNat A) (consN (codeNatTerm t₁) (consN (codeNatTerm t₂) 0)))
  | .p3 A => consN 14 (consN (codeNat A) 0)
  | .ind A => consN 18 (consN (codeNat A) 0)
  | .qconf P C => consN 19 (consN (codeNat P) (consN (codeNat C) 0))
  | .listInd A => consN 20 (consN (codeNat A) 0)
  | .thy _ => consN 15 0
  | .mp _ j => consN 16 (consN (codeNat ((acc[j]?).getD Formula.bottom)) 0)
  | .gen i => consN 17 (consN (codeNat ((acc[i]?).getD Formula.bottom)) 0)

/-- El valor en ℕ de `lineCode' acc f r`. -/
def codeNatLine (acc : List Formula) (f : Formula) (r : Rule) : Nat := consN (codeNat f) (codeNatJustif acc r)

/-- El valor en ℕ de `proofCode' rs acc`. -/
def codeNatProof : List Rule → List Formula → Nat
  | [], _ => 0
  | r :: rs, acc =>
      match stepConcl acc r with
      | some f => consN (codeNatLine acc f r) (codeNatProof rs (acc ++ [f]))
      | none => 0

/-! ## §2 · El término de prueba de D1 ES el numeral de su valor -/

/-- La justificación de una línea es el numeral de su valor: las 21 reglas. -/
theorem prf_lineJustif_numeral (acc : List Formula) :
    ∀ r : Rule, Prf (lineJustif acc r =eq numeral (codeNatJustif acc r))
  | .p1 A B => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A)
      (prf_cons_eval_of (prf_formCode_numeral B) (prf_refl nil)))
  | .p2 A B C => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A)
      (prf_cons_eval_of (prf_formCode_numeral B) (prf_cons_eval_of (prf_formCode_numeral C) (prf_refl nil))))
  | .c1 A B => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A)
      (prf_cons_eval_of (prf_formCode_numeral B) (prf_refl nil)))
  | .c2 A B => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A)
      (prf_cons_eval_of (prf_formCode_numeral B) (prf_refl nil)))
  | .c3 A B => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A)
      (prf_cons_eval_of (prf_formCode_numeral B) (prf_refl nil)))
  | .j1 A B => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A)
      (prf_cons_eval_of (prf_formCode_numeral B) (prf_refl nil)))
  | .j2 A B => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A)
      (prf_cons_eval_of (prf_formCode_numeral B) (prf_refl nil)))
  | .j3 A B C => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A)
      (prf_cons_eval_of (prf_formCode_numeral B) (prf_cons_eval_of (prf_formCode_numeral C) (prf_refl nil))))
  | .efq A => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A) (prf_refl nil))
  | .q1 A t => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A)
      (prf_cons_eval_of (prf_termCode_numeral t) (prf_refl nil)))
  | .q2 A t => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A)
      (prf_cons_eval_of (prf_termCode_numeral t) (prf_refl nil)))
  | .q3 A B => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A)
      (prf_cons_eval_of (prf_formCode_numeral B) (prf_refl nil)))
  | .eqrefl t => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_termCode_numeral t) (prf_refl nil))
  | .leibniz A t₁ t₂ => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A)
      (prf_cons_eval_of (prf_termCode_numeral t₁) (prf_cons_eval_of (prf_termCode_numeral t₂) (prf_refl nil))))
  | .p3 A => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A) (prf_refl nil))
  | .ind A => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A) (prf_refl nil))
  | .qconf P C => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral P)
      (prf_cons_eval_of (prf_formCode_numeral C) (prf_refl nil)))
  | .listInd A => prf_cons_eval_of (prf_refl _) (prf_cons_eval_of (prf_formCode_numeral A) (prf_refl nil))
  | .thy _ => prf_cons_eval_of (prf_refl (numeral 15)) (prf_refl (numeral 0))
  | .mp _ j => prf_cons_eval_of (prf_refl _)
      (prf_cons_eval_of (prf_formCode_numeral ((acc[j]?).getD Formula.bottom)) (prf_refl nil))
  | .gen i => prf_cons_eval_of (prf_refl _)
      (prf_cons_eval_of (prf_formCode_numeral ((acc[i]?).getD Formula.bottom)) (prf_refl nil))

/-- Una línea es el numeral de su valor: la conclusión y la justificación. -/
theorem prf_lineCode'_numeral (acc : List Formula) (f : Formula) (r : Rule) :
    Prf (lineCode' acc f r =eq numeral (codeNatLine acc f r)) :=
  prf_cons_eval_of (prf_formCode_numeral f) (prf_lineJustif_numeral acc r)

/-- 🏁 **El término de prueba de D1 es el numeral de su valor**: `proofCode' rs acc =eq ⟨codeNatProof rs acc⟩‾`.
    Por inducción sobre la lista de reglas, con el esqueleto de `prf_runFn_track`. -/
theorem prf_proofCode'_numeral (rs : List Rule) : ∀ acc : List Formula,
    Prf (proofCode' rs acc =eq numeral (codeNatProof rs acc)) := by
  induction rs with
  | nil => intro acc; exact prf_refl nil
  | cons r rs ih =>
      intro acc
      cases hsc : stepConcl acc r with
      | none =>
          rw [show proofCode' (r :: rs) acc = nil from by simp [proofCode', hsc],
            show codeNatProof (r :: rs) acc = 0 from by simp [codeNatProof, hsc]]
          exact prf_refl nil
      | some f =>
          rw [show proofCode' (r :: rs) acc = cons (lineCode' acc f r) (proofCode' rs (acc ++ [f]))
                from by simp [proofCode', hsc],
            show codeNatProof (r :: rs) acc = consN (codeNatLine acc f r) (codeNatProof rs (acc ++ [f]))
                from by simp [codeNatProof, hsc]]
          exact prf_cons_eval_of (prf_lineCode'_numeral acc f r) (ih (acc ++ [f]))

/-! ## §3 · PosNum -/

/-- El predicado de prueba de T (ADR‑146 §1): `y` es una cadena correcta que concluye `x`. Es la matriz de
    `provFormulaC'`, con la prueba y la conclusión como términos. -/
def PfF (y x : Term) : Formula := land (chainOk nil y) (In x (runFn nil y))

/-- PosNum con su testigo: el numeral del valor del término de prueba de D1. -/
theorem posNum_de {rs : List Rule} {L : List Formula} {φ : Formula}
    (hchk : checkAux rs [] = some L) (hmem : φ ∈ L) :
    Prf (PfF (numeralM (codeNatProof rs [])) (formCode φ)) := by
  have heq : Prf (proofCode' rs [] =eq numeralM (codeNatProof rs [])) := by
    rw [numeralM_eq]; exact prf_proofCode'_numeral rs []
  exact prf_and_intro (prf_chainOk_subst2 heq (prf_chainOk_track rs [] L hchk))
    (prf_eq_subst_in (prf_congr_runFn_2 heq) (prf_In_runFn_of_mem hchk hmem))

/-- 🏁 **PosNum** (ADR‑146 §1): todo teorema de `Prf` tiene una prueba cuyo código es un NUMERAL. -/
theorem posNum {φ : Formula} (h : Prf φ) : ∃ m : Nat, Prf (PfF (numeralM m) (formCode φ)) := by
  obtain ⟨rs, L, hchk, hmem⟩ := prf_iff_derivation.mp h
  have hchk' : checkAux rs [] = some L := by simpa [checkProof] using hchk
  exact ⟨codeNatProof rs [], posNum_de hchk' hmem⟩

/-! ## §4 · Los controles -/

/-- ✅ `PfF` es la matriz de `provCodeC'`: un testigo cualquiera da `Prov(⌜φ⌝)`. -/
theorem prov_of_pfF {t : Term} {φ : Formula} (h : Prf (PfF t (formCode φ))) : Prf (provCodeC' φ) :=
  provCodeC'_intro_prf φ t (prf_and_elim_left h) (prf_and_elim_right h)

/-- ✅ Con `posNum`, D1 otra vez, ahora por un numeral: el enunciado de PosNum no dice menos que D1. -/
theorem repr_pos_num {φ : Formula} (h : Prf φ) : Prf (provCodeC' φ) :=
  (posNum h).elim fun _ hm => prov_of_pfF hm

end ROBINSON_PlusPlus.Meta.RosserPosNum

-- `prf_proofCode'_numeral` no lleva `#print axioms`: [COBERTURA] de `check-footprints.bash` extrae los nombres con
-- `'[^']+'` y una prima lo corta (por eso D1, `repr_pos'_prf`, tampoco tiene fila: T11b). Su footprint va en el de
-- `posNum`, que lo usa.
#print axioms ROBINSON_PlusPlus.Meta.RosserPosNum.posNum
#print axioms ROBINSON_PlusPlus.Meta.RosserPosNum.repr_pos_num

/-! T08 en el módulo (ADR‑147): lo de esta etapa no nombra la semántica; `modelo_prov_iff`, D1 leído en el modelo,
    sí. Si un paso de aquí pasara por el modelo, el build fallaría en este módulo. -/
#pureza ROBINSON_PlusPlus.Meta.RosserPosNum.prf_proofCode'_numeral ROBINSON_PlusPlus.Meta.RosserPosNum.posNum
  ROBINSON_PlusPlus.Meta.RosserPosNum.repr_pos_num
  | ROBINSON_PlusPlus.Meta.SolidezVerificador.modelo_prov_iff
