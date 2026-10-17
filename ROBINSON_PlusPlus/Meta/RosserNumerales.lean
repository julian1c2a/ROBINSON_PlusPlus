/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.NumListPrf
import ROBINSON_PlusPlus.Meta.CodeNumeralPrf
import ROBINSON_PlusPlus.Meta.ModeloEstandar
import ROBINSON_PlusPlus.Meta.PurezaComando

/-!
# `Meta/RosserNumerales.lean` — Rosser, etapa 1: la capa de listas sobre numerales (ADR‑146, ADR‑147, ADR‑150)

**Qué.** NegNum se construye como «T decide el espejo de `ModeloCodigo` sobre numerales» (ADR‑146 §4). Esta es la capa
de abajo: las listas. Sobre un numeral `m̄`, `Prf` descompone, accede y decide la pertenencia como lo hace ℕ:

* **§1** `cons ā b̄ = ⟨consN a b⟩‾`, y un numeral no nulo ES un `cons`: `m̄ = cons ⟨carN m⟩‾ ⟨cdrN m⟩‾`.
* **§2** Los accesores: `carc`, `cdrc` (no nulos), `lenc` (todos) y `nthc` (dentro de rango); fuera de esas
  condiciones los axiomas no fijan `carc`/`nthc` sobre `nil`.
* **§3** Los constructores de código de fórmula sobre numerales: `implc ā b̄ = ⟨implcN a b⟩‾`, y los otros seis.
* **§4** `In`, decidido en los dos sentidos: `memN y l → Prf (In ȳ l̄)` y `¬ memN y l → Prf ¬(In ȳ l̄)`.
* **§5** `concat` y `runFn` evaluados, y la pertenencia a las conclusiones de una cadena (`runFnN`), decidida.

**De dónde.** `prf_cons_evalM`, `prf_congr_carc` y la etiqueta de `⟨k, r⟩‾` (`prf_carc_consN`) vienen de
`sondeos/RosserBasura.lean` §3–§4, que ahora los usa desde aquí (ADR‑146 §4.6). Lo demás reutiliza los lemas de lista
del árbol (`prf_in_cons_iff`, `prf_not_in_nil`, `prf_lenc_cons`, `prf_nthc_succ`, `prf_runFn_cons`…) y `crit_num_ne`.

**Controles.** `prf_In_decide`: la capa decide `In` sobre numerales. Y el `#pureza` del final: lo de la etapa no nombra
la semántica, y `ev_numeralM` —el valor de un numeral en el modelo— sí.

⛔ Ningún numeral se evalúa: las listas se recorren por `encodeL`/`decodeL` con lemas ∀, y `codeNat` no aparece.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.ModeloCodigo

namespace ROBINSON_PlusPlus.Meta.RosserNumerales

/-! ## §1 · `cons` sobre numerales, y un numeral no nulo es un `cons` -/

/-- `cons ā b̄ = ⟨consN a b⟩‾`, con `numeralM` (de `sondeos/RosserBasura.lean`). -/
theorem prf_cons_evalM (a b : Nat) : Prf (cons (numeralM a) (numeralM b) =eq numeralM (consN a b)) := by
  have h1 := ROBINSON_PlusPlus.Meta.CodeNumeralPrf.prf_cons_eval a b
  rw [← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq, ← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq,
    ← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq] at h1
  exact h1

/-- El paso genérico: si los dos hijos son numerales, el `cons` también. -/
theorem prf_cons_evalM_of {A B : Term} {a b : Nat} (ha : Prf (A =eq numeralM a)) (hb : Prf (B =eq numeralM b)) :
    Prf (cons A B =eq numeralM (consN a b)) :=
  prf_eq_trans (prf_eq_trans (prf_congr_cons_head ha) (prf_congr_cons_tail hb)) (prf_cons_evalM a b)

/-- 🏁 **Un numeral no nulo es un `cons`**: `m̄ = cons ⟨carN m⟩‾ ⟨cdrN m⟩‾`. -/
theorem prf_numeral_cons {m : Nat} (h : m ≠ 0) :
    Prf (numeralM m =eq cons (numeralM (carN m)) (numeralM (cdrN m))) := by
  have e := prf_cons_evalM (carN m) (cdrN m)
  rw [consN_car_cdr h] at e
  exact prf_eq_symm e

/-! ## §2 · Los accesores sobre numerales -/

/-- La congruencia de `carc` en `Prf` (de `sondeos/RosserBasura.lean`). -/
theorem prf_congr_carc {x y : Term} (h : Prf (x =eq y)) : Prf (carc x =eq carc y) := by
  let f : Formula := Formula.eq (carc (liftTerm 0 x)) (carc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (carc x) (carc s) := by
    intro s; simp only [f, substFormula, carc, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS y) ▸ prf_leibniz_subst (A := f) h ((hS x) ▸ prf_refl (carc x))

/-- La congruencia de `cdrc` en `Prf`. -/
theorem prf_congr_cdrc {x y : Term} (h : Prf (x =eq y)) : Prf (cdrc x =eq cdrc y) := by
  let f : Formula := Formula.eq (cdrc (liftTerm 0 x)) (cdrc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (cdrc x) (cdrc s) := by
    intro s; simp only [f, substFormula, cdrc, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS y) ▸ prf_leibniz_subst (A := f) h ((hS x) ▸ prf_refl (cdrc x))

/-- La etiqueta de `⟨k, r⟩‾` (la forma de `sondeos/RosserBasura.lean`). -/
theorem prf_carc_consN (k r : Nat) : Prf (carc (numeralM (consN k r)) =eq numeralM k) :=
  prf_eq_trans (prf_congr_carc (prf_eq_symm (prf_cons_evalM k r))) (prf_carc_cons _ _)

/-- `carc m̄ = ⟨carN m⟩‾`, si `m ≠ 0`. -/
theorem prf_carc_numeral {m : Nat} (h : m ≠ 0) : Prf (carc (numeralM m) =eq numeralM (carN m)) :=
  prf_eq_trans (prf_congr_carc (prf_numeral_cons h)) (prf_carc_cons _ _)

/-- `cdrc m̄ = ⟨cdrN m⟩‾`, si `m ≠ 0`. -/
theorem prf_cdrc_numeral {m : Nat} (h : m ≠ 0) : Prf (cdrc (numeralM m) =eq numeralM (cdrN m)) :=
  prf_eq_trans (prf_congr_cdrc (prf_numeral_cons h)) (prf_cdrc_cons _ _)

/-- La longitud de un numeral de lista, por la lista. -/
theorem prf_lenc_encodeL : ∀ l : List Nat, Prf (lenc (numeralM (encodeL l)) =eq numeralM l.length)
  | [] => prf_lenc_nil
  | a :: l => prf_eq_trans (prf_congr_lenc (prf_eq_symm (prf_cons_evalM a (encodeL l))))
      (prf_eq_trans (prf_lenc_cons _ _) (prf_eq_congr_succ (prf_lenc_encodeL l)))

/-- 🏁 `lenc m̄ = ⟨lenN m⟩‾`, para todo `m`. -/
theorem prf_lenc_numeral (m : Nat) : Prf (lenc (numeralM m) =eq numeralM (lenN m)) := by
  have h := prf_lenc_encodeL (decodeL m)
  rw [encodeL_decodeL] at h
  exact h

theorem lenN_cdrN {m : Nat} (h : m ≠ 0) : lenN m = lenN (cdrN m) + 1 := by
  conv => lhs; rw [← consN_car_cdr h]
  rw [lenN_consN]

/-- 🏁 `nthc m̄ ī = ⟨nthN m i⟩‾` dentro de rango (fuera, los axiomas no fijan `nthc` sobre `nil`). -/
theorem prf_nthc_numeral : ∀ (i m : Nat), i < lenN m →
    Prf (nthc (numeralM m) (numeralM i) =eq numeralM (nthN m i))
  | 0, m, h => by
      have hm : m ≠ 0 := fun e => by rw [e, lenN_zero] at h; exact Nat.lt_irrefl 0 h
      exact prf_eq_trans (prf_congr_nthc_lst _ (prf_numeral_cons hm)) (prf_nthc_zero _ _)
  | i + 1, m, h => by
      have hm : m ≠ 0 := fun e => by rw [e, lenN_zero] at h; exact Nat.not_lt_zero _ h
      have hl : i < lenN (cdrN m) := by rw [lenN_cdrN hm] at h; omega
      exact prf_eq_trans (prf_congr_nthc_lst _ (prf_numeral_cons hm))
        (prf_eq_trans (prf_nthc_succ _ _ _) (prf_nthc_numeral i (cdrN m) hl))

/-! ## §3 · Los constructores de código de fórmula sobre numerales (espejo de `ModeloCodigo`) -/

theorem prf_botc_numeral : Prf (botc =eq numeralM botcN) :=
  prf_cons_evalM_of (prf_refl (numeralM 2)) (prf_refl (numeralM 0))

theorem prf_eqc_numeral (a b : Nat) : Prf (eqc (numeralM a) (numeralM b) =eq numeralM (eqcN a b)) :=
  prf_cons_evalM_of (prf_refl (numeralM 4)) (prf_cons_evalM_of (prf_refl (numeralM a))
    (prf_cons_evalM_of (prf_refl (numeralM b)) (prf_refl (numeralM 0))))

theorem prf_implc_numeral (a b : Nat) : Prf (implc (numeralM a) (numeralM b) =eq numeralM (implcN a b)) :=
  prf_cons_evalM_of (prf_refl (numeralM 5)) (prf_cons_evalM_of (prf_refl (numeralM a))
    (prf_cons_evalM_of (prf_refl (numeralM b)) (prf_refl (numeralM 0))))

theorem prf_forallc_numeral (a : Nat) : Prf (forallc (numeralM a) =eq numeralM (forallcN a)) :=
  prf_cons_evalM_of (prf_refl (numeralM 6)) (prf_cons_evalM_of (prf_refl (numeralM a)) (prf_refl (numeralM 0)))

theorem prf_andc_numeral (a b : Nat) : Prf (andc (numeralM a) (numeralM b) =eq numeralM (andcN a b)) :=
  prf_cons_evalM_of (prf_refl (numeralM 7)) (prf_cons_evalM_of (prf_refl (numeralM a))
    (prf_cons_evalM_of (prf_refl (numeralM b)) (prf_refl (numeralM 0))))

theorem prf_orc_numeral (a b : Nat) : Prf (orc (numeralM a) (numeralM b) =eq numeralM (orcN a b)) :=
  prf_cons_evalM_of (prf_refl (numeralM 8)) (prf_cons_evalM_of (prf_refl (numeralM a))
    (prf_cons_evalM_of (prf_refl (numeralM b)) (prf_refl (numeralM 0))))

theorem prf_exc_numeral (a : Nat) : Prf (exc (numeralM a) =eq numeralM (excN a)) :=
  prf_cons_evalM_of (prf_refl (numeralM 9)) (prf_cons_evalM_of (prf_refl (numeralM a)) (prf_refl (numeralM 0)))

/-! ## §4 · `In` sobre numerales, decidido en los dos sentidos -/

/-- Lo que está en la lista, `Prf` lo prueba. -/
theorem prf_In_encodeL (y : Nat) : ∀ l : List Nat, List.Mem y l →
    Prf (In (numeralM y) (numeralM (encodeL l)))
  | _ :: l, List.Mem.head _ =>
      prf_eq_subst_in (prf_cons_evalM y (encodeL l)) (prf_in_cons_head _ _)
  | a :: l, List.Mem.tail _ hm =>
      prf_eq_subst_in (prf_cons_evalM a (encodeL l))
        (prf_iff_mpr (prf_in_cons_iff _ _ _) (prf_or_intro_right (prf_In_encodeL y l hm)))

/-- Lo que NO está en la lista, `Prf` lo refuta, numeral a numeral (`crit_num_ne`). -/
theorem prf_not_In_encodeL (y : Nat) : ∀ l : List Nat, ¬ List.Mem y l →
    Prf (neg (In (numeralM y) (numeralM (encodeL l))))
  | [], _ => prf_not_in_nil _
  | a :: l, h => by
      have hya : y ≠ a := by rintro rfl; exact h (List.Mem.head l)
      have hl : ¬ List.Mem y l := fun hm => h (List.Mem.tail a hm)
      refine prf_deduction ?_
      have hin : PrfH [In (numeralM y) (numeralM (encodeL (a :: l)))]
          (In (numeralM y) (cons (numeralM a) (numeralM (encodeL l)))) :=
        PrfH_eq_subst_in (prf_to_prfH (prf_eq_symm (prf_cons_evalM a (encodeL l))) _) (prfH_hyp_self _)
      have hor := PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_in_cons_iff _ _ _)) _) hin
      exact PrfH.mp _ _ _ (prf_to_prfH (prf_or_elim_imp (crit_num_ne y a hya) (prf_not_In_encodeL y l hl)) _) hor

/-- 🏁 `memN y l → Prf (In ȳ l̄)`. -/
theorem prf_In_numeral {y l : Nat} (h : memN y l) : Prf (In (numeralM y) (numeralM l)) := by
  have e := prf_In_encodeL y (decodeL l) h
  rw [encodeL_decodeL] at e
  exact e

/-- 🏁 `¬ memN y l → Prf ¬(In ȳ l̄)`. -/
theorem prf_not_In_numeral {y l : Nat} (h : ¬ memN y l) : Prf (neg (In (numeralM y) (numeralM l))) := by
  have e := prf_not_In_encodeL y (decodeL l) h
  rw [encodeL_decodeL] at e
  exact e

/-! ## §5 · `concat` y `runFn` sobre numerales; la pertenencia a las conclusiones de una cadena -/

theorem prf_concat_encodeL : ∀ (la : List Nat) (b : Nat),
    Prf (concat (numeralM (encodeL la)) (numeralM b) =eq numeralM (encodeL (la ++ decodeL b)))
  | [], b => by
      rw [List.nil_append, encodeL_decodeL]
      exact prf_concat_nil_eq _
  | a :: la, b => prf_eq_trans (prf_congr_concat_first (prf_eq_symm (prf_cons_evalM a (encodeL la))))
      (prf_eq_trans (prf_concat_cons_eq _ _ _)
        (prf_cons_evalM_of (prf_refl (numeralM a)) (prf_concat_encodeL la b)))

/-- `concat ā b̄ = ⟨concatN a b⟩‾`. -/
theorem prf_concat_numeral (a b : Nat) : Prf (concat (numeralM a) (numeralM b) =eq numeralM (concatN a b)) := by
  have e := prf_concat_encodeL (decodeL a) b
  rw [encodeL_decodeL] at e
  exact e

/-- `runFn` sobre el numeral de una lista de líneas no nulas (sobre `0`, `carc` no está fijado). -/
theorem prf_runFn_encodeL : ∀ (l : List Nat), (∀ x, List.Mem x l → x ≠ 0) → ∀ c : Nat,
    Prf (runFn (numeralM c) (numeralM (encodeL l)) =eq numeralM (runFnL c l))
  | [], _, c => prf_runFn_nil _
  | x :: r, hl, c => by
      have hx : x ≠ 0 := hl x (List.Mem.head r)
      have hr : ∀ y, List.Mem y r → y ≠ 0 := fun y hy => hl y (List.Mem.tail x hy)
      have hacc : Prf (concat (numeralM c) (cons (carc (numeralM x)) nil) =eq
          numeralM (concatN c (consN (carN x) 0))) :=
        prf_eq_trans (prf_congr_concat_left (prf_cons_evalM_of (prf_carc_numeral hx) (prf_refl (numeralM 0))))
          (prf_concat_numeral c (consN (carN x) 0))
      exact prf_eq_trans (prf_congr_runFn_2 (prf_eq_symm (prf_cons_evalM x (encodeL r))))
        (prf_eq_trans (prf_runFn_cons _ _ _)
          (prf_eq_trans (prf_congr_runFn_1 hacc) (prf_runFn_encodeL r hr _)))

/-- 🏁 `runFn c̄ p̄ = ⟨runFnN c p⟩‾`, si ninguna línea de `p` es `0`. -/
theorem prf_runFn_numeral {c p : Nat} (hl : ∀ x, memN x p → x ≠ 0) :
    Prf (runFn (numeralM c) (numeralM p) =eq numeralM (runFnN c p)) := by
  have e := prf_runFn_encodeL (decodeL p) hl c
  rw [encodeL_decodeL] at e
  exact e

/-- Las conclusiones de una cadena, en ℕ: las cabezas de sus líneas. -/
theorem runFnL_eq : ∀ (l : List Nat) (c : Nat), runFnL c l = encodeL (decodeL c ++ l.map carN)
  | [], c => by rw [List.map_nil, List.append_nil, encodeL_decodeL, runFnL]
  | x :: r, c => by
      rw [runFnL, runFnL_eq r, concatN, decodeL_encodeL, decodeL_consN, decodeL_zero, List.map_cons,
        List.append_assoc, List.singleton_append]

theorem memN_runFnN_zero (y p : Nat) : memN y (runFnN 0 p) ↔ ∃ x, And (List.Mem x (decodeL p)) (carN x = y) := by
  unfold memN runFnN
  rw [runFnL_eq, decodeL_zero, List.nil_append, decodeL_encodeL]
  exact List.mem_map

/-- 🏁 **La pertenencia a las conclusiones, decidida**: si ninguna línea de `p` es `0`, `Prf` prueba lo que `runFnN`
    contiene y refuta lo que no. -/
theorem prf_In_runFn {y p : Nat} (hl : ∀ x, memN x p → x ≠ 0) (h : memN y (runFnN 0 p)) :
    Prf (In (numeralM y) (runFn nil (numeralM p))) :=
  prf_eq_subst_in (prf_eq_symm (prf_runFn_numeral (c := 0) hl)) (prf_In_numeral h)

theorem prf_not_In_runFn {y p : Nat} (hl : ∀ x, memN x p → x ≠ 0) (h : ¬ memN y (runFnN 0 p)) :
    Prf (neg (In (numeralM y) (runFn nil (numeralM p)))) := by
  refine prf_deduction ?_
  have hin := PrfH_eq_subst_in (prf_to_prfH (prf_runFn_numeral (c := 0) hl) _)
    (prfH_hyp_self (In (numeralM y) (runFn nil (numeralM p))))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_not_In_numeral h) _) hin

/-! ## §6 · Control: la capa DECIDE `In` sobre numerales -/

/-- La pertenencia en ℕ es decidible, sin lógica clásica. Sin esta instancia, `by_cases` sobre `memN` no encuentra una
    (`memN` no es reducible) y cae en `Classical.propDecidable`: así dependía `prf_In_decide` de `Classical.choice`,
    medido en ADR‑154 y arreglado en ADR‑155. -/
instance decMemN (y l : Nat) : Decidable (memN y l) := List.instDecidableMemOfLawfulBEq y (decodeL l)

/-- ✅ Para todo par de numerales, `Prf` prueba la pertenencia o la refuta (sin lógica clásica). -/
theorem prf_In_decide (y l : Nat) :
    Or (Prf (In (numeralM y) (numeralM l))) (Prf (neg (In (numeralM y) (numeralM l)))) := by
  by_cases h : memN y l
  · exact Or.inl (prf_In_numeral h)
  · exact Or.inr (prf_not_In_numeral h)

end ROBINSON_PlusPlus.Meta.RosserNumerales

#print axioms ROBINSON_PlusPlus.Meta.RosserNumerales.prf_numeral_cons
#print axioms ROBINSON_PlusPlus.Meta.RosserNumerales.prf_lenc_numeral
#print axioms ROBINSON_PlusPlus.Meta.RosserNumerales.prf_nthc_numeral
#print axioms ROBINSON_PlusPlus.Meta.RosserNumerales.prf_not_In_numeral
#print axioms ROBINSON_PlusPlus.Meta.RosserNumerales.prf_runFn_numeral
#print axioms ROBINSON_PlusPlus.Meta.RosserNumerales.prf_not_In_runFn
#print axioms ROBINSON_PlusPlus.Meta.RosserNumerales.prf_In_decide

/-! T08 en el módulo (ADR‑147, con el recorrido de ADR‑149): lo de esta etapa no nombra la semántica; `ev_numeralM`, el
    valor de un numeral en el modelo, sí. -/
#pureza ROBINSON_PlusPlus.Meta.RosserNumerales.prf_numeral_cons ROBINSON_PlusPlus.Meta.RosserNumerales.prf_carc_numeral
  ROBINSON_PlusPlus.Meta.RosserNumerales.prf_cdrc_numeral ROBINSON_PlusPlus.Meta.RosserNumerales.prf_lenc_numeral
  ROBINSON_PlusPlus.Meta.RosserNumerales.prf_nthc_numeral ROBINSON_PlusPlus.Meta.RosserNumerales.prf_implc_numeral
  ROBINSON_PlusPlus.Meta.RosserNumerales.prf_In_numeral ROBINSON_PlusPlus.Meta.RosserNumerales.prf_not_In_numeral
  ROBINSON_PlusPlus.Meta.RosserNumerales.prf_concat_numeral ROBINSON_PlusPlus.Meta.RosserNumerales.prf_runFn_numeral
  ROBINSON_PlusPlus.Meta.RosserNumerales.prf_In_runFn ROBINSON_PlusPlus.Meta.RosserNumerales.prf_not_In_runFn
  ROBINSON_PlusPlus.Meta.RosserNumerales.prf_In_decide
  | ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM
