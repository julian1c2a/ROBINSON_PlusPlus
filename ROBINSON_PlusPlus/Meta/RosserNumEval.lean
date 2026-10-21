/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.RosserNumerales
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
import ROBINSON_PlusPlus.Meta.BoundedInPrf
import ROBINSON_PlusPlus.Meta.LineWFTrackedPrf

/-!
# `Meta/RosserNumEval.lean` — Rosser, etapa 2: la sustitución sobre numerales (ADR‑146 §3, ADR‑147, ADR‑152)

**Qué.** Encima de la capa de listas (`Meta/RosserNumerales.lean`), `Prf` evalúa sobre numerales los símbolos de la
sustitución —`substtc`/`substtsc`, `liftc`/`liftsc`, `substfc` y `liftfc`— como lo hacen sus espejos de ℕ
(`substtcN`…`liftfcN`, en `ModeloCodigo`), cuando las guardas son verdaderas:

* **§1** Los códigos BUENOS en ℕ: `CodT`/`CodTs` (término y lista de términos, mutuos) y `CodF` (fórmula), los árboles
  que forman los constructores de código. Sobre lo demás, la «basura», los axiomas no fijan la sustitución:
  `ax_substfc_impl` y los suyos no llevan guarda.
* **§2** La clausura en ℕ: `liftcN`, `substtcN`, `liftfcN` y `substfcN` llevan códigos buenos a códigos buenos.
* **§3** Las guardas dan árboles: `hasWitN c → CodT c` y `hasWitFN c → CodF c`, por inducción fuerte en el número (el
  testigo es una lista cerrada por los constructores, y un hijo es menor que su padre).
* **§4** Los constructores de término sobre numerales: `varc n̄ = ⟨0, n⟩‾`, `funcc` y `atomc`.
* **§5** Términos: `substtc k̄ s̄ c̄ = ⟨substtcN k s c⟩‾` y `liftc c̄ t̄ = ⟨liftcN c t⟩‾`, y sus listas, por recursión mutua
  sobre `CodT`/`CodTs`; la variable, por tricotomía con `prf_lt_numeralM`.
* **§6** Fórmulas: `liftfc` y `substfc`, por inducción sobre `CodF`. En `∀`/`∃` el sustituyendo baja con `liftc 0`, que
  §5 evalúa y §2 mantiene bueno.
* **§7** Con las guardas: `prf_substfc_guarda` y las otras tres, la forma que consumirá NegLineWF.

**De dónde.** Es el análogo de `ArithPrf.lean:181-473` (`prf_substTerm_arith`…`prf_liftFormula_arith`), que evalúa sólo
códigos CANÓNICOS (`termCode t`, `formCode φ`), sobre códigos de ℕ, donde el código de un símbolo puede ser cualquier
número. Las ecuaciones son las de `ArithPrf` (`prf_substtc_var_gt`, `prf_substfc_forall`…); las congruencias, las de
`NumCodeClosedPrf` (`prf_congr_liftc`, `prf_congr_substtc3`, `prf_congr_funcc2`, y las dos de listas que bajan allí con
esta etapa: `prf_congr_liftsc` y `prf_congr_substtsc3`).

**Controles.** `codF_codeNat`: el código de toda fórmula es bueno, y `prf_substfc_codeNat` aplica la evaluación a
todos. `not_hasWitFN_zero`: la hipótesis puede fallar. `guardas_satisfacibles`: las dos guardas de
`prf_substfc_guarda` valen a la vez. Y el `#pureza` del final.

⛔ Ningún numeral se evalúa: los códigos se recorren con las ecuaciones ∀ de `ModeloCodigo` (`substtcN_var`,
`substfcN_forall`…) y `rw`, y `simp` no toca un código.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.RosserNumerales

namespace ROBINSON_PlusPlus.Meta.RosserNumEval

/-! ## §1 · Los códigos buenos en ℕ -/

mutual
/-- Un código de TÉRMINO: `⟨0, n⟩` (la variable `n`) o `⟨1, s, ts⟩`, con `ts` una lista de códigos de término. El código
    del símbolo, `s`, es cualquier número. -/
inductive CodT : Nat → Prop
  | var (n : Nat) : CodT (consN 0 (consN n 0))
  | func (s ts : Nat) : CodTs ts → CodT (consN 1 (consN s (consN ts 0)))
/-- Una lista de códigos de término. -/
inductive CodTs : Nat → Prop
  | nil : CodTs 0
  | cons (a r : Nat) : CodT a → CodTs r → CodTs (consN a r)
end

/-- Un código de FÓRMULA, con las etiquetas de `codeNat` (2…9). -/
inductive CodF : Nat → Prop
  | bot : CodF (consN 2 0)
  | atom (p ts : Nat) : CodTs ts → CodF (consN 3 (consN p (consN ts 0)))
  | eq (a b : Nat) : CodT a → CodT b → CodF (consN 4 (consN a (consN b 0)))
  | impl (a b : Nat) : CodF a → CodF b → CodF (consN 5 (consN a (consN b 0)))
  | all (a : Nat) : CodF a → CodF (consN 6 (consN a 0))
  | and (a b : Nat) : CodF a → CodF b → CodF (consN 7 (consN a (consN b 0)))
  | or (a b : Nat) : CodF a → CodF b → CodF (consN 8 (consN a (consN b 0)))
  | ex (a : Nat) : CodF a → CodF (consN 9 (consN a 0))

/-! ## §2 · La clausura en ℕ: la sustitución y el lift llevan códigos buenos a códigos buenos -/

mutual
theorem codT_liftcN {t : Nat} (h : CodT t) (c : Nat) : CodT (liftcN c t) :=
  match h with
  | .var n => by
      rw [liftcN_var]
      by_cases hn : n < c
      · rw [ite_eq_left hn]; exact .var n
      · rw [ite_eq_right hn]; exact .var (n + 1)
  | .func s ts hts => by
      rw [liftcN_func]; exact .func s _ (codTs_liftscN hts c)
theorem codTs_liftscN {ts : Nat} (h : CodTs ts) (c : Nat) : CodTs (liftscN c ts) :=
  match h with
  | .nil => by rw [liftscN_zero]; exact .nil
  | .cons a r ha hr => by
      rw [liftscN_consN]; exact .cons _ _ (codT_liftcN ha c) (codTs_liftscN hr c)
end

mutual
theorem codT_substtcN {c : Nat} (h : CodT c) {s : Nat} (hs : CodT s) (k : Nat) : CodT (substtcN k s c) :=
  match h with
  | .var n => by
      rw [substtcN_var]
      by_cases e : k = n
      · rw [ite_eq_left e]; exact hs
      · rw [ite_eq_right e]
        by_cases hl : k < n
        · rw [ite_eq_left hl]; exact .var (n - 1)
        · rw [ite_eq_right hl]; exact .var n
  | .func sy ts hts => by
      rw [substtcN_func]; exact .func sy _ (codTs_substtscN hts hs k)
theorem codTs_substtscN {ts : Nat} (h : CodTs ts) {s : Nat} (hs : CodT s) (k : Nat) :
    CodTs (substtscN k s ts) :=
  match h with
  | .nil => by rw [substtscN_zero]; exact .nil
  | .cons a r ha hr => by
      rw [substtscN_consN]; exact .cons _ _ (codT_substtcN ha hs k) (codTs_substtscN hr hs k)
end

theorem codF_liftfcN {f : Nat} (hf : CodF f) : ∀ c : Nat, CodF (liftfcN c f) := by
  induction hf with
  | bot => intro c; rw [liftfcN_bot]; exact .bot
  | atom p ts hts => intro c; rw [liftfcN_atom]; exact .atom p _ (codTs_liftscN hts c)
  | eq a b ha hb => intro c; rw [liftfcN_eq]; exact .eq _ _ (codT_liftcN ha c) (codT_liftcN hb c)
  | impl a b _ _ iha ihb => intro c; rw [liftfcN_impl]; exact .impl _ _ (iha c) (ihb c)
  | all a _ iha => intro c; rw [liftfcN_forall]; exact .all _ (iha (c + 1))
  | and a b _ _ iha ihb => intro c; rw [liftfcN_and]; exact .and _ _ (iha c) (ihb c)
  | or a b _ _ iha ihb => intro c; rw [liftfcN_or]; exact .or _ _ (iha c) (ihb c)
  | ex a _ iha => intro c; rw [liftfcN_ex]; exact .ex _ (iha (c + 1))

theorem codF_substfcN {f : Nat} (hf : CodF f) : ∀ (v t : Nat), CodT t → CodF (substfcN v t f) := by
  induction hf with
  | bot => intro v t _; rw [substfcN_bot]; exact .bot
  | atom p ts hts => intro v t ht; rw [substfcN_atom]; exact .atom p _ (codTs_substtscN hts ht v)
  | eq a b ha hb =>
      intro v t ht; rw [substfcN_eq]; exact .eq _ _ (codT_substtcN ha ht v) (codT_substtcN hb ht v)
  | impl a b _ _ iha ihb => intro v t ht; rw [substfcN_impl]; exact .impl _ _ (iha v t ht) (ihb v t ht)
  | all a _ iha => intro v t ht; rw [substfcN_forall]; exact .all _ (iha (v + 1) _ (codT_liftcN ht 0))
  | and a b _ _ iha ihb => intro v t ht; rw [substfcN_and]; exact .and _ _ (iha v t ht) (ihb v t ht)
  | or a b _ _ iha ihb => intro v t ht; rw [substfcN_or]; exact .or _ _ (iha v t ht) (ihb v t ht)
  | ex a _ iha => intro v t ht; rw [substfcN_ex]; exact .ex _ (iha (v + 1) _ (codT_liftcN ht 0))

/-! ## §3 · Las guardas dan árboles: `hasWitN c → CodT c`, `hasWitFN c → CodF c` -/

theorem memN_nthN_encodeL (x : Nat) :
    ∀ L : List Nat, List.Mem x L → ∃ i, And (i < L.length) (nthN (encodeL L) i = x)
  | _ :: _, List.Mem.head _ => ⟨0, Nat.succ_pos _, nthN_cz _ _⟩
  | a :: L, List.Mem.tail _ hm => by
      obtain ⟨i, hi, he⟩ := memN_nthN_encodeL x L hm
      exact ⟨i + 1, Nat.succ_lt_succ hi, by rw [encodeL, nthN_cs]; exact he⟩

/-- Lo que está en una lista está en alguna posición. -/
theorem memN_nthN {x l : Nat} (h : memN x l) : ∃ i, And (i < lenN l) (nthN l i = x) := by
  have e := memN_nthN_encodeL x (decodeL l) h
  rw [encodeL_decodeL] at e
  exact e

/-- Lo que está en una lista es menor que ella. -/
theorem memN_lt {x l : Nat} (h : memN x l) : x < l := by
  obtain ⟨i, _, he⟩ := memN_nthN h
  have hl : ¬ l = 0 := by rintro rfl; exact memN_zero x h
  rw [← he]; exact nthN_lt i hl

theorem argsInN_mem {w Y x : Nat} (h : argsInN w Y) (hx : memN x Y) : memN x w := by
  obtain ⟨i, hi, he⟩ := memN_nthN hx
  rw [← he]; exact h i hi

theorem codTs_encodeL : ∀ L : List Nat, (∀ x, List.Mem x L → CodT x) → CodTs (encodeL L)
  | [], _ => .nil
  | a :: L, h => .cons _ _ (h a (List.Mem.head L)) (codTs_encodeL L (fun x hx => h x (List.Mem.tail a hx)))

theorem codTs_of_mem {ts : Nat} (h : ∀ x, memN x ts → CodT x) : CodTs ts := by
  have e := codTs_encodeL (decodeL ts) h
  rw [encodeL_decodeL] at e
  exact e

/-- 🏁 Lo que está en una lista testigo de términos (`wfAll1N`) es un código de término. -/
theorem codT_of_wit {w : Nat} (hw : wfAll1N w) : ∀ c : Nat, memN c w → CodT c := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro hc
    obtain ⟨i, hi, hie⟩ := memN_nthN hc
    have hE : isTermCodeE1N w c := hie ▸ hw i hi
    rcases hE with hu | ⟨hb, hargs⟩
    · have e : c = consN 0 (consN (nthN c 1) 0) := hu
      rw [e]; exact .var _
    · have e : c = consN 1 (consN (nthN c 1) (consN (nthN c 2) 0)) := hb
      have hc0 : ¬ c = 0 := by rw [e]; exact CodeNatInjPrf.consN_ne_zero _ _
      have hts : CodTs (nthN c 2) := codTs_of_mem fun x hx =>
        ih x (Nat.lt_trans (memN_lt hx) (nthN_lt 2 hc0)) (argsInN_mem hargs hx)
      rw [e]; exact .func _ _ hts

/-- 🏁 Lo que está en una lista testigo de fórmulas (`wfAllFN`, sobre una de términos) es un código de fórmula. -/
theorem codF_of_wit {wF wT : Nat} (hT : wfAll1N wT) (hF : wfAllFN wF wT) : ∀ c : Nat, memN c wF → CodF c := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro hc
    obtain ⟨i, hi, hie⟩ := memN_nthN hc
    have hE : isFormCodeE2N wF wT c := hie ▸ hF i hi
    rcases hE with hbot | ⟨hs, hargs⟩ | ⟨hs, h1, h2⟩ | ⟨hs, h1, h2⟩ | ⟨hs, h1⟩ | ⟨hs, h1, h2⟩ | ⟨hs, h1, h2⟩ |
      ⟨hs, h1⟩
    · have e : c = consN 2 0 := hbot
      rw [e]; exact .bot
    · have e : c = consN 3 (consN (nthN c 1) (consN (nthN c 2) 0)) := hs
      rw [e]; exact .atom _ _ (codTs_of_mem fun x hx => codT_of_wit hT x (argsInN_mem hargs hx))
    · have e : c = consN 4 (consN (nthN c 1) (consN (nthN c 2) 0)) := hs
      rw [e]; exact .eq _ _ (codT_of_wit hT _ h1) (codT_of_wit hT _ h2)
    · have e : c = consN 5 (consN (nthN c 1) (consN (nthN c 2) 0)) := hs
      have hc0 : ¬ c = 0 := by rw [e]; exact CodeNatInjPrf.consN_ne_zero _ _
      rw [e]; exact .impl _ _ (ih _ (nthN_lt 1 hc0) h1) (ih _ (nthN_lt 2 hc0) h2)
    · have e : c = consN 6 (consN (nthN c 1) 0) := hs
      have hc0 : ¬ c = 0 := by rw [e]; exact CodeNatInjPrf.consN_ne_zero _ _
      rw [e]; exact .all _ (ih _ (nthN_lt 1 hc0) h1)
    · have e : c = consN 7 (consN (nthN c 1) (consN (nthN c 2) 0)) := hs
      have hc0 : ¬ c = 0 := by rw [e]; exact CodeNatInjPrf.consN_ne_zero _ _
      rw [e]; exact .and _ _ (ih _ (nthN_lt 1 hc0) h1) (ih _ (nthN_lt 2 hc0) h2)
    · have e : c = consN 8 (consN (nthN c 1) (consN (nthN c 2) 0)) := hs
      have hc0 : ¬ c = 0 := by rw [e]; exact CodeNatInjPrf.consN_ne_zero _ _
      rw [e]; exact .or _ _ (ih _ (nthN_lt 1 hc0) h1) (ih _ (nthN_lt 2 hc0) h2)
    · have e : c = consN 9 (consN (nthN c 1) 0) := hs
      have hc0 : ¬ c = 0 := by rw [e]; exact CodeNatInjPrf.consN_ne_zero _ _
      rw [e]; exact .ex _ (ih _ (nthN_lt 1 hc0) h1)

/-- 🏁 La guarda de término da un árbol. -/
theorem codT_of_hasWitN {c : Nat} (h : hasWitN c) : CodT c := by
  obtain ⟨_, hw, hc⟩ := h
  exact codT_of_wit hw _ hc

/-- 🏁 La guarda de fórmula da un árbol. -/
theorem codF_of_hasWitFN {c : Nat} (h : hasWitFN c) : CodF c := by
  obtain ⟨_, _, ⟨hT, hF⟩, hc⟩ := h
  exact codF_of_wit hT hF _ hc

/-! ## §4 · Los constructores de término sobre numerales -/

theorem prf_varc_numeral (n : Nat) : Prf (varc (numeralM n) =eq numeralM (consN 0 (consN n 0))) :=
  prf_cons_evalM_of (prf_refl (numeralM 0)) (prf_cons_evalM_of (prf_refl (numeralM n)) (prf_refl (numeralM 0)))

theorem prf_funcc_numeral (s ts : Nat) :
    Prf (funcc (numeralM s) (numeralM ts) =eq numeralM (consN 1 (consN s (consN ts 0)))) :=
  prf_cons_evalM_of (prf_refl (numeralM 1)) (prf_cons_evalM_of (prf_refl (numeralM s))
    (prf_cons_evalM_of (prf_refl (numeralM ts)) (prf_refl (numeralM 0))))

theorem prf_atomc_numeral (p ts : Nat) :
    Prf (atomc (numeralM p) (numeralM ts) =eq numeralM (consN 3 (consN p (consN ts 0)))) :=
  prf_cons_evalM_of (prf_refl (numeralM 3)) (prf_cons_evalM_of (prf_refl (numeralM p))
    (prf_cons_evalM_of (prf_refl (numeralM ts)) (prf_refl (numeralM 0))))

/-! ## §5 · La sustitución y el lift de TÉRMINOS sobre numerales -/

/-- La variable, por tricotomía: `k = n` da el sustituyendo, `k < n` baja el índice, `n < k` lo deja. -/
theorem prf_substtc_var (k s n : Nat) :
    Prf (substtc (numeralM k) (numeralM s) (numeralM (consN 0 (consN n 0))) =eq
      numeralM (substtcN k s (consN 0 (consN n 0)))) := by
  refine prf_eq_trans (NumCodeClosedPrf.prf_congr_substtc3 (prf_eq_symm (prf_varc_numeral n))) ?_
  rw [substtcN_var]
  rcases Nat.lt_trichotomy k n with hlt | rfl | hgt
  · rw [ite_eq_right (Nat.ne_of_lt hlt), ite_eq_left hlt]
    cases n with
    | zero => exact absurd hlt (Nat.not_lt_zero k)
    | succ m =>
      rw [Nat.add_sub_cancel]
      exact prf_eq_trans (prf_mp (prf_substtc_var_gt _ _ _) (LineWFTrackedPrf.prf_lt_numeralM hlt))
        (prf_eq_trans (prf_congr_un (BoundedInPrf.prf_pred_succ (numeralM m))) (prf_varc_numeral m))
  · rw [ite_eq_left rfl]
    exact prf_mp (prf_substtc_var_eq _ _ _) (prf_refl _)
  · rw [ite_eq_right (Nat.ne_of_lt hgt).symm, ite_eq_right (Nat.lt_asymm hgt)]
    exact prf_eq_trans (prf_mp (prf_substtc_var_lt _ _ _) (LineWFTrackedPrf.prf_lt_numeralM hgt))
      (prf_varc_numeral n)

mutual
/-- 🏁 `substtc k̄ s̄ c̄ = ⟨substtcN k s c⟩‾` sobre un código de término (el sustituyendo, cualquiera). -/
theorem prf_substtc_numeral {c : Nat} (h : CodT c) (k s : Nat) :
    Prf (substtc (numeralM k) (numeralM s) (numeralM c) =eq numeralM (substtcN k s c)) :=
  match h with
  | .var n => prf_substtc_var k s n
  | .func sy ts hts => by
      rw [substtcN_func]
      exact prf_eq_trans (NumCodeClosedPrf.prf_congr_substtc3 (prf_eq_symm (prf_funcc_numeral sy ts)))
        (prf_eq_trans (prf_substtc_func _ _ _ _)
          (prf_eq_trans (NumCodeClosedPrf.prf_congr_funcc2 (prf_substtsc_numeral hts k s)) (prf_funcc_numeral sy _)))
theorem prf_substtsc_numeral {ts : Nat} (h : CodTs ts) (k s : Nat) :
    Prf (substtsc (numeralM k) (numeralM s) (numeralM ts) =eq numeralM (substtscN k s ts)) :=
  match h with
  | .nil => by rw [substtscN_zero]; exact prf_substtsc_nil _ _
  | .cons a r ha hr => by
      rw [substtscN_consN]
      exact prf_eq_trans (NumCodeClosedPrf.prf_congr_substtsc3 (prf_eq_symm (prf_cons_evalM a r)))
        (prf_eq_trans (prf_substtsc_cons _ _ _ _)
          (prf_cons_evalM_of (prf_substtc_numeral ha k s) (prf_substtsc_numeral hr k s)))
end

/-- La variable: `n < c` la deja, `c ≤ n` la sube. -/
theorem prf_liftc_var (c n : Nat) :
    Prf (liftc (numeralM c) (numeralM (consN 0 (consN n 0))) =eq numeralM (liftcN c (consN 0 (consN n 0)))) := by
  refine prf_eq_trans (NumCodeClosedPrf.prf_congr_liftc (prf_eq_symm (prf_varc_numeral n))) ?_
  rw [liftcN_var]
  by_cases h : n < c
  · rw [ite_eq_left h]
    exact prf_eq_trans (prf_mp (prf_liftc_var_lt _ _) (LineWFTrackedPrf.prf_lt_numeralM h)) (prf_varc_numeral n)
  · rw [ite_eq_right h]
    exact prf_eq_trans
      (prf_mp (prf_liftc_var_ge _ _) (LineWFTrackedPrf.prf_lt_numeralM (Nat.lt_succ_of_le (Nat.not_lt.mp h))))
      (prf_varc_numeral (n + 1))

mutual
/-- 🏁 `liftc c̄ t̄ = ⟨liftcN c t⟩‾` sobre un código de término. -/
theorem prf_liftc_numeral {t : Nat} (h : CodT t) (c : Nat) :
    Prf (liftc (numeralM c) (numeralM t) =eq numeralM (liftcN c t)) :=
  match h with
  | .var n => prf_liftc_var c n
  | .func sy ts hts => by
      rw [liftcN_func]
      exact prf_eq_trans (NumCodeClosedPrf.prf_congr_liftc (prf_eq_symm (prf_funcc_numeral sy ts)))
        (prf_eq_trans (prf_liftc_func _ _ _)
          (prf_eq_trans (NumCodeClosedPrf.prf_congr_funcc2 (prf_liftsc_numeral hts c)) (prf_funcc_numeral sy _)))
theorem prf_liftsc_numeral {ts : Nat} (h : CodTs ts) (c : Nat) :
    Prf (liftsc (numeralM c) (numeralM ts) =eq numeralM (liftscN c ts)) :=
  match h with
  | .nil => by rw [liftscN_zero]; exact prf_liftsc_nil _
  | .cons a r ha hr => by
      rw [liftscN_consN]
      exact prf_eq_trans (NumCodeClosedPrf.prf_congr_liftsc (prf_eq_symm (prf_cons_evalM a r)))
        (prf_eq_trans (prf_liftsc_cons _ _ _) (prf_cons_evalM_of (prf_liftc_numeral ha c) (prf_liftsc_numeral hr c)))
end

/-! ## §6 · La sustitución y el lift de FÓRMULAS sobre numerales -/

/-- 🏁 `liftfc c̄ f̄ = ⟨liftfcN c f⟩‾` sobre un código de fórmula. -/
theorem prf_liftfc_numeral {f : Nat} (hf : CodF f) : ∀ c : Nat,
    Prf (liftfc (numeralM c) (numeralM f) =eq numeralM (liftfcN c f)) := by
  induction hf with
  | bot =>
      intro c; rw [liftfcN_bot]
      exact prf_eq_trans (prf_congr_liftfc_arg2 (prf_eq_symm prf_botc_numeral))
        (prf_eq_trans (prf_liftfc_bottom _) prf_botc_numeral)
  | atom p ts hts =>
      intro c; rw [liftfcN_atom]
      exact prf_eq_trans (prf_congr_liftfc_arg2 (prf_eq_symm (prf_atomc_numeral p ts)))
        (prf_eq_trans (prf_liftfc_atom _ _ _)
          (prf_eq_trans (prf_congr_bin2 (prf_liftsc_numeral hts c)) (prf_atomc_numeral p _)))
  | eq a b ha hb =>
      intro c; rw [liftfcN_eq]
      exact prf_eq_trans (prf_congr_liftfc_arg2 (prf_eq_symm (prf_eqc_numeral a b)))
        (prf_eq_trans (prf_liftfc_eq _ _ _)
          (prf_eq_trans (prf_congr_bin1 (prf_liftc_numeral ha c))
            (prf_eq_trans (prf_congr_bin2 (prf_liftc_numeral hb c)) (prf_eqc_numeral _ _))))
  | impl a b _ _ iha ihb =>
      intro c; rw [liftfcN_impl]
      exact prf_eq_trans (prf_congr_liftfc_arg2 (prf_eq_symm (prf_implc_numeral a b)))
        (prf_eq_trans (prf_liftfc_impl _ _ _)
          (prf_eq_trans (prf_congr_bin1 (iha c)) (prf_eq_trans (prf_congr_bin2 (ihb c)) (prf_implc_numeral _ _))))
  | all a _ iha =>
      intro c; rw [liftfcN_forall]
      exact prf_eq_trans (prf_congr_liftfc_arg2 (prf_eq_symm (prf_forallc_numeral a)))
        (prf_eq_trans (prf_liftfc_forall _ _) (prf_eq_trans (prf_congr_un (iha (c + 1))) (prf_forallc_numeral _)))
  | and a b _ _ iha ihb =>
      intro c; rw [liftfcN_and]
      exact prf_eq_trans (prf_congr_liftfc_arg2 (prf_eq_symm (prf_andc_numeral a b)))
        (prf_eq_trans (prf_liftfc_and _ _ _)
          (prf_eq_trans (prf_congr_bin1 (iha c)) (prf_eq_trans (prf_congr_bin2 (ihb c)) (prf_andc_numeral _ _))))
  | or a b _ _ iha ihb =>
      intro c; rw [liftfcN_or]
      exact prf_eq_trans (prf_congr_liftfc_arg2 (prf_eq_symm (prf_orc_numeral a b)))
        (prf_eq_trans (prf_liftfc_or _ _ _)
          (prf_eq_trans (prf_congr_bin1 (iha c)) (prf_eq_trans (prf_congr_bin2 (ihb c)) (prf_orc_numeral _ _))))
  | ex a _ iha =>
      intro c; rw [liftfcN_ex]
      exact prf_eq_trans (prf_congr_liftfc_arg2 (prf_eq_symm (prf_exc_numeral a)))
        (prf_eq_trans (prf_liftfc_ex _ _) (prf_eq_trans (prf_congr_un (iha (c + 1))) (prf_exc_numeral _)))

/-- 🏁 `substfc v̄ t̄ f̄ = ⟨substfcN v t f⟩‾` sobre un código de fórmula, con un código de término `t`: bajo un
    cuantificador el sustituyendo pasa a `liftc 0 t̄`, que sólo está fijado sobre códigos. -/
theorem prf_substfc_numeral {f : Nat} (hf : CodF f) : ∀ (v t : Nat), CodT t →
    Prf (substfc (numeralM v) (numeralM t) (numeralM f) =eq numeralM (substfcN v t f)) := by
  induction hf with
  | bot =>
      intro v t _; rw [substfcN_bot]
      exact prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_symm prf_botc_numeral))
        (prf_eq_trans (prf_substfc_bottom _ _) prf_botc_numeral)
  | atom p ts hts =>
      intro v t _; rw [substfcN_atom]
      exact prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_symm (prf_atomc_numeral p ts)))
        (prf_eq_trans (prf_substfc_atom _ _ _ _)
          (prf_eq_trans (prf_congr_bin2 (prf_substtsc_numeral hts v t)) (prf_atomc_numeral p _)))
  | eq a b ha hb =>
      intro v t _; rw [substfcN_eq]
      exact prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_symm (prf_eqc_numeral a b)))
        (prf_eq_trans (prf_substfc_eq _ _ _ _)
          (prf_eq_trans (prf_congr_bin1 (prf_substtc_numeral ha v t))
            (prf_eq_trans (prf_congr_bin2 (prf_substtc_numeral hb v t)) (prf_eqc_numeral _ _))))
  | impl a b _ _ iha ihb =>
      intro v t ht; rw [substfcN_impl]
      exact prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_symm (prf_implc_numeral a b)))
        (prf_eq_trans (prf_substfc_impl _ _ _ _)
          (prf_eq_trans (prf_congr_bin1 (iha v t ht))
            (prf_eq_trans (prf_congr_bin2 (ihb v t ht)) (prf_implc_numeral _ _))))
  | all a _ iha =>
      intro v t ht; rw [substfcN_forall]
      exact prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_symm (prf_forallc_numeral a)))
        (prf_eq_trans (prf_substfc_forall _ _ _)
          (prf_eq_trans (prf_congr_un (prf_eq_trans
              (prf_congr_substfc_arg2 (x := succ (numeralM v)) (z := numeralM a) (prf_liftc_numeral ht 0))
              (iha (v + 1) _ (codT_liftcN ht 0))))
            (prf_forallc_numeral _)))
  | and a b _ _ iha ihb =>
      intro v t ht; rw [substfcN_and]
      exact prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_symm (prf_andc_numeral a b)))
        (prf_eq_trans (prf_substfc_and _ _ _ _)
          (prf_eq_trans (prf_congr_bin1 (iha v t ht))
            (prf_eq_trans (prf_congr_bin2 (ihb v t ht)) (prf_andc_numeral _ _))))
  | or a b _ _ iha ihb =>
      intro v t ht; rw [substfcN_or]
      exact prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_symm (prf_orc_numeral a b)))
        (prf_eq_trans (prf_substfc_or _ _ _ _)
          (prf_eq_trans (prf_congr_bin1 (iha v t ht))
            (prf_eq_trans (prf_congr_bin2 (ihb v t ht)) (prf_orc_numeral _ _))))
  | ex a _ iha =>
      intro v t ht; rw [substfcN_ex]
      exact prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_symm (prf_exc_numeral a)))
        (prf_eq_trans (prf_substfc_ex _ _ _)
          (prf_eq_trans (prf_congr_un (prf_eq_trans
              (prf_congr_substfc_arg2 (x := succ (numeralM v)) (z := numeralM a) (prf_liftc_numeral ht 0))
              (iha (v + 1) _ (codT_liftcN ht 0))))
            (prf_exc_numeral _)))

/-! ## §7 · Con las guardas: la forma que consumirá NegLineWF -/

theorem prf_substtc_guarda {c : Nat} (hc : hasWitN c) (k s : Nat) :
    Prf (substtc (numeralM k) (numeralM s) (numeralM c) =eq numeralM (substtcN k s c)) :=
  prf_substtc_numeral (codT_of_hasWitN hc) k s

theorem prf_liftc_guarda {t : Nat} (ht : hasWitN t) (c : Nat) :
    Prf (liftc (numeralM c) (numeralM t) =eq numeralM (liftcN c t)) :=
  prf_liftc_numeral (codT_of_hasWitN ht) c

/-- 🏁 **La sustitución sobre numerales, con las guardas de las líneas** (`hasWitFN`, `hasWitN`, las de `lineWFT`). -/
theorem prf_substfc_guarda {f t : Nat} (hf : hasWitFN f) (ht : hasWitN t) (v : Nat) :
    Prf (substfc (numeralM v) (numeralM t) (numeralM f) =eq numeralM (substfcN v t f)) :=
  prf_substfc_numeral (codF_of_hasWitFN hf) v t (codT_of_hasWitN ht)

/-- 🏁 El lift sobre numerales, con la guarda de fórmula. -/
theorem prf_liftfc_guarda {f : Nat} (hf : hasWitFN f) (c : Nat) :
    Prf (liftfc (numeralM c) (numeralM f) =eq numeralM (liftfcN c f)) :=
  prf_liftfc_numeral (codF_of_hasWitFN hf) c

/-! ## §8 · Controles -/

mutual
theorem codT_codeNatTerm (t : Term) : CodT (codeNatTerm t) :=
  match t with
  | .var n => .var n
  | .func _ ts => .func _ _ (codTs_codeNatTerms ts)
theorem codTs_codeNatTerms (ts : List Term) : CodTs (codeNatTerms ts) :=
  match ts with
  | [] => .nil
  | t :: ts' => .cons _ _ (codT_codeNatTerm t) (codTs_codeNatTerms ts')
end

/-- ✅ El código de toda fórmula es bueno. -/
theorem codF_codeNat : ∀ φ : Formula, CodF (codeNat φ)
  | .bottom => .bot
  | .atom _ ts => .atom _ _ (codTs_codeNatTerms ts)
  | .eq t u => .eq _ _ (codT_codeNatTerm t) (codT_codeNatTerm u)
  | .impl a b => .impl _ _ (codF_codeNat a) (codF_codeNat b)
  | Formula.forall a => .all _ (codF_codeNat a)
  | .and a b => .and _ _ (codF_codeNat a) (codF_codeNat b)
  | .or a b => .or _ _ (codF_codeNat a) (codF_codeNat b)
  | .ex a => .ex _ (codF_codeNat a)

/-- ✅ …así que la evaluación de §6 vale sobre el código de toda fórmula y todo término: no es vacía. -/
theorem prf_substfc_codeNat (v : Nat) (s : Term) (φ : Formula) :
    Prf (substfc (numeralM v) (numeralM (codeNatTerm s)) (numeralM (codeNat φ)) =eq
      numeralM (substfcN v (codeNatTerm s) (codeNat φ))) :=
  prf_substfc_numeral (codF_codeNat φ) v _ (codT_codeNatTerm s)

/-- Los códigos cerrados que incrustan `ind` y `listInd` son buenos (los pedirá NegLineWF). -/
theorem codT_TC0 : CodT TC0 := codT_codeNatTerm zero
theorem codT_TCS : CodT TCS := codT_codeNatTerm (succ (.var 0))
theorem codT_TNIL : CodT TNIL := codT_codeNatTerm nil
theorem codT_TCONS : CodT TCONS := codT_codeNatTerm (cons (.var 1) (.var 0))

theorem codF_ne_zero {f : Nat} (h : CodF f) : f ≠ 0 := by
  cases h <;> exact CodeNatInjPrf.consN_ne_zero _ _

/-- ✅ La hipótesis puede fallar: `0` no es un código de fórmula, ni pasa la guarda. -/
theorem not_hasWitFN_zero : ¬ hasWitFN 0 := fun h => codF_ne_zero (codF_of_hasWitFN h) rfl

/-- La variable `0` pasa la guarda de término: el testigo es la lista con su código. -/
theorem hasWitN_var0 : hasWitN (consN 0 (consN 0 0)) := by
  refine ⟨consN (consN 0 (consN 0 0)) 0, fun i hi => ?_, (memN_consN _ _ _).mpr (Or.inl rfl)⟩
  rw [lenN_consN, lenN_zero] at hi
  match i, hi with
  | 0, _ =>
    rw [nthN_cz]
    exact Or.inl (show consN 0 (consN 0 0) = consN 0 (consN (nthN (consN 0 (consN 0 0)) 1) 0) by
      rw [nthN_cs, nthN_cz])
  | i + 1, hi => exact absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero i)

/-- `⊥` pasa la guarda de fórmula: el testigo es la lista con su código, sin términos. -/
theorem hasWitFN_bot : hasWitFN botcN := by
  refine ⟨consN botcN 0, 0, ⟨fun i hi => ?_, fun i hi => ?_⟩, (memN_consN _ _ _).mpr (Or.inl rfl)⟩
  · rw [lenN_zero] at hi; exact absurd hi (Nat.not_lt_zero i)
  · rw [lenN_consN, lenN_zero] at hi
    match i, hi with
    | 0, _ => rw [nthN_cz]; exact Or.inl rfl
    | i + 1, hi => exact absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero i)

/-- ✅ …y puede valer: las dos guardas de `prf_substfc_guarda` se cumplen a la vez. -/
theorem guardas_satisfacibles : And (hasWitFN botcN) (hasWitN (consN 0 (consN 0 0))) :=
  ⟨hasWitFN_bot, hasWitN_var0⟩

end ROBINSON_PlusPlus.Meta.RosserNumEval

#print axioms ROBINSON_PlusPlus.Meta.RosserNumEval.prf_substtc_numeral
#print axioms ROBINSON_PlusPlus.Meta.RosserNumEval.prf_liftc_numeral
#print axioms ROBINSON_PlusPlus.Meta.RosserNumEval.prf_substfc_numeral
#print axioms ROBINSON_PlusPlus.Meta.RosserNumEval.prf_liftfc_numeral
#print axioms ROBINSON_PlusPlus.Meta.RosserNumEval.codF_of_hasWitFN
#print axioms ROBINSON_PlusPlus.Meta.RosserNumEval.prf_substfc_guarda

/-! T08 en el módulo (ADR‑147): lo de esta etapa no nombra la semántica; `ev_numeralM`, el valor de un numeral en el
    modelo, sí. -/
#pureza ROBINSON_PlusPlus.Meta.RosserNumEval.codT_liftcN ROBINSON_PlusPlus.Meta.RosserNumEval.codF_liftfcN
  ROBINSON_PlusPlus.Meta.RosserNumEval.codF_substfcN ROBINSON_PlusPlus.Meta.RosserNumEval.codT_of_hasWitN
  ROBINSON_PlusPlus.Meta.RosserNumEval.codF_of_hasWitFN ROBINSON_PlusPlus.Meta.RosserNumEval.prf_substtc_numeral
  ROBINSON_PlusPlus.Meta.RosserNumEval.prf_liftc_numeral ROBINSON_PlusPlus.Meta.RosserNumEval.prf_liftfc_numeral
  ROBINSON_PlusPlus.Meta.RosserNumEval.prf_substfc_numeral ROBINSON_PlusPlus.Meta.RosserNumEval.prf_substfc_guarda
  ROBINSON_PlusPlus.Meta.RosserNumEval.prf_liftfc_guarda ROBINSON_PlusPlus.Meta.RosserNumEval.prf_substfc_codeNat
  ROBINSON_PlusPlus.Meta.RosserNumEval.guardas_satisfacibles
  | ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM
