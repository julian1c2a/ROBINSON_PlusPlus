/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.RosserNumEval
import ROBINSON_PlusPlus.Meta.Consistencia

/-!
# `Meta/RosserGuardNeg.lean` — Rosser, etapa 3: GuardNeg, la guarda FALSA se refuta (ADR‑146 §3, ADR‑147, ADR‑153)

**Qué.** Donde la guarda es falsa en ℕ, `Prf` la refuta sobre el numeral, con la guarda ENTERA (sus `∃` eliminados):

    ¬ hasWitN c  → Prf (¬ hasWit c̄)          -- prf_neg_hasWit
    ¬ hasWitFN c → Prf (¬ hasWitF c̄)         -- prf_neg_hasWitF

* **§1** ℕ, la mitad de la caracterización que faltaba: un código bueno TIENE testigo (`hasWitN_of_codT`,
  `hasWitFN_of_codF`), juntando los testigos de los hijos. Con la otra mitad (ADR‑152): `hasWitN c ↔ CodT c` y
  `hasWitFN c ↔ CodF c`.
* **§2** ℕ, las formas: una etiqueta y una longitud dicen la forma (`eq_shape1`…`eq_shape3`).
* **§3** `Prf`, los refutadores: una forma posicional que pide otra etiqueta u otra longitud cae (`rej_cOk2`,
  `rej_cOk3`); los selectores (`prf_B2_sel3`…`prf_B2_sel9`) dejan, con la etiqueta, una sola de las ocho cláusulas de
  fórmula; y la carga de la cláusula lleva a un hijo, que se refuta por la hipótesis de inducción.
* **§4** La dicotomía, por inducción fuerte en el número y sin lógica clásica: `codT_or_rejT : CodT c ∨ RejT c` y
  `codF_or_rejF`, donde `RejT c` dice que ninguna lista testigo contiene `c̄`.
* **§5** Los titulares de la etapa, y la guarda DECIDIDA: `hasWit_decide : hasWitN c ∨ Prf ¬hasWit c̄`.

**De dónde.** La forma posicional y sus refutadores son los de `Meta/CodeWitnessPrf.lean` (`prf_isTermCodeE1_str`,
`crit_cOk2_absurd`, `PrfH_inst_argsIn`…); la evaluación sobre numerales, la de ADR‑150 (`prf_nthc_numeral`,
`prf_lenc_numeral`, `prf_carc_numeral`). El esquema es el de `sondeos/RosserBasura.lean` §4 y
`sondeos/RosserHasWitF.lean` §4, de profundidad 1–2, hecho general: la longitud, además de la etiqueta, refuta también
el `0` y las formas con la etiqueta buena y la longitud mala.

**Controles.** `control_neg_hasWit_zero` y `control_neg_hasWitF_zero`: el `0` no es código de nada. Y la recíproca,
`control_exacta` (con la solidez en `MNV V₀`): donde la guarda vale, `Prf` no la refuta. Es el control positivo del
`#pureza`: nombra la semántica.

⛔ Ningún numeral se evalúa: los refutadores van por `crit_num_ne` sobre `carc`/`lenc`/`nthc` evaluados con lemas ∀.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.RosserNumerales ROBINSON_PlusPlus.Meta.RosserNumEval

namespace ROBINSON_PlusPlus.Meta.RosserGuardNeg

/-! ## §1 · ℕ: un código bueno tiene testigo -/

theorem memN_nthN_encodeL_of_lt : ∀ (L : List Nat) (i : Nat), i < L.length → List.Mem (nthN (encodeL L) i) L
  | [], i, h => absurd h (Nat.not_lt_zero i)
  | a :: L, 0, _ => by rw [encodeL, nthN_cz]; exact List.Mem.head L
  | a :: L, i + 1, h => by
      rw [encodeL, nthN_cs]
      exact List.Mem.tail a (memN_nthN_encodeL_of_lt L i (Nat.lt_of_succ_lt_succ h))

/-- Lo que está en una posición de la lista está en la lista. -/
theorem memN_of_lt {l i : Nat} (h : i < lenN l) : memN (nthN l i) l := by
  have e := memN_nthN_encodeL_of_lt (decodeL l) i h
  rw [encodeL_decodeL] at e
  exact e

theorem memN_head (a l : Nat) : memN a (consN a l) := (memN_consN _ _ _).mpr (Or.inl rfl)
theorem memN_tail {x l : Nat} (a : Nat) (h : memN x l) : memN x (consN a l) := (memN_consN _ _ _).mpr (Or.inr h)
theorem memN_cat_l {x a : Nat} (b : Nat) (h : memN x a) : memN x (concatN a b) := (memN_concatN _ _ _).mpr (Or.inl h)
theorem memN_cat_r {x b : Nat} (a : Nat) (h : memN x b) : memN x (concatN a b) := (memN_concatN _ _ _).mpr (Or.inr h)

theorem wfAll1N_of_mem {w : Nat} (h : ∀ e, memN e w → isTermCodeE1N w e) : wfAll1N w :=
  fun _ hi => h _ (memN_of_lt hi)

theorem isTermCodeE1N_of_mem {w e : Nat} (hw : wfAll1N w) (he : memN e w) : isTermCodeE1N w e := by
  obtain ⟨i, hi, hie⟩ := memN_nthN he
  rw [← hie]; exact hw i hi

theorem wfAllFN_of_mem {wF wT : Nat} (h : ∀ e, memN e wF → isFormCodeE2N wF wT e) : wfAllFN wF wT :=
  fun _ hi => h _ (memN_of_lt hi)

theorem isFormCodeE2N_of_mem {wF wT e : Nat} (hw : wfAllFN wF wT) (he : memN e wF) : isFormCodeE2N wF wT e := by
  obtain ⟨i, hi, hie⟩ := memN_nthN he
  rw [← hie]; exact hw i hi

theorem wfAll1N_zero : wfAll1N 0 := fun i hi => absurd hi (by rw [lenN_zero]; exact Nat.not_lt_zero i)
theorem wfAllFN_zero (wT : Nat) : wfAllFN 0 wT := fun i hi => absurd hi (by rw [lenN_zero]; exact Nat.not_lt_zero i)

theorem argsInN_mono {w w' Y : Nat} (hs : ∀ y, memN y w → memN y w') (h : argsInN w Y) : argsInN w' Y :=
  fun i hi => hs _ (h i hi)

theorem isTermCodeE1N_mono {w w' X : Nat} (hs : ∀ y, memN y w → memN y w') (h : isTermCodeE1N w X) :
    isTermCodeE1N w' X := by
  rcases h with hu | ⟨hb, ha⟩
  · exact Or.inl hu
  · exact Or.inr ⟨hb, argsInN_mono hs ha⟩

theorem isFormCodeE2N_mono {wF wF' wT wT' X : Nat} (hF : ∀ y, memN y wF → memN y wF')
    (hT : ∀ y, memN y wT → memN y wT') (h : isFormCodeE2N wF wT X) : isFormCodeE2N wF' wT' X := by
  rcases h with h | ⟨hs, ha⟩ | ⟨hs, h1, h2⟩ | ⟨hs, h1, h2⟩ | ⟨hs, h1⟩ | ⟨hs, h1, h2⟩ | ⟨hs, h1, h2⟩ | ⟨hs, h1⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨hs, argsInN_mono hT ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hs, hT _ h1, hT _ h2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, hF _ h1, hF _ h2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, hF _ h1⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, hF _ h1, hF _ h2⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, hF _ h1, hF _ h2⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hs, hF _ h1⟩))))))

/-- Dos testigos de términos, juntos, siguen siendo un testigo. -/
theorem wfAll1N_concatN {w1 w2 : Nat} (h1 : wfAll1N w1) (h2 : wfAll1N w2) : wfAll1N (concatN w1 w2) :=
  wfAll1N_of_mem fun e he => by
    rcases (memN_concatN _ _ _).mp he with h | h
    · exact isTermCodeE1N_mono (fun _ hy => memN_cat_l _ hy) (isTermCodeE1N_of_mem h1 h)
    · exact isTermCodeE1N_mono (fun _ hy => memN_cat_r _ hy) (isTermCodeE1N_of_mem h2 h)

theorem wfAllFN_concatN {wF1 wF2 wT1 wT2 : Nat} (h1 : wfAllFN wF1 wT1) (h2 : wfAllFN wF2 wT2) :
    wfAllFN (concatN wF1 wF2) (concatN wT1 wT2) :=
  wfAllFN_of_mem fun e he => by
    rcases (memN_concatN _ _ _).mp he with h | h
    · exact isFormCodeE2N_mono (fun _ hy => memN_cat_l _ hy) (fun _ hy => memN_cat_l _ hy) (isFormCodeE2N_of_mem h1 h)
    · exact isFormCodeE2N_mono (fun _ hy => memN_cat_r _ hy) (fun _ hy => memN_cat_r _ hy) (isFormCodeE2N_of_mem h2 h)

theorem nthN_un1 (k a : Nat) : nthN (consN k (consN a 0)) 1 = a := by rw [nthN_cs, nthN_cz]
theorem nthN_bin1 (k a b : Nat) : nthN (consN k (consN a (consN b 0))) 1 = a := by rw [nthN_cs, nthN_cz]
theorem nthN_bin2 (k a b : Nat) : nthN (consN k (consN a (consN b 0))) 2 = b := by rw [nthN_cs, nthN_cs, nthN_cz]

theorem shapeUnN_consN (k a : Nat) : shapeUnN (consN k (consN a 0)) k := by
  show consN k (consN a 0) = consN k (consN (nthN (consN k (consN a 0)) 1) 0)
  rw [nthN_un1]

theorem shapeBinN_consN (k a b : Nat) : shapeBinN (consN k (consN a (consN b 0))) k := by
  show consN k (consN a (consN b 0)) = consN k (consN (nthN (consN k (consN a (consN b 0))) 1)
    (consN (nthN (consN k (consN a (consN b 0))) 2) 0))
  rw [nthN_bin1, nthN_bin2]

mutual
/-- 🏁 **Un código de término tiene testigo**: la lista del nodo y los testigos de sus argumentos. -/
theorem hasWitN_of_codT {c : Nat} (h : CodT c) : hasWitN c :=
  match h with
  | .var n => ⟨consN (consN 0 (consN n 0)) 0, wfAll1N_of_mem fun e he => by
      rcases (memN_consN _ _ _).mp he with rfl | h0
      · exact Or.inl (shapeUnN_consN 0 n)
      · exact absurd h0 (memN_zero e), memN_head _ _⟩
  | .func s ts hts =>
    match witTs_of_codTs hts with
    | ⟨w, hw, hmem⟩ => ⟨consN (consN 1 (consN s (consN ts 0))) w, wfAll1N_of_mem fun e he => by
        rcases (memN_consN _ _ _).mp he with rfl | hew
        · refine Or.inr ⟨shapeBinN_consN 1 s ts, ?_⟩
          rw [nthN_bin2]
          exact fun _ hi => memN_tail _ (hmem _ (memN_of_lt hi))
        · exact isTermCodeE1N_mono (fun _ hy => memN_tail _ hy) (isTermCodeE1N_of_mem hw hew), memN_head _ _⟩
/-- Una lista de códigos de término tiene UN testigo para todos. -/
theorem witTs_of_codTs {ts : Nat} (h : CodTs ts) : ∃ w, And (wfAll1N w) (∀ x, memN x ts → memN x w) :=
  match h with
  | .nil => ⟨0, wfAll1N_zero, fun x hx => absurd hx (memN_zero x)⟩
  | .cons _ _ ha hr =>
    match hasWitN_of_codT ha, witTs_of_codTs hr with
    | ⟨wa, hwa, hma⟩, ⟨wr, hwr, hmr⟩ => ⟨concatN wa wr, wfAll1N_concatN hwa hwr, fun x hx => by
        rcases (memN_consN _ _ _).mp hx with rfl | hxr
        · exact memN_cat_l _ hma
        · exact memN_cat_r _ (hmr _ hxr)⟩
end

/-- Un nodo sobre testigos de sus hijos: con su cláusula contra `X :: wF`, tiene testigo. -/
theorem hasWitFN_node {X wF wT : Nat} (hT : wfAll1N wT) (hF : wfAllFN wF wT)
    (hX : isFormCodeE2N (consN X wF) wT X) : hasWitFN X :=
  ⟨consN X wF, wT, ⟨hT, wfAllFN_of_mem fun e he => by
      rcases (memN_consN _ _ _).mp he with rfl | h
      · exact hX
      · exact isFormCodeE2N_mono (fun _ hy => memN_tail _ hy) (fun _ hy => hy) (isFormCodeE2N_of_mem hF h)⟩,
    memN_head X wF⟩

theorem hasWitFN_bin (k a b : Nat) (inj : ∀ wF wT X : Nat, clBinN wF X k → isFormCodeE2N wF wT X)
    (ha : hasWitFN a) (hb : hasWitFN b) : hasWitFN (consN k (consN a (consN b 0))) := by
  obtain ⟨wFa, wTa, ⟨hTa, hFa⟩, hma⟩ := ha
  obtain ⟨wFb, wTb, ⟨hTb, hFb⟩, hmb⟩ := hb
  refine hasWitFN_node (wF := concatN wFa wFb) (wT := concatN wTa wTb) (wfAll1N_concatN hTa hTb)
    (wfAllFN_concatN hFa hFb) (inj _ _ _ ⟨shapeBinN_consN k a b, ?_, ?_⟩)
  · rw [nthN_bin1]; exact memN_tail _ (memN_cat_l _ hma)
  · rw [nthN_bin2]; exact memN_tail _ (memN_cat_r _ hmb)

theorem hasWitFN_un (k a : Nat) (inj : ∀ wF wT X : Nat, clUnN wF X k → isFormCodeE2N wF wT X)
    (ha : hasWitFN a) : hasWitFN (consN k (consN a 0)) := by
  obtain ⟨wFa, wTa, ⟨hTa, hFa⟩, hma⟩ := ha
  refine hasWitFN_node (wF := wFa) (wT := wTa) hTa hFa (inj _ _ _ ⟨shapeUnN_consN k a, ?_⟩)
  rw [nthN_un1]; exact memN_tail _ hma

/-- 🏁 **Un código de fórmula tiene testigo**. -/
theorem hasWitFN_of_codF {c : Nat} (h : CodF c) : hasWitFN c := by
  induction h with
  | bot => exact hasWitFN_node (wF := 0) (wT := 0) wfAll1N_zero (wfAllFN_zero 0) (Or.inl rfl)
  | atom p ts hts =>
      obtain ⟨w, hw, hmem⟩ := witTs_of_codTs hts
      refine hasWitFN_node (wF := 0) (wT := w) hw (wfAllFN_zero w)
        (Or.inr (Or.inl ⟨shapeBinN_consN 3 p ts, ?_⟩))
      rw [nthN_bin2]; exact fun _ hi => hmem _ (memN_of_lt hi)
  | eq a b ha hb =>
      obtain ⟨wa, hwa, hma⟩ := hasWitN_of_codT ha
      obtain ⟨wb, hwb, hmb⟩ := hasWitN_of_codT hb
      refine hasWitFN_node (wF := 0) (wT := concatN wa wb) (wfAll1N_concatN hwa hwb) (wfAllFN_zero _)
        (Or.inr (Or.inr (Or.inl ⟨shapeBinN_consN 4 a b, ?_, ?_⟩)))
      · rw [nthN_bin1]; exact memN_cat_l _ hma
      · rw [nthN_bin2]; exact memN_cat_r _ hmb
  | impl a b _ _ iha ihb =>
      exact hasWitFN_bin 5 a b (fun _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inl h)))) iha ihb
  | all a _ iha => exact hasWitFN_un 6 a (fun _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) iha
  | and a b _ _ iha ihb =>
      exact hasWitFN_bin 7 a b (fun _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) iha ihb
  | or a b _ _ iha ihb =>
      exact hasWitFN_bin 8 a b (fun _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) iha ihb
  | ex a _ iha =>
      exact hasWitFN_un 9 a (fun _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))) iha

/-- 🏁 **La caracterización en ℕ**: la guarda de término es el árbol. -/
theorem hasWitN_iff (c : Nat) : hasWitN c ↔ CodT c := ⟨codT_of_hasWitN, hasWitN_of_codT⟩

/-- 🏁 Y la de fórmula. -/
theorem hasWitFN_iff (c : Nat) : hasWitFN c ↔ CodF c := ⟨codF_of_hasWitFN, hasWitFN_of_codF⟩

/-! ## §2 · ℕ: la etiqueta y la longitud dicen la forma -/

theorem ne_zero_of_lenN {c ℓ : Nat} (h : lenN c = ℓ) (hℓ : ℓ ≠ 0) : c ≠ 0 := by
  rintro rfl; rw [lenN_zero] at h; exact hℓ h.symm

theorem lenN_eq_zero {c : Nat} (h : lenN c = 0) : c = 0 := by
  cases c with
  | zero => rfl
  | succ m => rw [lenN_cdrN (Nat.succ_ne_zero m)] at h; exact absurd h (Nat.succ_ne_zero _)

theorem eq_shape1 {c : Nat} (h : lenN c = 1) : c = consN (carN c) 0 := by
  have hc := ne_zero_of_lenN h (by decide)
  have h0 : cdrN c = 0 := by
    have e := lenN_cdrN hc; rw [h] at e; exact lenN_eq_zero (Nat.succ.inj e).symm
  calc c = consN (carN c) (cdrN c) := (consN_car_cdr hc).symm
    _ = consN (carN c) 0 := by rw [h0]

theorem eq_shape2 {c : Nat} (h : lenN c = 2) : c = consN (carN c) (consN (nthN c 1) 0) := by
  have hc := ne_zero_of_lenN h (by decide)
  have h1 : lenN (cdrN c) = 1 := by
    have e := lenN_cdrN hc; rw [h] at e; exact (Nat.succ.inj e).symm
  calc c = consN (carN c) (cdrN c) := (consN_car_cdr hc).symm
    _ = consN (carN c) (consN (carN (cdrN c)) 0) := congrArg (consN (carN c)) (eq_shape1 h1)

theorem eq_shape3 {c : Nat} (h : lenN c = 3) : c = consN (carN c) (consN (nthN c 1) (consN (nthN c 2) 0)) := by
  have hc := ne_zero_of_lenN h (by decide)
  have h2 : lenN (cdrN c) = 2 := by
    have e := lenN_cdrN hc; rw [h] at e; exact (Nat.succ.inj e).symm
  calc c = consN (carN c) (cdrN c) := (consN_car_cdr hc).symm
    _ = consN (carN c) (consN (carN (cdrN c)) (consN (nthN (cdrN c) 1) 0)) :=
        congrArg (consN (carN c)) (eq_shape2 h2)

theorem eq_nul_of {c k : Nat} (h : And (carN c = k) (lenN c = 1)) : c = consN k 0 := by
  have e := eq_shape1 h.2; rw [h.1] at e; exact e

theorem eq_un_of {c k : Nat} (h : And (carN c = k) (lenN c = 2)) : c = consN k (consN (nthN c 1) 0) := by
  have e := eq_shape2 h.2; rw [h.1] at e; exact e

theorem eq_bin_of {c k : Nat} (h : And (carN c = k) (lenN c = 3)) :
    c = consN k (consN (nthN c 1) (consN (nthN c 2) 0)) := by
  have e := eq_shape3 h.2; rw [h.1] at e; exact e

/-- Una disyunción por cada elemento de una lista da todos de un lado o uno del otro (por la lista: sin lógica
    clásica). -/
theorem list_or_aux {P Q : Nat → Prop} : ∀ L : List Nat, (∀ x, List.Mem x L → Or (P x) (Q x)) →
    Or (∀ x, List.Mem x L → P x) (∃ x, And (List.Mem x L) (Q x))
  | [], _ => Or.inl fun _ hx => nomatch hx
  | a :: L, h =>
    match h a (List.Mem.head L), list_or_aux L fun x hx => h x (List.Mem.tail a hx) with
    | Or.inr hq, _ => Or.inr ⟨a, List.Mem.head L, hq⟩
    | Or.inl _, Or.inr ⟨x, hx, hq⟩ => Or.inr ⟨x, List.Mem.tail a hx, hq⟩
    | Or.inl hp, Or.inl hall => Or.inl fun x hx =>
        match hx with
        | List.Mem.head _ => hp
        | List.Mem.tail _ hx' => hall x hx'

theorem list_or {P Q : Nat → Prop} {l : Nat} (h : ∀ x, memN x l → Or (P x) (Q x)) :
    Or (∀ x, memN x l → P x) (∃ x, And (memN x l) (Q x)) :=
  list_or_aux (decodeL l) h

/-! ## §3 · `Prf`: los refutadores -/

/-- Ninguna lista testigo de TÉRMINOS contiene `c̄`. -/
def RejT (c : Nat) : Prop := ∀ w : Term, Prf (isTC1 w (numeralM c) ⇒ Formula.bottom)

/-- Ninguna lista testigo de FÓRMULAS contiene `c̄`. -/
def RejF (c : Nat) : Prop := ∀ wF wT : Term, Prf (isFC1 wF wT (numeralM c) ⇒ Formula.bottom)

theorem imp_of_absurd {D C : Formula} (h : Prf (D ⇒ Formula.bottom)) : Prf (D ⇒ C) :=
  impT h (Prf.incl (Prfᵢ.efq _))

/-- La hermana de `crit_tag_absurd` para la longitud. -/
theorem crit_len_absurd (X : Term) (k m : Nat) (hkm : k ≠ m) (hX : Prf (lenc X =eq numeralM k)) :
    Prf (Formula.impl (Formula.eq (lenc X) (numeralM m)) Formula.bottom) :=
  prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (crit_num_ne k m hkm) _)
    (PrfH_eq_trans (prf_to_prfH (prf_eq_symm hX) _) (prfH_hyp_self _)))

theorem prf_carc_tag {c k : Nat} (hk : carN c = k) (hc : c ≠ 0) : Prf (carc (numeralM c) =eq numeralM k) := by
  rw [← hk]; exact prf_carc_numeral hc

/-- Una forma que pide `carc c̄ = k̄` y `lenc c̄ = ℓ̄` (`ℓ ≠ 0`) cae si `c` no tiene esa etiqueta y esa longitud: por la
    longitud, que se evalúa siempre, o por la etiqueta. -/
theorem prf_tagLen_absurd (c k ℓ : Nat) (hℓ : ℓ ≠ 0) (h : ¬ And (carN c = k) (lenN c = ℓ)) :
    Prf (land (Formula.eq (carc (numeralM c)) (numeralM k)) (Formula.eq (lenc (numeralM c)) (numeralM ℓ))
      ⇒ Formula.bottom) := by
  by_cases hl : lenN c = ℓ
  · exact impT (Prf.incl (Prfᵢ.c2 _ _)) (crit_tag_absurd _ (carN c) k (fun e => h ⟨e, hl⟩)
      (prf_carc_numeral (ne_zero_of_lenN hl hℓ)))
  · exact impT (Prf.incl (Prfᵢ.c3 _ _)) (crit_len_absurd _ (lenN c) ℓ hl (prf_lenc_numeral c))

/-- Una forma posicional sin carga (`varOkT`, `nulOkF`) con otra etiqueta o longitud, cae. -/
theorem rej_cOk2 (c k ℓ : Nat) (hℓ : ℓ ≠ 0) (h : ¬ And (carN c = k) (lenN c = ℓ)) :
    Prf (cOk (numeralM c) (land (Formula.eq (carc (numeralM c)) (numeralM k))
      (Formula.eq (lenc (numeralM c)) (numeralM ℓ))) ⇒ Formula.bottom) :=
  impT (Prf.incl (Prfᵢ.c3 _ _)) (prf_tagLen_absurd c k ℓ hℓ h)

/-- Y una con carga (`funcOkT1`, `strBinOkF1`, `binOkF`, `unOkF`). -/
theorem rej_cOk3 (c k ℓ : Nat) (hℓ : ℓ ≠ 0) (h : ¬ And (carN c = k) (lenN c = ℓ)) (M : Formula) :
    Prf (cOk (numeralM c) (land (land (Formula.eq (carc (numeralM c)) (numeralM k))
      (Formula.eq (lenc (numeralM c)) (numeralM ℓ))) M) ⇒ Formula.bottom) :=
  impT (Prf.incl (Prfᵢ.c3 _ _)) (impT (Prf.incl (Prfᵢ.c2 _ _)) (prf_tagLen_absurd c k ℓ hℓ h))

/-- La carga de una forma posicional. -/
theorem PrfH_pay {Γ : List Formula} {X : Term} {A B C : Formula} (hD : PrfH Γ (cOk X (land (land A B) C))) :
    PrfH Γ C :=
  PrfH_and_elim_right (PrfH_and_elim_right hD)

/-- La casilla `i` de `c̄`, evaluada dentro de un `In`. -/
theorem PrfH_slot {Γ : List Formula} {w : Term} {c : Nat} (i : Nat) (hi : i < lenN c)
    (h : PrfH Γ (In (nthc (numeralM c) (numeralM i)) w)) : PrfH Γ (In (numeralM (nthN c i)) w) :=
  PrfH_congr_In_left (prf_to_prfH (prf_nthc_numeral i c hi) _) h

/-- De `argsIn w (nthc c̄ 2̄)`, un argumento `x` de `c` está en `w`. -/
theorem PrfH_argsIn_mem {Γ : List Formula} {w : Term} {c x : Nat} (h2 : 2 < lenN c) (hx : memN x (nthN c 2))
    (h : PrfH Γ (argsIn w (nthc (numeralM c) (numeralM 2)))) : PrfH Γ (In (numeralM x) w) := by
  obtain ⟨i, hi, hie⟩ := memN_nthN hx
  have hts := prf_nthc_numeral 2 c h2
  have hlt : Prf (lt (numeralM i) (lenc (nthc (numeralM c) (numeralM 2)))) :=
    prf_lt_subst2 (prf_eq_symm (prf_eq_trans (prf_congr_lenc hts) (prf_lenc_numeral _)))
      (LineWFTrackedPrf.prf_lt_numeralM hi)
  have hin := PrfH.mp _ _ _ (PrfH_inst_argsIn w _ (numeralM i) h) (prf_to_prfH hlt _)
  have hx' : Prf (nthc (nthc (numeralM c) (numeralM 2)) (numeralM i) =eq numeralM x) := by
    rw [← hie]
    exact prf_eq_trans (prf_congr_nthc_lst _ hts) (prf_nthc_numeral i _ hi)
  exact PrfH_congr_In_left (prf_to_prfH hx' _) hin

/-- Un hijo de término refutado refuta al padre: está en el mismo testigo. -/
theorem rejT_slot {x : Nat} (hr : RejT x) {w : Term} {Γ : List Formula} (hin : PrfH Γ (In (numeralM x) w))
    (hwf : PrfH Γ (wfAll1 w)) : PrfH Γ Formula.bottom :=
  PrfH.mp _ _ _ (prf_to_prfH (hr w) _) (PrfH_and_intro hwf hin)

/-- Un hijo de fórmula refutado refuta al padre. -/
theorem rejF_slot {x : Nat} (hr : RejF x) {wF wT : Term} {Γ : List Formula} (hin : PrfH Γ (In (numeralM x) wF))
    (hw : PrfH Γ (land (wfAll1 wT) (wfAllF wF wT))) : PrfH Γ Formula.bottom :=
  PrfH.mp _ _ _ (prf_to_prfH (hr wF wT) _) (PrfH_and_intro hw hin)

theorem rejT_arg {c x : Nat} (h2 : 2 < lenN c) (hx : memN x (nthN c 2)) (hr : RejT x) {w : Term}
    {Γ : List Formula} (hargs : PrfH Γ (argsIn w (nthc (numeralM c) (numeralM 2)))) (hwf : PrfH Γ (wfAll1 w)) :
    PrfH Γ Formula.bottom :=
  rejT_slot hr (PrfH_argsIn_mem h2 hx hargs) hwf

/-! ### Términos: las dos ramas de `isTermCodeB1` -/

theorem rejT_via {c : Nat} (dv : Prf (cOk (numeralM c) (varOkT (numeralM c)) ⇒ Formula.bottom))
    (pay : ∀ (w : Term) (Γ : List Formula), PrfH Γ (cOk (numeralM c) (funcOkT1 w (numeralM c))) →
      PrfH Γ (wfAll1 w) → PrfH Γ Formula.bottom) : RejT c := fun w => by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (isTC1 w (numeralM c))
  have hE := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_of_In w _) _) (PrfH_and_elim_right hh))
    (PrfH_and_elim_left hh)
  have hB := PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_str w _) _) hE
  refine PrfH_or_elim hB (PrfH.mp _ _ _ (prf_to_prfH dv _) (PrfH.hyp _ _ (List.Mem.head _))) ?_
  exact pay w _ (PrfH.hyp _ _ (List.Mem.head _))
    (PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))))

/-- Ni variable ni función: las dos ramas caen por la forma. -/
theorem rejT_shape {c : Nat} (hv : ¬ And (carN c = 0) (lenN c = 2)) (hf : ¬ And (carN c = 1) (lenN c = 3)) :
    RejT c :=
  rejT_via (rej_cOk2 c 0 2 (by decide) hv) fun _ _ hD _ =>
    PrfH.mp _ _ _ (prf_to_prfH (rej_cOk3 c 1 3 (by decide) hf _) _) hD

/-- Una función con un argumento malo. -/
theorem rejT_func {c x : Nat} (hf : And (carN c = 1) (lenN c = 3)) (hx : memN x (nthN c 2)) (hr : RejT x) :
    RejT c :=
  rejT_via (rej_cOk2 c 0 2 (by decide) fun h => absurd (hf.1.symm.trans h.1) (by decide))
    fun _ _ hD hwf => rejT_arg (by rw [hf.2]; decide) hx hr (PrfH_pay hD) hwf

/-! ### Fórmulas: los selectores, y las ocho cláusulas de `isFormCodeB2` -/

theorem prf_B2_sel3 (wF wT X : Term) (hX : Prf (carc X =eq numeralM 3)) :
    Prf (isFormCodeB2 wF wT X ⇒ cOk X (strBinOkF1 wT X 3)) := by
  simp only [isFormCodeB2, lorAll]
  exact prf_or_elim_imp (imp_of_absurd (crit_cOk2_absurd X 3 2 (by decide) hX _))
    (prf_or_elim_imp (prf_deduction (prfH_hyp_self _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 3 4 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 3 5 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 3 6 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 3 7 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 3 8 (by decide) hX _ _))
      (imp_of_absurd (crit_cOk3_absurd X 3 9 (by decide) hX _ _))))))))

theorem prf_B2_sel4 (wF wT X : Term) (hX : Prf (carc X =eq numeralM 4)) :
    Prf (isFormCodeB2 wF wT X ⇒ cOk X (binOkF wT wT X 4)) := by
  simp only [isFormCodeB2, lorAll]
  exact prf_or_elim_imp (imp_of_absurd (crit_cOk2_absurd X 4 2 (by decide) hX _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 4 3 (by decide) hX _ _))
    (prf_or_elim_imp (prf_deduction (prfH_hyp_self _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 4 5 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 4 6 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 4 7 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 4 8 (by decide) hX _ _))
      (imp_of_absurd (crit_cOk3_absurd X 4 9 (by decide) hX _ _))))))))

theorem prf_B2_sel5 (wF wT X : Term) (hX : Prf (carc X =eq numeralM 5)) :
    Prf (isFormCodeB2 wF wT X ⇒ cOk X (binOkF wF wF X 5)) := by
  simp only [isFormCodeB2, lorAll]
  exact prf_or_elim_imp (imp_of_absurd (crit_cOk2_absurd X 5 2 (by decide) hX _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 5 3 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 5 4 (by decide) hX _ _))
    (prf_or_elim_imp (prf_deduction (prfH_hyp_self _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 5 6 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 5 7 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 5 8 (by decide) hX _ _))
      (imp_of_absurd (crit_cOk3_absurd X 5 9 (by decide) hX _ _))))))))

theorem prf_B2_sel6 (wF wT X : Term) (hX : Prf (carc X =eq numeralM 6)) :
    Prf (isFormCodeB2 wF wT X ⇒ cOk X (unOkF wF X 6)) := by
  simp only [isFormCodeB2, lorAll]
  exact prf_or_elim_imp (imp_of_absurd (crit_cOk2_absurd X 6 2 (by decide) hX _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 6 3 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 6 4 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 6 5 (by decide) hX _ _))
    (prf_or_elim_imp (prf_deduction (prfH_hyp_self _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 6 7 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 6 8 (by decide) hX _ _))
      (imp_of_absurd (crit_cOk3_absurd X 6 9 (by decide) hX _ _))))))))

theorem prf_B2_sel7 (wF wT X : Term) (hX : Prf (carc X =eq numeralM 7)) :
    Prf (isFormCodeB2 wF wT X ⇒ cOk X (binOkF wF wF X 7)) := by
  simp only [isFormCodeB2, lorAll]
  exact prf_or_elim_imp (imp_of_absurd (crit_cOk2_absurd X 7 2 (by decide) hX _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 7 3 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 7 4 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 7 5 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 7 6 (by decide) hX _ _))
    (prf_or_elim_imp (prf_deduction (prfH_hyp_self _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 7 8 (by decide) hX _ _))
      (imp_of_absurd (crit_cOk3_absurd X 7 9 (by decide) hX _ _))))))))

theorem prf_B2_sel8 (wF wT X : Term) (hX : Prf (carc X =eq numeralM 8)) :
    Prf (isFormCodeB2 wF wT X ⇒ cOk X (binOkF wF wF X 8)) := by
  simp only [isFormCodeB2, lorAll]
  exact prf_or_elim_imp (imp_of_absurd (crit_cOk2_absurd X 8 2 (by decide) hX _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 8 3 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 8 4 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 8 5 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 8 6 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 8 7 (by decide) hX _ _))
    (prf_or_elim_imp (prf_deduction (prfH_hyp_self _))
      (imp_of_absurd (crit_cOk3_absurd X 8 9 (by decide) hX _ _))))))))

theorem prf_B2_sel9 (wF wT X : Term) (hX : Prf (carc X =eq numeralM 9)) :
    Prf (isFormCodeB2 wF wT X ⇒ cOk X (unOkF wF X 9)) := by
  simp only [isFormCodeB2, lorAll]
  exact prf_or_elim_imp (imp_of_absurd (crit_cOk2_absurd X 9 2 (by decide) hX _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 9 3 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 9 4 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 9 5 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 9 6 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 9 7 (by decide) hX _ _))
    (prf_or_elim_imp (imp_of_absurd (crit_cOk3_absurd X 9 8 (by decide) hX _ _))
      (prf_deduction (prfH_hyp_self _))))))))

/-- De `c̄ ∈ wF` y `wfAllF`, la forma posicional de `c̄`; refutar lo que el selector deja refuta `isFC1`. -/
theorem rejF_via {c : Nat} {D : Term → Term → Formula}
    (sel : ∀ wF wT : Term, Prf (isFormCodeB2 wF wT (numeralM c) ⇒ D wF wT))
    (pay : ∀ (wF wT : Term) (Γ : List Formula), PrfH Γ (D wF wT) → PrfH Γ (isFC1 wF wT (numeralM c)) →
      PrfH Γ Formula.bottom) : RejF c := fun wF wT => by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (isFC1 wF wT (numeralM c))
  have hE := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (ENS.prf_isFormCodeE2_of_In wF wT _) _)
    (PrfH_and_elim_right hh)) (PrfH_and_elim_right (PrfH_and_elim_left hh))
  have hB := PrfH.mp _ _ _ (prf_to_prfH (ENS.prf_isFormCodeE2_str wF wT _) _) hE
  exact pay wF wT _ (PrfH.mp _ _ _ (prf_to_prfH (sel wF wT) _) hB) hh

/-- Ninguna de las ocho formas: todas caen por la etiqueta o por la longitud. -/
theorem rejF_shape {c : Nat} (s2 : ¬ And (carN c = 2) (lenN c = 1)) (s3 : ¬ And (carN c = 3) (lenN c = 3))
    (s4 : ¬ And (carN c = 4) (lenN c = 3)) (s5 : ¬ And (carN c = 5) (lenN c = 3))
    (s6 : ¬ And (carN c = 6) (lenN c = 2)) (s7 : ¬ And (carN c = 7) (lenN c = 3))
    (s8 : ¬ And (carN c = 8) (lenN c = 3)) (s9 : ¬ And (carN c = 9) (lenN c = 2)) : RejF c := by
  refine rejF_via (D := fun _ _ => Formula.bottom) (fun wF wT => ?_) (fun _ _ _ hD _ => hD)
  simp only [isFormCodeB2, lorAll]
  exact prf_or_elim_imp (rej_cOk2 c 2 1 (by decide) s2)
    (prf_or_elim_imp (rej_cOk3 c 3 3 (by decide) s3 _) (prf_or_elim_imp (rej_cOk3 c 4 3 (by decide) s4 _)
    (prf_or_elim_imp (rej_cOk3 c 5 3 (by decide) s5 _) (prf_or_elim_imp (rej_cOk3 c 6 2 (by decide) s6 _)
    (prf_or_elim_imp (rej_cOk3 c 7 3 (by decide) s7 _) (prf_or_elim_imp (rej_cOk3 c 8 3 (by decide) s8 _)
      (rej_cOk3 c 9 2 (by decide) s9 _)))))))

/-- Un átomo con un argumento malo. -/
theorem rejF_atom {c x : Nat} (hs : And (carN c = 3) (lenN c = 3)) (hx : memN x (nthN c 2)) (hr : RejT x) :
    RejF c :=
  rejF_via (fun wF wT => prf_B2_sel3 wF wT _ (prf_carc_tag hs.1 (ne_zero_of_lenN hs.2 (by decide))))
    fun _ _ _ hD hH => rejT_arg (by rw [hs.2]; decide) hx hr (PrfH_pay hD) (PrfH_and_elim_left (PrfH_and_elim_left hH))

/-- Una igualdad con un miembro malo (el 1.º o el 2.º). -/
theorem rejF_eq1 {c : Nat} (hs : And (carN c = 4) (lenN c = 3)) (hr : RejT (nthN c 1)) : RejF c :=
  rejF_via (fun wF wT => prf_B2_sel4 wF wT _ (prf_carc_tag hs.1 (ne_zero_of_lenN hs.2 (by decide))))
    fun _ _ _ hD hH => rejT_slot hr (PrfH_slot 1 (by rw [hs.2]; decide) (PrfH_and_elim_left (PrfH_pay hD)))
      (PrfH_and_elim_left (PrfH_and_elim_left hH))

theorem rejF_eq2 {c : Nat} (hs : And (carN c = 4) (lenN c = 3)) (hr : RejT (nthN c 2)) : RejF c :=
  rejF_via (fun wF wT => prf_B2_sel4 wF wT _ (prf_carc_tag hs.1 (ne_zero_of_lenN hs.2 (by decide))))
    fun _ _ _ hD hH => rejT_slot hr (PrfH_slot 2 (by rw [hs.2]; decide) (PrfH_and_elim_right (PrfH_pay hD)))
      (PrfH_and_elim_left (PrfH_and_elim_left hH))

/-- Una cláusula binaria de fórmula (`implc`, `andc`, `orc`) con un hijo malo (el 1.º o el 2.º). -/
theorem rejF_bin1 {c : Nat} (k : Nat)
    (sel : ∀ wF wT X : Term, Prf (carc X =eq numeralM k) → Prf (isFormCodeB2 wF wT X ⇒ cOk X (binOkF wF wF X k)))
    (hs : And (carN c = k) (lenN c = 3)) (hr : RejF (nthN c 1)) : RejF c :=
  rejF_via (fun wF wT => sel wF wT _ (prf_carc_tag hs.1 (ne_zero_of_lenN hs.2 (by decide))))
    fun _ _ _ hD hH => rejF_slot hr (PrfH_slot 1 (by rw [hs.2]; decide) (PrfH_and_elim_left (PrfH_pay hD)))
      (PrfH_and_elim_left hH)

theorem rejF_bin2 {c : Nat} (k : Nat)
    (sel : ∀ wF wT X : Term, Prf (carc X =eq numeralM k) → Prf (isFormCodeB2 wF wT X ⇒ cOk X (binOkF wF wF X k)))
    (hs : And (carN c = k) (lenN c = 3)) (hr : RejF (nthN c 2)) : RejF c :=
  rejF_via (fun wF wT => sel wF wT _ (prf_carc_tag hs.1 (ne_zero_of_lenN hs.2 (by decide))))
    fun _ _ _ hD hH => rejF_slot hr (PrfH_slot 2 (by rw [hs.2]; decide) (PrfH_and_elim_right (PrfH_pay hD)))
      (PrfH_and_elim_left hH)

/-- Una cláusula unaria (`forallc`, `exc`) con el hijo malo. -/
theorem rejF_un1 {c : Nat} (k : Nat)
    (sel : ∀ wF wT X : Term, Prf (carc X =eq numeralM k) → Prf (isFormCodeB2 wF wT X ⇒ cOk X (unOkF wF X k)))
    (hs : And (carN c = k) (lenN c = 2)) (hr : RejF (nthN c 1)) : RejF c :=
  rejF_via (fun wF wT => sel wF wT _ (prf_carc_tag hs.1 (ne_zero_of_lenN hs.2 (by decide))))
    fun _ _ _ hD hH => rejF_slot hr (PrfH_slot 1 (by rw [hs.2]; decide) (PrfH_pay hD)) (PrfH_and_elim_left hH)

/-! ## §4 · La dicotomía, por inducción fuerte en el número -/

/-- 🏁 **Todo número es un código de término, o `Prf` lo saca de toda lista testigo.** -/
theorem codT_or_rejT : ∀ c : Nat, Or (CodT c) (RejT c) := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
    by_cases hv : And (carN c = 0) (lenN c = 2)
    · exact Or.inl (by rw [eq_un_of hv]; exact .var _)
    by_cases hf : And (carN c = 1) (lenN c = 3)
    · have hc := ne_zero_of_lenN hf.2 (by decide)
      rcases list_or (P := CodT) (Q := RejT) (l := nthN c 2)
          (fun x hx => ih x (Nat.lt_trans (memN_lt hx) (nthN_lt 2 hc))) with hall | ⟨x, hx, hr⟩
      · exact Or.inl (by rw [eq_bin_of hf]; exact .func _ _ (codTs_of_mem hall))
      · exact Or.inr (rejT_func hf hx hr)
    exact Or.inr (rejT_shape hv hf)

/-- 🏁 **Todo número es un código de fórmula, o `Prf` lo saca de todo par de listas testigo.** -/
theorem codF_or_rejF : ∀ c : Nat, Or (CodF c) (RejF c) := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
    by_cases s2 : And (carN c = 2) (lenN c = 1)
    · exact Or.inl (by rw [eq_nul_of s2]; exact .bot)
    by_cases s3 : And (carN c = 3) (lenN c = 3)
    · rcases list_or (P := CodT) (Q := RejT) (l := nthN c 2) (fun x _ => codT_or_rejT x) with hall | ⟨x, hx, hr⟩
      · exact Or.inl (by rw [eq_bin_of s3]; exact .atom _ _ (codTs_of_mem hall))
      · exact Or.inr (rejF_atom s3 hx hr)
    by_cases s4 : And (carN c = 4) (lenN c = 3)
    · rcases codT_or_rejT (nthN c 1) with h1 | h1
      · rcases codT_or_rejT (nthN c 2) with h2 | h2
        · exact Or.inl (by rw [eq_bin_of s4]; exact .eq _ _ h1 h2)
        · exact Or.inr (rejF_eq2 s4 h2)
      · exact Or.inr (rejF_eq1 s4 h1)
    by_cases s5 : And (carN c = 5) (lenN c = 3)
    · have hc := ne_zero_of_lenN s5.2 (by decide)
      rcases ih _ (nthN_lt 1 hc) with h1 | h1
      · rcases ih _ (nthN_lt 2 hc) with h2 | h2
        · exact Or.inl (by rw [eq_bin_of s5]; exact .impl _ _ h1 h2)
        · exact Or.inr (rejF_bin2 5 prf_B2_sel5 s5 h2)
      · exact Or.inr (rejF_bin1 5 prf_B2_sel5 s5 h1)
    by_cases s6 : And (carN c = 6) (lenN c = 2)
    · have hc := ne_zero_of_lenN s6.2 (by decide)
      rcases ih _ (nthN_lt 1 hc) with h1 | h1
      · exact Or.inl (by rw [eq_un_of s6]; exact .all _ h1)
      · exact Or.inr (rejF_un1 6 prf_B2_sel6 s6 h1)
    by_cases s7 : And (carN c = 7) (lenN c = 3)
    · have hc := ne_zero_of_lenN s7.2 (by decide)
      rcases ih _ (nthN_lt 1 hc) with h1 | h1
      · rcases ih _ (nthN_lt 2 hc) with h2 | h2
        · exact Or.inl (by rw [eq_bin_of s7]; exact .and _ _ h1 h2)
        · exact Or.inr (rejF_bin2 7 prf_B2_sel7 s7 h2)
      · exact Or.inr (rejF_bin1 7 prf_B2_sel7 s7 h1)
    by_cases s8 : And (carN c = 8) (lenN c = 3)
    · have hc := ne_zero_of_lenN s8.2 (by decide)
      rcases ih _ (nthN_lt 1 hc) with h1 | h1
      · rcases ih _ (nthN_lt 2 hc) with h2 | h2
        · exact Or.inl (by rw [eq_bin_of s8]; exact .or _ _ h1 h2)
        · exact Or.inr (rejF_bin2 8 prf_B2_sel8 s8 h2)
      · exact Or.inr (rejF_bin1 8 prf_B2_sel8 s8 h1)
    by_cases s9 : And (carN c = 9) (lenN c = 2)
    · have hc := ne_zero_of_lenN s9.2 (by decide)
      rcases ih _ (nthN_lt 1 hc) with h1 | h1
      · exact Or.inl (by rw [eq_un_of s9]; exact .ex _ h1)
      · exact Or.inr (rejF_un1 9 prf_B2_sel9 s9 h1)
    exact Or.inr (rejF_shape s2 s3 s4 s5 s6 s7 s8 s9)

/-! ## §5 · GuardNeg -/

theorem prf_neg_hasWit_of_rejT {c : Nat} (h : RejT c) : Prf (neg (hasWit (numeralM c))) := by
  refine prf_ex_elim_imp ?_
  rw [ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM]
  show PrfH [isTC1 (.var 0) (numeralM c)] Formula.bottom
  exact PrfH.mp _ _ _ (prf_to_prfH (h (.var 0)) _) (prfH_hyp_self _)

theorem prf_neg_hasWitF_of_rejF {c : Nat} (h : RejF c) : Prf (neg (hasWitF (numeralM c))) := by
  refine prf_ex_elim_imp ?_
  rw [ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM, ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM]
  show PrfH [Formula.ex (isFC1 (.var 1) (.var 0) (numeralM c))] Formula.bottom
  have hB : PrfH [isFC1 (.var 1) (.var 0) (numeralM c)] Formula.bottom :=
    PrfH.mp _ _ _ (prf_to_prfH (h (.var 1) (.var 0)) _) (prfH_hyp_self _)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_ex_elim_imp (C := Formula.bottom) hB) _) (prfH_hyp_self _)

/-- 🏁 **GuardNeg, la guarda de TÉRMINO**: si `c` no tiene testigo en ℕ, `Prf` refuta `hasWit c̄`. -/
theorem prf_neg_hasWit {c : Nat} (h : ¬ hasWitN c) : Prf (neg (hasWit (numeralM c))) := by
  rcases codT_or_rejT c with hc | hr
  · exact absurd (hasWitN_of_codT hc) h
  · exact prf_neg_hasWit_of_rejT hr

/-- 🏁 **GuardNeg, la guarda de FÓRMULA**. -/
theorem prf_neg_hasWitF {c : Nat} (h : ¬ hasWitFN c) : Prf (neg (hasWitF (numeralM c))) := by
  rcases codF_or_rejF c with hc | hr
  · exact absurd (hasWitFN_of_codF hc) h
  · exact prf_neg_hasWitF_of_rejF hr

/-- 🏁 **La guarda de término, DECIDIDA**: ℕ la cumple o `Prf` la refuta (sin lógica clásica). -/
theorem hasWit_decide (c : Nat) : Or (hasWitN c) (Prf (neg (hasWit (numeralM c)))) := by
  rcases codT_or_rejT c with hc | hr
  · exact Or.inl (hasWitN_of_codT hc)
  · exact Or.inr (prf_neg_hasWit_of_rejT hr)

/-- 🏁 Y la de fórmula. -/
theorem hasWitF_decide (c : Nat) : Or (hasWitFN c) (Prf (neg (hasWitF (numeralM c)))) := by
  rcases codF_or_rejF c with hc | hr
  · exact Or.inl (hasWitFN_of_codF hc)
  · exact Or.inr (prf_neg_hasWitF_of_rejF hr)

/-! ## §6 · Controles -/

theorem codT_ne_zero {c : Nat} (h : CodT c) : c ≠ 0 := by
  cases h <;> exact CodeNatInjPrf.consN_ne_zero _ _

/-- ✅ La hipótesis se cumple: el `0` no es código de término, y `Prf` lo refuta. -/
theorem control_neg_hasWit_zero : Prf (neg (hasWit (numeralM 0))) :=
  prf_neg_hasWit fun h => codT_ne_zero (codT_of_hasWitN h) rfl

/-- ✅ Ni de fórmula. -/
theorem control_neg_hasWitF_zero : Prf (neg (hasWitF (numeralM 0))) :=
  prf_neg_hasWitF fun h => codF_ne_zero (codF_of_hasWitFN h) rfl

/-- ✅ **…y sólo donde la guarda es falsa**: donde vale en ℕ, `Prf` no la refuta, por la solidez en `MNV V₀`. Nombra la
    semántica: es el control positivo del `#pureza`. -/
theorem control_exacta (c : Nat) (h : hasWitN c) : ¬ Prf (neg (hasWit (numeralM c))) := by
  intro hp
  have hs := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN hp
    (fun _ => 0)
  apply hs
  rw [ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_hasWit, ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM]
  exact h

/-- ✅ Lo mismo para la guarda de fórmula. -/
theorem control_exactaF (c : Nat) (h : hasWitFN c) : ¬ Prf (neg (hasWitF (numeralM c))) := by
  intro hp
  have hs := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN hp
    (fun _ => 0)
  apply hs
  rw [ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_hasWitF, ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM]
  exact h

end ROBINSON_PlusPlus.Meta.RosserGuardNeg

#print axioms ROBINSON_PlusPlus.Meta.RosserGuardNeg.hasWitN_of_codT
#print axioms ROBINSON_PlusPlus.Meta.RosserGuardNeg.hasWitFN_of_codF
#print axioms ROBINSON_PlusPlus.Meta.RosserGuardNeg.codT_or_rejT
#print axioms ROBINSON_PlusPlus.Meta.RosserGuardNeg.codF_or_rejF
#print axioms ROBINSON_PlusPlus.Meta.RosserGuardNeg.prf_neg_hasWit
#print axioms ROBINSON_PlusPlus.Meta.RosserGuardNeg.prf_neg_hasWitF

/-! T08 en el módulo (ADR‑147): lo de esta etapa no nombra la semántica; `control_exacta`, que usa la solidez en el
    modelo, sí. -/
#pureza ROBINSON_PlusPlus.Meta.RosserGuardNeg.hasWitN_of_codT ROBINSON_PlusPlus.Meta.RosserGuardNeg.hasWitFN_of_codF
  ROBINSON_PlusPlus.Meta.RosserGuardNeg.hasWitN_iff ROBINSON_PlusPlus.Meta.RosserGuardNeg.hasWitFN_iff
  ROBINSON_PlusPlus.Meta.RosserGuardNeg.codT_or_rejT ROBINSON_PlusPlus.Meta.RosserGuardNeg.codF_or_rejF
  ROBINSON_PlusPlus.Meta.RosserGuardNeg.prf_neg_hasWit ROBINSON_PlusPlus.Meta.RosserGuardNeg.prf_neg_hasWitF
  ROBINSON_PlusPlus.Meta.RosserGuardNeg.hasWit_decide ROBINSON_PlusPlus.Meta.RosserGuardNeg.hasWitF_decide
  ROBINSON_PlusPlus.Meta.RosserGuardNeg.control_neg_hasWit_zero
  ROBINSON_PlusPlus.Meta.RosserGuardNeg.control_neg_hasWitF_zero
  | ROBINSON_PlusPlus.Meta.RosserGuardNeg.control_exacta ROBINSON_PlusPlus.Meta.RosserGuardNeg.control_exactaF
