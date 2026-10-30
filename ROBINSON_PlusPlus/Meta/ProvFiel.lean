/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.RosserNegNum
import ROBINSON_PlusPlus.Meta.RigidezEstandar

/-!
# `Meta/ProvFiel.lean` — `Prov` es FIEL, sin lógica clásica: la vuelta de `modelo_prov_iff` (ADR‑191)

La ida de `modelo_prov_iff` —lo que el modelo cree demostrable, lo es— es W1 (`prf_of_prov`, `prf_of_prov_de`), y ya
era intuicionista. La vuelta —todo teorema es demostrable para el modelo— se hacía leyendo D1 (`repr_pos'_prf`) por la
solidez en `Prop`, `prf_sound`, que lleva la lógica clásica. Por la solidez doble‑negada no se puede: de `Prov(⌜φ⌝)`
leído por `gg` sólo sale `¬¬ ∃p …`, y quitar esa doble negación es el principio de Markov. Hace falta el TESTIGO.

* **§1 · D1 en ℕ, con el testigo** (`proofN_of_prf`): si `Prf φ`, hay `m` con `ProofN m ⌜φ⌝`. El `m` es el de `posNum`
  (el código de la prueba); `proofN_decide` (Rosser, NegNum) decide `ProofN m ⌜φ⌝` o refuta `PfF m̄ ⌜φ⌝` en `Prf`, y
  la refutación choca, en `MNV V₀` y leída por `gg`, con `posNum`. Sin el modelo en el enunciado.
* **§2 · `modelo_prov_iff`**, la vuelta: el testigo, en `MNV V₀`, es una cadena que el modelo cree, porque `chainOk`
  ES `chainOkN` en él. Conserva su nombre (`SolidezVerificador`); vive aquí porque `posNum` y `proofN_decide` van
  después de aquel módulo.
* **§3 · La vuelta de la rigidez en un `M` estándar cualquiera** (`M_lineWF_de`, `M_premsOf_de`, `M_cadena_de`): si `p`
  es una cadena de verdad, `M` la cree. Es la gemela de `M_lineWF` y `M_cadena` (`Meta/RigidezEstandar.lean`),
  etiqueta por etiqueta, con el otro sentido de los axiomas `ax_lineWF_*` y los `ax_premsOf_*`.
* **§4 · `modelo_prov_iff_de`**, la vuelta en todo modelo estándar: el testigo de §1 y §3. Conserva su nombre
  (`RigidezEstandar`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL FOL.Metamath.Semantics ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.ModeloEstandar
open ROBINSON_PlusPlus.Meta.SolidezDobleNegacion
open ROBINSON_PlusPlus.Meta.RosserW1 ROBINSON_PlusPlus.Meta.RosserPosNum ROBINSON_PlusPlus.Meta.RosserNegNum

namespace ROBINSON_PlusPlus.Meta.ProvFiel

/-! ## §1 · D1 en ℕ, con el testigo -/

/-- `PfF y x`, leído por `gg`, sólo mira el VALOR de `x`. -/
theorem gg_PfF_congr {M : Model Nat} (v : Nat → Nat) {y x x' : Term} (h : evalTerm M v x = evalTerm M v x') :
    evalFormula M v (gg (PfF y x)) ↔ evalFormula M v (gg (PfF y x')) := by
  simp only [PfF, land, In, chainOk, gg, neg, evalFormula, evalTerms, h]

/-- 🏁 **D1 en ℕ, con el testigo**: todo teorema tiene una cadena de verdad. `posNum` da `Prf (PfF m̄ ⌜φ⌝)`;
    `proofN_decide` da `ProofN m ⌜φ⌝` o `Prf ¬PfF m̄ ⌜φ⌝`, y lo segundo, leído por `gg` en `MNV V₀`, choca con lo
    primero. Sin lógica clásica. -/
theorem proofN_of_prf {φ : Formula} (h : Prf φ) : ∃ m, ProofN m (codeNat φ) := by
  obtain ⟨m, hm⟩ := posNum h
  rcases proofN_decide m (codeNat φ) with hp | hn
  · exact ⟨m, hp⟩
  · exact absurd ((gg_PfF_congr (M := MNV ROBINSON_PlusPlus.Meta.ModeloCodigo.V₀) (fun _ => 0)
      (by rw [← ROBINSON_PlusPlus.Meta.Representability.formCodeM_eq, ev_formCodeM, ev_numeralM])).mp
        (prf_sound_dn ROBINSON_PlusPlus.Meta.Consistencia.estandarDN_MN hm (fun _ => 0)))
      (prf_sound_dn ROBINSON_PlusPlus.Meta.Consistencia.estandarDN_MN hn (fun _ => 0))

end ROBINSON_PlusPlus.Meta.ProvFiel

/-! ## §2 · `modelo_prov_iff`, la vuelta en `MNV V₀` -/

namespace ROBINSON_PlusPlus.Meta.SolidezVerificador

/-- Lo que un testigo de verdad da en `MNV V₀`: `Prov(⌜φ⌝)`. -/
theorem prov_de_proofN {φ : Formula} {m : Nat} (h : ProofN m (codeNat φ)) (v : Nat → Nat) :
    evalFormula (MNV ROBINSON_PlusPlus.Meta.ModeloCodigo.V₀) v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) := by
  rw [ROBINSON_PlusPlus.Meta.ProofChain.provCodeC', eval_substFormula_zero,
    ← ROBINSON_PlusPlus.Meta.Representability.formCodeM_eq, ev_formCodeM]
  simp only [ROBINSON_PlusPlus.Meta.ProofChain.provFormulaC', land, chainOk, In, runFn, nil, zero,
    in_sym, zero_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MN_chainOk, MN_mem, MN_runFn, MN_zero]
  refine ⟨m, ?_, h.2⟩
  rw [ROBINSON_PlusPlus.Meta.Consistencia.V₀_eq_codigo]
  exact h.1

/-- 🏁 **`Prov` es FIEL en `MNV V₀`**, el modelo estándar construido: `MNV V₀ ⊨ Prov(⌜φ⌝)` exactamente cuando `φ` es
    teorema (en TODO modelo estándar: `modelo_prov_iff_de`). La ida es W1 (`prf_of_prov`); la vuelta, desde ADR‑191, el
    testigo de `proofN_of_prf`: sin lógica clásica. Es también el control de vacuidad de W1: su hipótesis se cumple para
    cada teorema. (Hasta ADR‑191 vivía en `Meta/SolidezVerificador.lean`, y su vuelta era D1 leído por `prf_sound`.) -/
theorem modelo_prov_iff (φ : Formula) (v : Nat → Nat) :
    evalFormula (MNV ROBINSON_PlusPlus.Meta.ModeloCodigo.V₀) v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) ↔
      Prf φ :=
  ⟨prf_of_prov φ v, fun h => by
    obtain ⟨m, hm⟩ := ROBINSON_PlusPlus.Meta.ProvFiel.proofN_of_prf h
    exact prov_de_proofN hm v⟩

end ROBINSON_PlusPlus.Meta.SolidezVerificador

#print axioms ROBINSON_PlusPlus.Meta.ProvFiel.proofN_of_prf
#print axioms ROBINSON_PlusPlus.Meta.SolidezVerificador.modelo_prov_iff

/-! ## §3 · La vuelta de la rigidez: si `p` es una cadena de verdad, un `M` estándar cualquiera la cree -/

section Vuelta
open ROBINSON_PlusPlus.Meta.SolidezPrf ROBINSON_PlusPlus.Meta.RigidezEstandar
open ROBINSON_PlusPlus.Meta.RosserNumEval (codT_of_hasWitN codF_of_hasWitFN codF_liftfcN codT_codeNatTerm)

namespace ROBINSON_PlusPlus.Meta.ProvFiel

variable {M : Model Nat}

set_option hygiene false in
/-- La vuelta de `lw3`/`lw4`/`lw5`: con la RHS de `lineWFT` en la mano, `M` cree la línea. -/
macro "wl_abre " ax:ident : tactic => `(tactic| (
  abre_lw $ax
  have hx : ¬ x = 0 := by intro e; subst e; simp [lenN_zero] at hlen
  have htag : M.func sym!"nthc" [x, 1] = nthN x 1 := M_nthc hM 1 x (by omega)
  rw [hk] at htag))

set_option hygiene false in
macro "wl3 " ax:ident : tactic => `(tactic| (
  obtain ⟨hlen, hr⟩ := hT
  wl_abre $ax
  refine (h htag).2 hlen ?_
  rw [M_carc' hM hx, M_nthc hM 2 x (by omega)]
  exact hr))

set_option hygiene false in
macro "wl4 " ax:ident : tactic => `(tactic| (
  obtain ⟨hlen, hr⟩ := hT
  wl_abre $ax
  refine (h htag).2 hlen ?_
  rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_nthc hM 3 x (by omega)]
  exact hr))

set_option hygiene false in
macro "wl5 " ax:ident : tactic => `(tactic| (
  obtain ⟨hlen, hr⟩ := hT
  wl_abre $ax
  refine (h htag).2 hlen ?_
  rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_nthc hM 3 x (by omega), M_nthc hM 4 x (by omega)]
  exact hr))

local notation "Vm" => M.func sym!"axiomsCodeT" []

theorem wl_0 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 0) (hT : lineWFT Vm 0 x) :
    M.rel sym!"lineWF" [x] := by wl4 ax_lineWF_p1
theorem wl_1 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 1) (hT : lineWFT Vm 1 x) :
    M.rel sym!"lineWF" [x] := by wl5 ax_lineWF_p2
theorem wl_2 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 2) (hT : lineWFT Vm 2 x) :
    M.rel sym!"lineWF" [x] := by wl4 ax_lineWF_c1
theorem wl_3 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 3) (hT : lineWFT Vm 3 x) :
    M.rel sym!"lineWF" [x] := by wl4 ax_lineWF_c2
theorem wl_4 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 4) (hT : lineWFT Vm 4 x) :
    M.rel sym!"lineWF" [x] := by wl4 ax_lineWF_c3
theorem wl_5 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 5) (hT : lineWFT Vm 5 x) :
    M.rel sym!"lineWF" [x] := by wl4 ax_lineWF_j1
theorem wl_6 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 6) (hT : lineWFT Vm 6 x) :
    M.rel sym!"lineWF" [x] := by wl4 ax_lineWF_j2
theorem wl_7 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 7) (hT : lineWFT Vm 7 x) :
    M.rel sym!"lineWF" [x] := by wl5 ax_lineWF_j3
theorem wl_8 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 8) (hT : lineWFT Vm 8 x) :
    M.rel sym!"lineWF" [x] := by wl3 ax_lineWF_efq
theorem wl_9 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 9) (hT : lineWFT Vm 9 x) :
    M.rel sym!"lineWF" [x] := by
  obtain ⟨hlen, hA, ht, hc⟩ := hT
  wl_abre ax_lineWF_q1
  refine (h htag).2 hlen ?_ ?_ ?_
  · rw [M_nthc hM 2 x (by omega)]; exact hA
  · rw [M_nthc hM 3 x (by omega)]; exact ht
  · rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_nthc hM 3 x (by omega),
      M_substfc hM (codF_of_hasWitFN hA) 0 _ (codT_of_hasWitN ht)]
    exact hc
theorem wl_10 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 10) (hT : lineWFT Vm 10 x) :
    M.rel sym!"lineWF" [x] := by
  obtain ⟨hlen, hA, ht, hc⟩ := hT
  wl_abre ax_lineWF_q2
  refine (h htag).2 hlen ?_ ?_ ?_
  · rw [M_nthc hM 2 x (by omega)]; exact hA
  · rw [M_nthc hM 3 x (by omega)]; exact ht
  · rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_nthc hM 3 x (by omega),
      M_substfc hM (codF_of_hasWitFN hA) 0 _ (codT_of_hasWitN ht)]
    exact hc
theorem wl_11 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 11) (hT : lineWFT Vm 11 x) :
    M.rel sym!"lineWF" [x] := by
  obtain ⟨hlen, hB, hc⟩ := hT
  wl_abre ax_lineWF_q3
  refine (h htag).2 hlen ?_ ?_
  · rw [M_nthc hM 3 x (by omega)]; exact hB
  · rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_nthc hM 3 x (by omega),
      M_liftfc hM (codF_of_hasWitFN hB) 0]
    exact hc
theorem wl_12 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 12) (hT : lineWFT Vm 12 x) :
    M.rel sym!"lineWF" [x] := by wl3 ax_lineWF_eqrefl
theorem wl_13 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 13) (hT : lineWFT Vm 13 x) :
    M.rel sym!"lineWF" [x] := by
  obtain ⟨hlen, hA, ht, hu, hc⟩ := hT
  wl_abre ax_lineWF_leibniz
  refine (h htag).2 hlen ?_ ?_ ?_ ?_
  · rw [M_nthc hM 2 x (by omega)]; exact hA
  · rw [M_nthc hM 3 x (by omega)]; exact ht
  · rw [M_nthc hM 4 x (by omega)]; exact hu
  · rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_nthc hM 3 x (by omega), M_nthc hM 4 x (by omega),
      M_substfc hM (codF_of_hasWitFN hA) 0 _ (codT_of_hasWitN ht),
      M_substfc hM (codF_of_hasWitFN hA) 0 _ (codT_of_hasWitN hu)]
    exact hc
theorem wl_14 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 14) (hT : lineWFT Vm 14 x) :
    M.rel sym!"lineWF" [x] := by wl3 ax_lineWF_p3
theorem wl_15 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 15) (hT : lineWFT Vm 15 x) :
    M.rel sym!"lineWF" [x] := by
  obtain ⟨hlen, hr⟩ := hT
  wl_abre ax_lineWF_thy
  refine (h htag).2 hlen ?_
  rw [M_carc' hM hx]
  exact hr
theorem wl_16 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 16) (hT : lineWFT Vm 16 x) :
    M.rel sym!"lineWF" [x] := by
  have hlen : lenN x = 3 := hT
  wl_abre ax_lineWF_mp
  exact (h htag).2 hlen
theorem wl_17 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 17) (hT : lineWFT Vm 17 x) :
    M.rel sym!"lineWF" [x] := by wl3 ax_lineWF_gen
theorem wl_18 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 18) (hT : lineWFT Vm 18 x) :
    M.rel sym!"lineWF" [x] := by
  obtain ⟨hlen, hA, hc⟩ := hT
  wl_abre ax_lineWF_ind
  have hA' := codF_of_hasWitFN hA
  refine (h htag).2 hlen ?_ ?_
  · rw [M_nthc hM 2 x (by omega)]; exact hA
  · rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_liftfc hM hA' 1,
      M_substfc hM (codF_liftfcN hA' 1) 0 _ (codT_codeNatTerm _),
      M_substfc hM hA' 0 _ (codT_codeNatTerm _)]
    exact hc
theorem wl_19 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 19) (hT : lineWFT Vm 19 x) :
    M.rel sym!"lineWF" [x] := by
  obtain ⟨hlen, hA, hc⟩ := hT
  wl_abre ax_lineWF_qconf
  refine (h htag).2 hlen ?_ ?_
  · rw [M_nthc hM 2 x (by omega)]; exact hA
  · rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_nthc hM 3 x (by omega),
      M_liftfc hM (codF_of_hasWitFN hA) 0]
    exact hc
theorem wl_20 (hM : Estandar M) (x : Nat) (hk : nthN x 1 = 20) (hT : lineWFT Vm 20 x) :
    M.rel sym!"lineWF" [x] := by
  obtain ⟨hlen, hA, hc⟩ := hT
  wl_abre ax_lineWF_listInd
  have hA' := codF_of_hasWitFN hA
  refine (h htag).2 hlen ?_ ?_
  · rw [M_nthc hM 2 x (by omega)]; exact hA
  · rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_liftfc hM hA' 1, M_liftfc hM (codF_liftfcN hA' 1) 2,
      M_substfc hM (codF_liftfcN (codF_liftfcN hA' 1) 2) 0 _ (codT_codeNatTerm _),
      M_substfc hM hA' 0 _ (codT_codeNatTerm _)]
    exact hc

/-- 🏁 **Si `x` es una línea bien formada de verdad, `M` lo cree** (con el `V` de `M`): la vuelta de `M_lineWF`. -/
theorem M_lineWF_de (hM : Estandar M) (x : Nat) (hw : lineWFN Vm x) : M.rel sym!"lineWF" [x] := by
  obtain ⟨hK, hT⟩ := hw
  match hk : nthN x 1, hK, hT with
  | 0, _, hT => exact wl_0 hM x hk hT
  | 1, _, hT => exact wl_1 hM x hk hT
  | 2, _, hT => exact wl_2 hM x hk hT
  | 3, _, hT => exact wl_3 hM x hk hT
  | 4, _, hT => exact wl_4 hM x hk hT
  | 5, _, hT => exact wl_5 hM x hk hT
  | 6, _, hT => exact wl_6 hM x hk hT
  | 7, _, hT => exact wl_7 hM x hk hT
  | 8, _, hT => exact wl_8 hM x hk hT
  | 9, _, hT => exact wl_9 hM x hk hT
  | 10, _, hT => exact wl_10 hM x hk hT
  | 11, _, hT => exact wl_11 hM x hk hT
  | 12, _, hT => exact wl_12 hM x hk hT
  | 13, _, hT => exact wl_13 hM x hk hT
  | 14, _, hT => exact wl_14 hM x hk hT
  | 15, _, hT => exact wl_15 hM x hk hT
  | 16, _, hT => exact wl_16 hM x hk hT
  | 17, _, hT => exact wl_17 hM x hk hT
  | 18, _, hT => exact wl_18 hM x hk hT
  | 19, _, hT => exact wl_19 hM x hk hT
  | 20, _, hT => exact wl_20 hM x hk hT
  | k + 21, hK, _ => exact absurd hK (by omega)

/-! ### Las premisas: `premsOf` de `M` es el de verdad en una línea bien formada

Las 21 etiquetas tienen su `ax_premsOf_*`, cada uno para la forma exacta de su línea; la longitud la da `lineWFT`. -/

-- (Sin `omega`: aquí su prueba por contradicción traía `Classical.choice`, ADR‑189.)
theorem consN_len {x n : Nat} (h : lenN x = n + 1) : ∃ a r, And (x = consN a r) (lenN r = n) := by
  have hx : ¬ x = 0 := by intro e; subst e; rw [lenN_zero] at h; exact Nat.noConfusion h
  obtain ⟨a, r, rfl, _⟩ := consN_de hx
  rw [lenN_consN] at h
  exact ⟨a, r, rfl, Nat.succ.inj h⟩

theorem len_cero {x : Nat} (h : lenN x = 0) : x = 0 := by
  rcases Nat.eq_zero_or_pos x with e | hpos
  · exact e
  · obtain ⟨d, s, rfl, _⟩ := consN_de (Nat.pos_iff_ne_zero.mp hpos); rw [lenN_consN] at h; omega

set_option hygiene false in
/-- Abre en `M` el `ax_premsOf_*` de una etiqueta. -/
macro "abre_pr " ax:ident : tactic => `(tactic| (
  have hp := ax_de hM (φ := $ax) (by simp [axioms]) (fun _ => 0)
  simp [$ax:ident, forall_, forall_2, forall_3, forall_4, premsOf, implc, cons, nil, zero, succ, evalFormula,
    evalTerm, evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc, M_numeral hM] at hp))

set_option hygiene false in
macro "pr2 " ax:ident : tactic => `(tactic| (
  obtain ⟨a, r1, rfl, h1⟩ := consN_len hlen
  obtain ⟨b, r2, rfl, h2⟩ := consN_len h1
  rw [len_cero h2] at hk ⊢
  simp only [nthN_cs, nthN_cz] at hk
  subst hk
  abre_pr $ax
  rw [hp a]
  simp [premsOfN, nthN_cs, nthN_cz]))

set_option hygiene false in
macro "pr3 " ax:ident : tactic => `(tactic| (
  obtain ⟨a, r1, rfl, h1⟩ := consN_len hlen
  obtain ⟨b, r2, rfl, h2⟩ := consN_len h1
  obtain ⟨c, r3, rfl, h3⟩ := consN_len h2
  rw [len_cero h3] at hk ⊢
  simp only [nthN_cs, nthN_cz] at hk
  subst hk
  abre_pr $ax
  rw [hp a c]
  simp [premsOfN, nthN_cs, nthN_cz, implcN]))

set_option hygiene false in
macro "pr4 " ax:ident : tactic => `(tactic| (
  obtain ⟨a, r1, rfl, h1⟩ := consN_len hlen
  obtain ⟨b, r2, rfl, h2⟩ := consN_len h1
  obtain ⟨c, r3, rfl, h3⟩ := consN_len h2
  obtain ⟨d, r4, rfl, h4⟩ := consN_len h3
  rw [len_cero h4] at hk ⊢
  simp only [nthN_cs, nthN_cz] at hk
  subst hk
  abre_pr $ax
  rw [hp a c d]
  simp [premsOfN, nthN_cs, nthN_cz]))

set_option hygiene false in
macro "pr5 " ax:ident : tactic => `(tactic| (
  obtain ⟨a, r1, rfl, h1⟩ := consN_len hlen
  obtain ⟨b, r2, rfl, h2⟩ := consN_len h1
  obtain ⟨c, r3, rfl, h3⟩ := consN_len h2
  obtain ⟨d, r4, rfl, h4⟩ := consN_len h3
  obtain ⟨e, r5, rfl, h5⟩ := consN_len h4
  rw [len_cero h5] at hk ⊢
  simp only [nthN_cs, nthN_cz] at hk
  subst hk
  abre_pr $ax
  rw [hp a c d e]
  simp [premsOfN, nthN_cs, nthN_cz]))

/-- 🏁 **`premsOf` de `M` es el de verdad en una línea bien formada.** -/
theorem M_premsOf_de (hM : Estandar M) (x : Nat) (hw : lineWFN Vm x) :
    M.func sym!"premsOf" [x] = premsOfN x := by
  obtain ⟨hK, hT⟩ := hw
  match hk : nthN x 1, hK, hT with
  | 0, _, hT => have hlen : lenN x = 4 := hT.1; pr4 ax_premsOf_p1
  | 1, _, hT => have hlen : lenN x = 5 := hT.1; pr5 ax_premsOf_p2
  | 2, _, hT => have hlen : lenN x = 4 := hT.1; pr4 ax_premsOf_c1
  | 3, _, hT => have hlen : lenN x = 4 := hT.1; pr4 ax_premsOf_c2
  | 4, _, hT => have hlen : lenN x = 4 := hT.1; pr4 ax_premsOf_c3
  | 5, _, hT => have hlen : lenN x = 4 := hT.1; pr4 ax_premsOf_j1
  | 6, _, hT => have hlen : lenN x = 4 := hT.1; pr4 ax_premsOf_j2
  | 7, _, hT => have hlen : lenN x = 5 := hT.1; pr5 ax_premsOf_j3
  | 8, _, hT => have hlen : lenN x = 3 := hT.1; pr3 ax_premsOf_efq
  | 9, _, hT => have hlen : lenN x = 4 := hT.1; pr4 ax_premsOf_q1
  | 10, _, hT => have hlen : lenN x = 4 := hT.1; pr4 ax_premsOf_q2
  | 11, _, hT => have hlen : lenN x = 4 := hT.1; pr4 ax_premsOf_q3
  | 12, _, hT => have hlen : lenN x = 3 := hT.1; pr3 ax_premsOf_eqrefl
  | 13, _, hT => have hlen : lenN x = 5 := hT.1; pr5 ax_premsOf_leibniz
  | 14, _, hT => have hlen : lenN x = 3 := hT.1; pr3 ax_premsOf_p3
  | 15, _, hT => have hlen : lenN x = 2 := hT.1; pr2 ax_premsOf_thy
  | 16, _, hT => have hlen : lenN x = 3 := hT; pr3 ax_premsOf_mp
  | 17, _, hT => have hlen : lenN x = 3 := hT.1; pr3 ax_premsOf_gen
  | 18, _, hT => have hlen : lenN x = 3 := hT.1; pr3 ax_premsOf_ind
  | 19, _, hT => have hlen : lenN x = 4 := hT.1; pr4 ax_premsOf_qconf
  | 20, _, hT => have hlen : lenN x = 3 := hT.1; pr3 ax_premsOf_listInd
  | k + 21, hK, _ => exact absurd hK (by omega)

set_option linter.unusedSimpArgs false in
/-- 🏁 **Si `p` es una cadena válida de verdad desde `c`, `M` la cree**: la vuelta de `M_cadena`. -/
theorem M_cadena_de (hM : Estandar M) : ∀ (p c : Nat), chainOkN Vm c p → M.rel sym!"chainOk" [c, p] := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro c hc
    by_cases hp : p = 0
    · subst hp
      have h := ax_de hM (φ := ax_chainOk_nil) (by simp [axioms]) (fun _ => 0) c
      simpa [ax_chainOk_nil, forall_, chainOk, nil, zero, evalFormula, evalTerm, evalTerms, shiftEnv, hM.hzero]
        using h
    · obtain ⟨l, r, rfl, hr⟩ := consN_de hp
      have h := ax_de hM (φ := ax_chainOk_cons) (by simp [axioms]) (fun _ => 0) c l r
      simp [ax_chainOk_cons, forall_3, _root_.iff, chainOk, lineOk, lineWF, allIn, premsOf, land, concat, carc,
        cons, nil, zero, evalFormula, evalTerm, evalTerms, shiftEnv, hM.hcons, hM.hzero] at h
      obtain ⟨⟨hlw, hal⟩, hrest⟩ := (chainOkN_consN _ c l r).1 hc
      have hl0 : ¬ l = 0 := by
        intro e; subst e
        have := hlw.1; have h2 := hlw.2
        rw [nthN_zero_l] at h2 this
        simp [lineWFT, lenN_zero] at h2
      refine h.2 (M_lineWF_de hM l hlw) ?_ ?_
      · rw [M_premsOf_de hM l hlw, M_allIn hM]; exact hal
      · rw [M_carc' hM hl0, M_concat hM]; exact ih r hr _ hrest

end ROBINSON_PlusPlus.Meta.ProvFiel

/-! ## §4 · `modelo_prov_iff_de`, la vuelta en todo modelo estándar -/

namespace ROBINSON_PlusPlus.Meta.RigidezEstandar

variable {M : Model Nat}

/-- 🏁 **`Prov` es FIEL en todo modelo estándar.** La ida, `prf_of_prov_de` (W1 en `M`); la vuelta, desde ADR‑191, el
    testigo de `proofN_of_prf`, que `M` cree (`M_cadena_de`): sin lógica clásica. (Hasta ADR‑191 vivía en
    `Meta/RigidezEstandar.lean`, y su vuelta era D1 leído por `prf_sound`.) -/
theorem modelo_prov_iff_de (hM : Estandar M) (φ : Formula) (v : Nat → Nat) :
    evalFormula M v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) ↔ Prf φ := by
  refine ⟨prf_of_prov_de hM φ v, fun h => ?_⟩
  obtain ⟨m, hc, hy⟩ := ROBINSON_PlusPlus.Meta.ProvFiel.proofN_of_prf h
  have hc' : chainOkN (M.func sym!"axiomsCodeT" []) 0 m := by rw [M_axiomsCodeT hM]; exact hc
  have hch := ROBINSON_PlusPlus.Meta.ProvFiel.M_cadena_de hM m 0 hc'
  have hrun := (M_cadena hM m 0 hch).2
  rw [ROBINSON_PlusPlus.Meta.ProofChain.provCodeC', eval_substFormula_zero,
    ← ROBINSON_PlusPlus.Meta.Representability.formCodeM_eq, M_formCodeM hM]
  simp only [ROBINSON_PlusPlus.Meta.ProofChain.provFormulaC', land, chainOk, In, runFn, nil, zero,
    evalFormula, evalTerm, evalTerms, shiftEnv, hM.hzero, M_mem hM]
  exact ⟨m, hch, by rw [hrun]; exact hy⟩

end ROBINSON_PlusPlus.Meta.RigidezEstandar

end Vuelta

#print axioms ROBINSON_PlusPlus.Meta.ProvFiel.M_cadena_de
#print axioms ROBINSON_PlusPlus.Meta.RigidezEstandar.modelo_prov_iff_de
