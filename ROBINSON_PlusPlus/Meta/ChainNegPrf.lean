/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.VerifierSound
import ROBINSON_PlusPlus.Meta.D3BodyPrf
import ROBINSON_PlusPlus.Meta.LineWFCases
import ROBINSON_PlusPlus.Meta.AxiomListCode
import ROBINSON_PlusPlus.Meta.Sigma1CorePrf
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.ChainDecode
import ROBINSON_PlusPlus.Full.Lists

/-!
# MÓDULOS C/D de `NegVerifier` — **`DEUDA_inNeg` SALDADA**, y el puente de `DEUDA_chainNeg`

`Meta/VerifierSound.lean` dejó `NegVerifier` reducido a **dos** obligaciones enunciadas. Aquí se
**paga una** y se construye el **núcleo reutilizable** de la otra.

## §1 · El PUENTE: de una línea refutada a la cadena refutada

    derives_chainOk_neg_of_line (l k x) (hk : l[k]? = some x)
      (hne : axioms ⊢ ¬ lineWF x) : axioms ⊢ ¬ chainOk nil ⟦l⟧

Es la mitad **reutilizable** de `DEUDA_chainNeg`, y sale de piezas que ya estaban:
`prf_lineWF_of_chainOk` (la que D3 usó en su mitad (a)), `prf_nthc_objList`, `prf_lenc_objList` y
`gnum_lt`. ⇒ **`DEUDA_chainNeg` queda reducida a**: *«el decodificador META rechaza ⟹ hay una línea
cuyo `lineWF` la teoría refuta»*.

## §2 · Las CABEZAS de una cadena aceptada SON los códigos de sus conclusiones

    decode_heads (l acc rs L) : decodeChainAux acc ⟦l⟧ = some rs → checkAux rs acc = some L →
      ∃ fs, L = acc ++ fs ∧ Prf (⟦l.map carc⟧ ≐ listFormCodeM fs)

🔑 **La pieza que lo hace posible es `decodeForm_inj`** —el decodificador es una **sección**—:
si `decodeLine` acepta, la cabeza del término **era** `formCodeM f`. Se extrae en dos lemas
(`decodeLine_stepConcl`, `decodeLine_carc`) y la inducción sobre la cadena hace el resto.

## §3 · 🏁 `DEUDA_inNeg`, SALDADA

    deuda_inNeg : DEUDA_inNeg

La cadena entera: `runFn nil ⟦l⟧ ≐ ⟦l.map carc⟧` (`prf_runFn_objList` + `prf_concat_nil_eq`)
`≐ listFormCodeM fs` (§2), y ahí manda **`prf_not_In_listFormCodeM`**, que ya existía y cuyo
docstring decía exactamente *«la refutación que necesita `NegVerifier`»*.

⚠️ **Nada de esto usa el ancla de codificación**: el footprint no cita `prf_axiomsCodeT_eq` ni
`ax_axiomsCodeT_eq`.

## ⬜ Lo que queda de `DEUDA_chainNeg`, medido

Con `StdChain` estrechada ([ADR‑022](../../DECISIONS.md)) toda línea es `⟨⌜f⌝, k̄, args⟩` con args
`formCode`/`termCode`, así que **las causas de rechazo del decodificador son cinco, y se pueden
enumerar**:

| # | por qué rechaza | ¿hay maquinaria? |
|---|---|---|
| (a) | **tag fuera de rango** (`k ≥ 21`) | 🔶 `prf_tagDisj_absurd` acota el tag por 20 |
| (b) | **aridad equivocada** | 🔶 los 21 `ax_lineWF_*` llevan `lenc = n̄`; es `gnum_ne` |
| (c) | **la conclusión no casa** (`stepConcl ≠ f`) | ✅ **`derives_lineWF_neg_of_tag`** + `formCode_ne` — es el grueso, y está |
| (d) | **`thy` con `f ∉ axioms`** | ✅ `derives_lineWF_neg_thy_of_not_prf` |
| (e) | **`mp`/`gen` sin premisas en el acumulador** | ⛔ **la única sin maquinaria**: no va por `lineWF` sino por el conjunto `premsOf ⊆ conclusiones anteriores` de `chainOk` |

⇒ **(a)–(d) componen con §1 y cierran**; **(e) es el trabajo que queda**, y es exactamente la
mitad de `chainOk` que D3 tuvo que aritmetizar (`boundedPremsIn`).
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.CodeArith
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.D3BodyPrf
open ROBINSON_PlusPlus.Meta.LineWFCases
open ROBINSON_PlusPlus.Meta.VerifierSound
open ROBINSON_PlusPlus.Meta.CodeDecode
open ROBINSON_PlusPlus.Meta.ChainDecode
open ROBINSON_PlusPlus.Meta.HilbertSeq
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.AxiomListCode

namespace ROBINSON_PlusPlus.Meta.ChainNegPrf

/-! ## §0 · Los dos Leibniz a nivel `⊢` que hacen falta (molde de `Full.eq_subst_in`) -/

theorem derives_lt_congr_right {Γ : List Formula} {a t₁ t₂ : Term}
    (h : Γ ⊢ (t₁ =eq t₂)) (hp : Γ ⊢ lt a t₁) : Γ ⊢ lt a t₂ := by
  let f : Formula := lt (liftTerm 0 a) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = lt a s := by
    intro s
    simp only [f, substFormula, lt, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ Derives.subst Γ t₁ t₂ f h ((hS t₁) ▸ hp)

theorem derives_lineWF_congr {Γ : List Formula} {t₁ t₂ : Term}
    (h : Γ ⊢ (t₁ =eq t₂)) (hp : Γ ⊢ lineWF t₁) : Γ ⊢ lineWF t₂ := by
  let f : Formula := lineWF (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = lineWF s := by
    intro s
    simp only [f, substFormula, lineWF, substTerm, substTerms, if_true]
  exact (hS t₂) ▸ Derives.subst Γ t₁ t₂ f h ((hS t₁) ▸ hp)

/-! ## §1 · EL PUENTE: de una línea refutada a la cadena refutada -/

theorem derives_chainOk_neg_of_line (l : List Term) (k : Nat) (x : Term)
    (hk : l[k]? = some x) (hne : axioms ⊢ neg (lineWF x)) :
    axioms ⊢ neg (chainOk nil (objList l)) := by
  refine FOL.MetaRules.raa (fun hch => ?_)
  -- (1) la cota: k < longitud
  have hklt : k < l.length := by
    rcases List.getElem?_eq_some_iff.mp hk with ⟨hb, _⟩
    exact hb
  have hlt0 : axioms ⊢ lt (numeralM k) (numeralM l.length) := by
    have := gnum_lt (a := k) (b := l.length) hklt
    simpa only [numeralM_eq] using this
  -- (2) transportar la cota a `lenc ⟦l⟧`
  have hlen : axioms ⊢ (lenc (objList l) =eq numeralM l.length) :=
    prf_to_derives (SinWTs.prf_lenc_objList l)
  have hlt : axioms ⊢ lt (numeralM k) (lenc (objList l)) :=
    derives_lt_congr_right (FOL.derive_eq_symm hlen) hlt0
  -- (3) chainOk ⇒ lineWF (nthc ⟦l⟧ k̄)
  have hwf : axioms ⊢ lineWF (nthc (objList l) (numeralM k)) :=
    FOL.MetaRules.mp
      (FOL.MetaRules.mp (prf_to_derives (prf_lineWF_of_chainOk (objList l) (numeralM k))) hch)
      hlt
  -- (4) `nthc ⟦l⟧ k̄ = x` ⇒ lineWF x
  have hnth : axioms ⊢ (nthc (objList l) (numeralM k) =eq x) :=
    prf_to_derives (SinWTs.prf_nthc_objList l k x hk)
  have hwfx : axioms ⊢ lineWF x := derives_lineWF_congr hnth hwf
  exact FOL.MetaRules.mp hne hwfx


/-! ## §2 · `DEUDA_inNeg`: las CABEZAS de una cadena aceptada SON los códigos de sus conclusiones -/

/-- Lo que `decodeLine` garantiza, extraído: la regla CONCLUYE la cabeza. -/
theorem decodeLine_stepConcl {acc : List Formula} {line : Term} {f : Formula} {r : Rule}
    (h : decodeLine acc line = some (f, r)) : stepConcl acc r = some f := by
  cases line with
  | var n => simp [decodeLine] at h
  | func cs args =>
      cases args with
      | nil => simp [decodeLine] at h
      | cons a as =>
          cases as with
          | nil => simp [decodeLine] at h
          | cons b bs =>
              cases bs with
              | cons _ _ => simp [decodeLine] at h
              | nil =>
                  simp only [decodeLine] at h
                  split at h
                  · rcases hf : decodeForm a with _ | f'
                    · rw [hf] at h; simp at h
                    · rw [hf] at h; simp only [Option.bind] at h
                      rcases hr : decodeRule acc f' b with _ | r'
                      · rw [hr] at h; simp at h
                      · rw [hr] at h; simp only [Option.bind] at h
                        split at h
                        · simp only [Option.some.injEq, Prod.mk.injEq] at h
                          obtain ⟨h1, h2⟩ := h; subst h1; subst h2; assumption
                        · simp at h
                  · simp at h

/-- Y la otra mitad: la CABEZA del término es el código de la fórmula decodificada. -/
theorem decodeLine_carc {acc : List Formula} {line : Term} {f : Formula} {r : Rule}
    (h : decodeLine acc line = some (f, r)) : Prf (carc line =eq formCodeM f) := by
  cases line with
  | var n => simp [decodeLine] at h
  | func cs args =>
      cases args with
      | nil => simp [decodeLine] at h
      | cons a as =>
          cases as with
          | nil => simp [decodeLine] at h
          | cons b bs =>
              cases bs with
              | cons _ _ => simp [decodeLine] at h
              | nil =>
                  simp only [decodeLine] at h
                  split at h
                  · next hcs =>
                      rcases hf : decodeForm a with _ | f'
                      · rw [hf] at h; simp at h
                      · rw [hf] at h; simp only [Option.bind] at h
                        rcases hr : decodeRule acc f' b with _ | r'
                        · rw [hr] at h; simp at h
                        · rw [hr] at h; simp only [Option.bind] at h
                          split at h
                          · simp only [Option.some.injEq, Prod.mk.injEq] at h
                            obtain ⟨h1, _⟩ := h
                            have ha : a = formCodeM f' := decodeForm_inj hf
                            have hsym : cs = cons_sym := by simpa using hcs
                            subst hsym; subst ha; rw [← h1]
                            exact prf_carc_cons _ b
                          · simp at h
                  · simp at h

theorem decode_heads : ∀ (l : List Term) (acc : List Formula) (rs : List Rule) (L : List Formula),
    decodeChainAux acc (objList l) = some rs → checkAux rs acc = some L →
    ∃ fs : List Formula, And (L = acc ++ fs)
      (Prf (objList (l.map carc) =eq listFormCodeM fs))
  | [], acc, rs, L, hd, hc => by
      simp only [objList, nil, zero, decodeChainAux, beq_self_eq_true, if_true,
        Option.some.injEq] at hd
      subst hd
      simp only [checkAux, Option.some.injEq] at hc
      subst hc
      exact ⟨[], by simp, by simpa [objList, listFormCodeM] using prf_refl nil⟩
  | line :: rest, acc, rs, L, hd, hc => by
      simp only [objList, cons, decodeChainAux, beq_self_eq_true, if_true] at hd
      rcases hdl : decodeLine acc line with _ | fr
      · rw [hdl] at hd; simp at hd
      · rw [hdl] at hd
        simp only [Option.bind] at hd
        rcases hrec : decodeChainAux (acc ++ [fr.1]) (objList rest) with _ | rs'
        · rw [hrec] at hd; simp at hd
        · rw [hrec] at hd
          simp only [Option.map, Option.some.injEq] at hd
          subst hd
          -- `stepConcl acc fr.2 = some fr.1` viene de `decodeLine`
          have hstep : stepConcl acc fr.2 = some fr.1 := decodeLine_stepConcl hdl
          simp only [checkAux, hstep] at hc
          obtain ⟨fs, hL, heq⟩ := decode_heads rest (acc ++ [fr.1]) rs' L hrec hc
          refine ⟨fr.1 :: fs, by simpa using hL, ?_⟩
          -- la CABEZA: `carc line = formCodeM fr.1`
          have hcarc : Prf (carc line =eq formCodeM fr.1) := decodeLine_carc hdl
          show Prf (cons (carc line) (objList (rest.map carc))
                      =eq cons (formCodeM fr.1) (listFormCodeM fs))
          exact prf_eq_trans (prf_congr_cons_head hcarc) (prf_congr_cons_tail heq)


/-! ## §3 · 🏁 `DEUDA_inNeg`, SALDADA -/

/-- Transporte de una NO‑pertenencia por igualdad del contenedor. -/
theorem derives_not_In_congr {x t₁ t₂ : Term}
    (h : axioms ⊢ (t₁ =eq t₂)) (hne : axioms ⊢ neg (In x t₂)) :
    axioms ⊢ neg (In x t₁) :=
  FOL.MetaRules.raa (fun hin =>
    FOL.MetaRules.mp hne (ROBINSON_PlusPlus.Full.eq_subst_in h hin))

theorem deuda_inNeg : ROBINSON_PlusPlus.Meta.VerifierSound.DEUDA_inNeg := by
  intro φ l L _hstd hcd hnm
  -- desarmar `conclsDec`
  unfold ROBINSON_PlusPlus.Meta.VerifierSound.conclsDec at hcd
  rcases hdec : decodeChain (objList l) with _ | rs
  · rw [hdec] at hcd; simp at hcd
  · rw [hdec] at hcd
    simp only [Option.bind] at hcd
    -- las cabezas SON los códigos de las conclusiones
    obtain ⟨fs, hL, heads⟩ := decode_heads l [] rs L hdec hcd
    simp only [List.nil_append] at hL
    have hnm' : ¬ List.Mem φ fs := by rw [hL] at hnm; exact hnm
    -- `runFn nil ⟦l⟧ = ⟦l.map carc⟧ = listFormCodeM fs`
    have hrun : Prf (runFn nil (objList l) =eq objList (l.map carc)) :=
      prf_eq_trans (prf_runFn_objList l nil) (prf_concat_nil_eq _)
    have hchain : axioms ⊢ (runFn nil (objList l) =eq listFormCodeM fs) :=
      prf_to_derives (prf_eq_trans hrun heads)
    exact derives_not_In_congr hchain (prf_not_In_listFormCodeM φ fs hnm')

end ROBINSON_PlusPlus.Meta.ChainNegPrf

/-! ## `export` — por CONSUMO: el módulo F (ensamblaje) necesita `deuda_inNeg` y el puente. -/
export ROBINSON_PlusPlus.Meta.ChainNegPrf (
  derives_lt_congr_right derives_lineWF_congr
  derives_chainOk_neg_of_line
  decodeLine_stepConcl decodeLine_carc decode_heads
  derives_not_In_congr deuda_inNeg
)

/-! ## FOOTPRINT -/
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.deuda_inNeg
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_of_line
