/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf

/-!
# La η DE LISTAS desde la LONGITUD

⛔ **El problema que resuelve.** Los veintiún `ax_premsOf_*` (`Minimal/Axioms.lean`) están
enunciados por *pattern‑matching* sobre un `cons` EXPLÍCITO:

    ax_premsOf_mp : ∀c∀a. premsOf ⟨c, 16̄, a⟩ ≐ ⟨implc a c, a⟩

⇒ Sobre una línea **abstracta** `t` no hay nada que evaluar (§13.1 de `D3ChainDotPrf`). Lo único
que la teoría sabe de `t` es su **longitud**, que sale del `⇔` de su `ax_lineWF_*`. Esto convierte
esa longitud en la reconstrucción entera:

    lenc t ≐ n̄   ⟹   t ≐ ⟨carc t, carc (cdrc t), …, carc (cdrc^{n-1} t)⟩

⚠️ **Y no hay axioma que lo dé.** `ax_lineWF_cons` da **un solo piso** (y sólo para líneas), y
`ax_lenc_*`/`ax_nthc_*` son las ecuaciones recursivas. El piso genérico sale de `prf_nil_or_cons`
(inducción de listas, `SubstfcWitnessPrf`) descartando la rama `nil` por
`prf_succ_ne_zero`; los pisos se apilan por recursión sobre `n`.

**Footprint**: la base sancionada.
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.ListEtaPrf

/-! ## §1 · UN PISO: `L` es un `cons` si su longitud es un sucesor -/


/-- `lenc L = 0` ⇒ `L = nil`. -/
theorem prf_nil_of_lenc_zero (L : Term) : Prf ((lenc L =eq zero) ⇒ (L =eq nil)) := by
  refine prf_deduction ?_
  refine PrfH_or_elim (prf_to_prfH (prf_nil_or_cons L) _) ?_ ?_
  · exact PrfH.hyp _ _ (List.Mem.head _)
  · -- `L = cons (carc L) (cdrc L)` ⇒ `lenc L = succ (lenc (cdrc L))`, contra `lenc L = 0`
    have hcons : PrfH [consOk L, lenc L =eq zero] (L =eq cons (carc L) (cdrc L)) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hz : PrfH [consOk L, lenc L =eq zero] (lenc L =eq zero) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    let A : Formula := Formula.eq (lenc (.var 0)) (liftTerm 0 (succ (lenc (cdrc L))))
    have hS : ∀ s : Term, substFormula 0 s A
        = Formula.eq (lenc s) (succ (lenc (cdrc L))) := by
      intro s
      simp only [A, lenc, cdrc, cons, nil, succ, zero, substFormula, substTerm, substTerms,
        FOL.substTerm_liftTerm, if_true]
    have hlc : PrfH [consOk L, lenc L =eq zero] (lenc L =eq succ (lenc (cdrc L))) :=
      (hS L) ▸ PrfH_leibniz_subst (A := A) (PrfH_eq_symm hcons)
        ((hS (cons (carc L) (cdrc L))) ▸ prf_to_prfH (prf_lenc_cons (carc L) (cdrc L)) _)
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_succ_ne_zero (lenc (cdrc L))) _)
        (PrfH_eq_trans (PrfH_eq_symm hlc) hz))

/-- ⭐ **η DE LISTA DESDE LA LONGITUD**: si `lenc L` es un sucesor, `L` es un `cons`. -/
theorem prf_eta_of_lenc_succ (L n : Term) :
    Prf ((lenc L =eq succ n) ⇒ (L =eq cons (carc L) (cdrc L))) := by
  refine prf_deduction ?_
  refine PrfH_or_elim (prf_to_prfH (prf_nil_or_cons L) _) ?_ ?_
  · -- `L = nil` ⇒ `lenc L = 0`, contra `lenc L = succ n`
    have hnil : PrfH [Formula.eq L nil, lenc L =eq succ n] (L =eq nil) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hs : PrfH [Formula.eq L nil, lenc L =eq succ n] (lenc L =eq succ n) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    let A : Formula := Formula.eq (lenc (.var 0)) (liftTerm 0 zero)
    have hS : ∀ s : Term, substFormula 0 s A = Formula.eq (lenc s) zero := by
      intro s
      simp only [A, lenc, cons, nil, zero, substFormula, substTerm, substTerms,
        FOL.substTerm_liftTerm, if_true]
    have hlz : PrfH [Formula.eq L nil, lenc L =eq succ n] (lenc L =eq zero) :=
      (hS L) ▸ PrfH_leibniz_subst (A := A) (PrfH_eq_symm hnil)
        ((hS nil) ▸ prf_to_prfH prf_lenc_nil _)
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_succ_ne_zero n) _)
        (PrfH_eq_trans (PrfH_eq_symm hs) hlz))
  · exact PrfH.hyp _ _ (List.Mem.head _)

/-- Y la longitud de la cola baja en uno. -/
theorem prf_lenc_cdrc (L n : Term) :
    Prf ((lenc L =eq succ n) ⇒ (lenc (cdrc L) =eq n)) := by
  refine prf_deduction ?_
  have hs : PrfH [lenc L =eq succ n] (lenc L =eq succ n) := prfH_hyp_self _
  have hcons : PrfH [lenc L =eq succ n] (L =eq cons (carc L) (cdrc L)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_eta_of_lenc_succ L n) _) hs
  let A : Formula := Formula.eq (lenc (.var 0)) (liftTerm 0 (succ (lenc (cdrc L))))
  have hS : ∀ s : Term, substFormula 0 s A
      = Formula.eq (lenc s) (succ (lenc (cdrc L))) := by
    intro s
    simp only [A, lenc, cdrc, cons, nil, succ, zero, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, if_true]
  have hlc : PrfH [lenc L =eq succ n] (lenc L =eq succ (lenc (cdrc L))) :=
    (hS L) ▸ PrfH_leibniz_subst (A := A) (PrfH_eq_symm hcons)
      ((hS (cons (carc L) (cdrc L))) ▸ prf_to_prfH (prf_lenc_cons (carc L) (cdrc L)) _)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_succ_inj (lenc (cdrc L)) n) _)
    (PrfH_eq_trans (PrfH_eq_symm hlc) hs)


/-! ## §2 · LA η ITERADA — la lista entera desde su longitud

`ax_premsOf_*` hace *pattern‑matching* sobre un `cons` explícito de longitud fija, así que para
aplicarlo a una línea **abstracta** hay que reconstruirla entera. §1 da un piso; esto los apila. -/

/-- `cdrc` iterado `j` veces. -/
def cdrcN (L : Term) : Nat → Term
  | 0     => L
  | n + 1 => cdrcN (cdrc L) n

/-- La reconstrucción de `L` como `cons` de longitud `n`, con los componentes escritos como
    `carc (cdrcN L j)` — que es la forma que los `ax_premsOf_*` consumen. -/
def etaAt (L : Term) : Nat → Term
  | 0     => nil
  | n + 1 => cons (carc L) (etaAt (cdrc L) n)

/-- ⭐⭐ **η ITERADA**: `lenc L = n̄ ⇒ L = ⟨carc L, carc (cdrc L), …⟩`. Recursión sobre `n`,
    con `prf_lenc_cdrc` bajando la longitud en cada piso. -/
theorem prf_eta_lenc : ∀ (n : Nat) (L : Term),
    Prf ((lenc L =eq numeralM n) ⇒ (L =eq etaAt L n))
  | 0, L => prf_nil_of_lenc_zero L
  | n + 1, L => by
      refine prf_deduction ?_
      have hs : PrfH [lenc L =eq numeralM (n + 1)] (lenc L =eq succ (numeralM n)) :=
        prfH_hyp_self _
      have hcons : PrfH [lenc L =eq numeralM (n + 1)] (L =eq cons (carc L) (cdrc L)) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_eta_of_lenc_succ L (numeralM n)) _) hs
      have htail : PrfH [lenc L =eq numeralM (n + 1)] (lenc (cdrc L) =eq numeralM n) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_lenc_cdrc L (numeralM n)) _) hs
      have hih : PrfH [lenc L =eq numeralM (n + 1)] (cdrc L =eq etaAt (cdrc L) n) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_eta_lenc n (cdrc L)) _) htail
      exact PrfH_eq_trans hcons (PrfH_congr_cons_tail hih)

/-! ## §3 · EL TAG, LEÍDO DE LA η

`lineTag L = nthc L 1̄`, y la η lo pone en `carc (cdrc L)`. Los dos pisos se recorren con
`prf_nthc_succ` y `prf_nthc_zero`. -/

/-- `nthc L 1̄ = carc (cdrc L)` para una lista de longitud ≥ 2. -/
theorem prf_nthc1_carc_cdrc (L : Term) (n : Nat) :
    Prf ((lenc L =eq numeralM (n + 2)) ⇒ (nthc L (numeralM 1) =eq carc (cdrc L))) := by
  refine prf_deduction ?_
  have hs : PrfH [lenc L =eq numeralM (n + 2)] (lenc L =eq succ (numeralM (n + 1))) :=
    prfH_hyp_self _
  have hcons : PrfH [lenc L =eq numeralM (n + 2)] (L =eq cons (carc L) (cdrc L)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_eta_of_lenc_succ L (numeralM (n + 1))) _) hs
  have htail : PrfH [lenc L =eq numeralM (n + 2)] (lenc (cdrc L) =eq succ (numeralM n)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_lenc_cdrc L (numeralM (n + 1))) _) hs
  have hcons2 : PrfH [lenc L =eq numeralM (n + 2)]
      (cdrc L =eq cons (carc (cdrc L)) (cdrc (cdrc L))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_eta_of_lenc_succ (cdrc L) (numeralM n)) _) htail
  -- piso 1: `nthc L 1̄ = nthc (cdrc L) 0̄`
  let A : Formula := Formula.eq (nthc (.var 0) (liftTerm 0 (numeralM 1)))
    (liftTerm 0 (nthc (cdrc L) zero))
  have hS : ∀ s : Term, substFormula 0 s A
      = Formula.eq (nthc s (numeralM 1)) (nthc (cdrc L) zero) := by
    intro s
    simp only [A, nthc, cdrc, cons, nil, succ, zero, numeralM, substFormula, substTerm,
      substTerms, FOL.substTerm_liftTerm, if_true]
  have hstep1 : PrfH [lenc L =eq numeralM (n + 2)]
      (nthc L (numeralM 1) =eq nthc (cdrc L) zero) :=
    (hS L) ▸ PrfH_leibniz_subst (A := A) (PrfH_eq_symm hcons)
      ((hS (cons (carc L) (cdrc L))) ▸
        prf_to_prfH (prf_nthc_succ (carc L) (cdrc L) zero) _)
  -- piso 2: `nthc (cdrc L) 0̄ = carc (cdrc L)`
  let B : Formula := Formula.eq (nthc (.var 0) (liftTerm 0 zero))
    (liftTerm 0 (carc (cdrc L)))
  have hSB : ∀ s : Term, substFormula 0 s B
      = Formula.eq (nthc s zero) (carc (cdrc L)) := by
    intro s
    simp only [B, nthc, carc, cdrc, cons, nil, zero, substFormula, substTerm,
      substTerms, FOL.substTerm_liftTerm, if_true]
  have hstep2 : PrfH [lenc L =eq numeralM (n + 2)]
      (nthc (cdrc L) zero =eq carc (cdrc L)) :=
    (hSB (cdrc L)) ▸ PrfH_leibniz_subst (A := B) (PrfH_eq_symm hcons2)
      ((hSB (cons (carc (cdrc L)) (cdrc (cdrc L)))) ▸
        prf_to_prfH (prf_nthc_zero (carc (cdrc L)) (cdrc (cdrc L))) _)
  exact PrfH_eq_trans hstep1 hstep2

end ROBINSON_PlusPlus.Meta.ListEtaPrf

/-! ## `export` — por CONSUMO

Consumidor previsto: la evaluación de `premsOf` por tags (`hbody`(b) de D3), que necesita la
línea reconstruida para poder instanciar `ax_premsOf_*`. -/
export ROBINSON_PlusPlus.Meta.ListEtaPrf (
  prf_nil_of_lenc_zero prf_eta_of_lenc_succ prf_lenc_cdrc
  cdrcN etaAt prf_eta_lenc prf_nthc1_carc_cdrc
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.ListEtaPrf.prf_eta_lenc
#print axioms ROBINSON_PlusPlus.Meta.ListEtaPrf.prf_nthc1_carc_cdrc
