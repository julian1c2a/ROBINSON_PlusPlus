/-
# SONDEO — VÍA 1: ¿es el testigo cerrable bajo `liftc zero` VÍA EL MAP `liftsc`?

Autocontenido: `import ROBINSON_PlusPlus.Meta` y copia de `sondeos/DiscriminaEcuacional.lean`
(namespace `PilotoParticion`) las definiciones necesarias.

Se mide, POR MITADES:

* **mitad `wTs`** (`isTermsCodeB`, códigos de LISTA de términos) bajo `liftsc zero`;
* **mitad `wT`**  (`isTermCodeB`,  códigos de TÉRMINO)          bajo `liftc  zero`.

CERO axiomas nuevos, CERO símbolos de función nuevos.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LiftMap

/-! ## 0 · Combinadores lógicos (copia de `sondeos/DiscriminaEcuacional.lean` §0) -/

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

theorem prf_orL {A B : Formula} (h : Prf A) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prfᵢ.j1 A B)) h

theorem prf_orR {A B : Formula} (h : Prf B) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prfᵢ.j2 A B)) h

theorem PrfH_orL {Γ : List Formula} {A B : Formula} (h : PrfH Γ A) : PrfH Γ (lor A B) :=
  PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.j1 A B)) h

theorem PrfH_orR {Γ : List Formula} {A B : Formula} (h : PrfH Γ B) : PrfH Γ (lor A B) :=
  PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.j2 A B)) h

/-! ## 1 · Las definiciones, copiadas LITERALMENTE de `sondeos/DiscriminaEcuacional.lean` §1 -/

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def varOkT (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 0)) (Formula.eq (lenc X) (numeralM 2))

def funcOkT (wTs X : Term) : Formula :=
  land (land (Formula.eq (carc X) (numeralM 1)) (Formula.eq (lenc X) (numeralM 3)))
       (In (nthc X (numeralM 2)) wTs)

def isTermCodeB (wT wTs X : Term) : Formula :=
  lor (cOk X (varOkT X)) (cOk X (funcOkT wTs X))

def isTermsCodeB (wT wTs X : Term) : Formula :=
  lor (Formula.eq X nil)
      (cOk X (land (In (carc X) wT) (In (cdrc X) wTs)))

/-! ## 2 · Congruencias (Leibniz) — las de `DiscriminaEcuacional` más las que faltaban -/

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons a b)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons a b)))

/-- Congruencia de `liftsc` en el código (2º argumento). **No existía.** -/
theorem prf_congr_liftsc {c a b : Term} (h : Prf (a =eq b)) :
    Prf (liftsc c a =eq liftsc c b) := by
  let f : Formula :=
    Formula.eq (liftsc (liftTerm 0 c) (liftTerm 0 a)) (liftsc (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (liftsc c a) (liftsc c s) := by
    intro s
    simp only [f, liftsc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ prf_leibniz_subst (A := f) h ((hS a) ▸ prf_refl (liftsc c a))

theorem PrfH_congr_liftsc {Γ : List Formula} {c a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (liftsc c a =eq liftsc c b) := by
  let f : Formula :=
    Formula.eq (liftsc (liftTerm 0 c) (liftTerm 0 a)) (liftsc (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (liftsc c a) (liftsc c s) := by
    intro s
    simp only [f, liftsc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (liftsc c a)) Γ)

theorem prf_congr_In_left {u v w : Term} (h : Prf (u =eq v)) (hin : Prf (In u w)) :
    Prf (In v w) := by
  let f : Formula := In (.var 0) (liftTerm 0 w)
  have hS : ∀ s : Term, substFormula 0 s f = In s w := by
    intro s
    simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS v) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h []) ((hS u) ▸ prf_to_prfH hin [])) rfl

theorem PrfH_congr_In_left {Γ : List Formula} {u v w : Term}
    (h : PrfH Γ (u =eq v)) (hin : PrfH Γ (In u w)) : PrfH Γ (In v w) := by
  let f : Formula := In (.var 0) (liftTerm 0 w)
  have hS : ∀ s : Term, substFormula 0 s f = In s w := by
    intro s
    simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS v) ▸ PrfH_leibniz_subst (A := f) h ((hS u) ▸ hin)

theorem prf_congr_In_right {u w w' : Term} (h : Prf (w =eq w')) (hin : Prf (In u w)) :
    Prf (In u w') := by
  let f : Formula := In (liftTerm 0 u) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = In u s := by
    intro s
    simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS w') ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h []) ((hS w) ▸ prf_to_prfH hin [])) rfl

theorem PrfH_congr_isTermCodeB {Γ : List Formula} {wT wTs X₁ X₂ : Term}
    (h : PrfH Γ (X₁ =eq X₂)) (hN : PrfH Γ (isTermCodeB wT wTs X₁)) :
    PrfH Γ (isTermCodeB wT wTs X₂) := by
  let f : Formula := isTermCodeB (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = isTermCodeB wT wTs s := by
    intro s
    simp only [f, isTermCodeB, cOk, consOk, varOkT, funcOkT, land, lor, In,
      carc, cdrc, lenc, nthc, cons, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, substTerm_numeralM, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := f) h ((hS X₁) ▸ hN)

theorem PrfH_congr_isTermsCodeB {Γ : List Formula} {wT wTs X₁ X₂ : Term}
    (h : PrfH Γ (X₁ =eq X₂)) (hN : PrfH Γ (isTermsCodeB wT wTs X₁)) :
    PrfH Γ (isTermsCodeB wT wTs X₂) := by
  let f : Formula := isTermsCodeB (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = isTermsCodeB wT wTs s := by
    intro s
    simp only [f, isTermsCodeB, cOk, consOk, land, lor, In,
      carc, cdrc, cons, nil, zero, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := f) h ((hS X₁) ▸ hN)

/-! ## 3 · LA HIPÓTESIS «MAP» — expresable SIN símbolos nuevos

    `mapsT W W'` dice: *la imagen de `W` por `liftc 0` cabe en `W'`*. Es una fórmula OBJETO
    (un `∀` de De Bruijn), no un símbolo de función. `mapsT_inst` la desgrana al esquema
    meta que usan los teoremas de abajo. -/

def mapsT (W W' : Term) : Formula :=
  Formula.forall (Formula.impl (In (.var 0) (liftTerm 0 W)) (In (liftc zero (.var 0)) (liftTerm 0 W')))

def mapsTs (W W' : Term) : Formula :=
  Formula.forall (Formula.impl (In (.var 0) (liftTerm 0 W)) (In (liftsc zero (.var 0)) (liftTerm 0 W')))

theorem mapsT_inst {W W' : Term} (h : Prf (mapsT W W')) (u : Term) :
    Prf (In u W ⇒ In (liftc zero u) W') := by
  have hh := prf_spec h u
  simpa only [mapsT, In, liftc, zero, substFormula, substTerm, substTerms,
    FOL.substTerm_liftTerm, if_true] using hh

theorem mapsTs_inst {W W' : Term} (h : Prf (mapsTs W W')) (u : Term) :
    Prf (In u W ⇒ In (liftsc zero u) W') := by
  have hh := prf_spec h u
  simpa only [mapsTs, In, liftsc, zero, substFormula, substTerm, substTerms,
    FOL.substTerm_liftTerm, if_true] using hh

/-! ## 4 · ✅ MITAD `wTs` — `isTermsCodeB` SE CIERRA bajo `liftsc zero`, con `W'T`/`W'Ts`
       COMPLETAMENTE ABSTRACTOS y sólo las dos hipótesis «map».

    La razón estructural: `ax_liftsc_cons` está enunciado sobre un `cons` GENÉRICO, y
    `consOk X` da exactamente `X = cons (carc X) (cdrc X)`. La forma ECUACIONAL basta. -/

theorem lift_isTermsCodeB (wT wTs W'T W'Ts X : Term)
    (hT  : ∀ u : Term, Prf (In u wT  ⇒ In (liftc  zero u) W'T))
    (hTs : ∀ u : Term, Prf (In u wTs ⇒ In (liftsc zero u) W'Ts)) :
    Prf (isTermsCodeB wT wTs X ⇒ isTermsCodeB W'T W'Ts (liftsc zero X)) := by
  refine prf_or_elim_imp ?nilC ?consC
  case nilC =>
    refine prf_deduction ?_
    have h : PrfH [Formula.eq X nil] (X =eq nil) := prfH_hyp_self _
    have hL : PrfH [Formula.eq X nil] (liftsc zero X =eq nil) :=
      PrfH_eq_trans (PrfH_congr_liftsc h) (prf_to_prfH (prf_liftsc_nil zero) _)
    exact PrfH_orL hL
  case consC =>
    refine prf_deduction ?_
    let Γ : List Formula := [cOk X (land (In (carc X) wT) (In (cdrc X) wTs))]
    show PrfH Γ (isTermsCodeB W'T W'Ts (liftsc zero X))
    have hh : PrfH Γ (cOk X (land (In (carc X) wT) (In (cdrc X) wTs))) := prfH_hyp_self _
    have hcons : PrfH Γ (consOk X) := PrfH_and_elim_left hh
    have hins : PrfH Γ (land (In (carc X) wT) (In (cdrc X) wTs)) := PrfH_and_elim_right hh
    have hin1 : PrfH Γ (In (carc X) wT)  := PrfH_and_elim_left hins
    have hin2 : PrfH Γ (In (cdrc X) wTs) := PrfH_and_elim_right hins
    have hL : PrfH Γ (liftsc zero X =eq cons (liftc zero (carc X)) (liftsc zero (cdrc X))) :=
      PrfH_eq_trans (PrfH_congr_liftsc hcons)
        (prf_to_prfH (prf_liftsc_cons zero (carc X) (cdrc X)) _)
    -- el testigo lifteado, en forma de `cons` explícito
    have hcY : PrfH Γ (consOk (cons (liftc zero (carc X)) (liftsc zero (cdrc X)))) :=
      prf_to_prfH (prf_consOk_cons _ _) _
    have hA : PrfH Γ (In (liftc zero (carc X)) W'T) :=
      PrfH.mp _ _ _ (prf_to_prfH (hT (carc X)) _) hin1
    have hB : PrfH Γ (In (liftsc zero (cdrc X)) W'Ts) :=
      PrfH.mp _ _ _ (prf_to_prfH (hTs (cdrc X)) _) hin2
    have hA' : PrfH Γ (In (carc (cons (liftc zero (carc X)) (liftsc zero (cdrc X)))) W'T) :=
      PrfH_congr_In_left (PrfH_eq_symm (prf_to_prfH (prf_carc_cons _ _) _)) hA
    have hB' : PrfH Γ (In (cdrc (cons (liftc zero (carc X)) (liftsc zero (cdrc X)))) W'Ts) :=
      PrfH_congr_In_left (PrfH_eq_symm (prf_to_prfH (prf_cdrc_cons _ _) _)) hB
    have hY : PrfH Γ
        (isTermsCodeB W'T W'Ts (cons (liftc zero (carc X)) (liftsc zero (cdrc X)))) :=
      PrfH_orR (PrfH_and_intro hcY (PrfH_and_intro hA' hB'))
    exact PrfH_congr_isTermsCodeB (PrfH_eq_symm hL) hY

/-! ## 5 · ❌ MITAD `wT` — la forma ECUACIONAL **NO** determina `liftc zero X`

    `ax_liftc_var_lt/ge` y `ax_liftc_func` están enunciados sobre `varc n` y `funcc s ts`,
    o sea sobre la ESPINA COMPLETA (`cons 0 (cons n nil)` / `cons 1 (cons s (cons ts nil))`).
    De `consOk X ∧ carc X = 0 ∧ lenc X = 2` sólo se obtiene `X = cons 0 (cdrc X)`: falta
    `cdrc X = cons (nthc X 1) nil`, que **no es derivable** (los axiomas de `lenc`/`carc`/`cdrc`
    sólo computan sobre constructores; no hay inversión `lenc t = σ n → t = cons (carc t) (cdrc t)`).
    ⇒ `liftc zero X` queda OPACO y no se puede probar nada de él.

    Lo que SÍ se cierra es la variante de **ESPINA** del predicado (§6), que es
    **ESTRICTAMENTE MÁS FUERTE** (§7: implica `isTermCodeB`) y por tanto conserva la
    discriminación medida en `sondeos/DiscriminaEcuacional.lean`. -/

/-! ## 6 · La variante de ESPINA y su CLAUSURA bajo `liftc zero` -/

/-- `X` es código de TÉRMINO, en forma de ESPINA: se afirma la igualdad con el
    CONSTRUCTOR reconstruido desde las propias casillas de `X`. -/
def isTermCodeS (wT wTs X : Term) : Formula :=
  lor (Formula.eq X (varc (nthc X (numeralM 1))))
      (land (Formula.eq X (funcc (nthc X (numeralM 1)) (nthc X (numeralM 2))))
            (In (nthc X (numeralM 2)) wTs))

theorem PrfH_congr_isTermCodeS {Γ : List Formula} {wT wTs X₁ X₂ : Term}
    (h : PrfH Γ (X₁ =eq X₂)) (hN : PrfH Γ (isTermCodeS wT wTs X₁)) :
    PrfH Γ (isTermCodeS wT wTs X₂) := by
  let f : Formula := isTermCodeS (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = isTermCodeS wT wTs s := by
    intro s
    simp only [f, isTermCodeS, land, lor, In, varc, funcc, nthc, cons, nil, zero, succ,
      substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, substTerm_numeralM, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := f) h ((hS X₁) ▸ hN)

theorem prf_congr_varc {a b : Term} (h : Prf (a =eq b)) : Prf (varc a =eq varc b) :=
  prf_congr_cons_tail (prf_congr_cons_head h)

theorem prf_congr_funcc_snd {s a b : Term} (h : Prf (a =eq b)) :
    Prf (funcc s a =eq funcc s b) :=
  prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head h))

theorem prf_congr_funcc_fst {a b t : Term} (h : Prf (a =eq b)) :
    Prf (funcc a t =eq funcc b t) :=
  prf_congr_cons_tail (prf_congr_cons_head h)

/-! ### Cálculo de las casillas sobre los constructores -/

theorem prf_nthc_varc_1 (n : Term) : Prf (nthc (varc n) (numeralM 1) =eq n) := by
  show Prf (nthc (cons zero (cons n nil)) (succ (numeralM 0)) =eq n)
  exact prf_eq_trans (prf_nthc_succ zero (cons n nil) (numeralM 0)) (prf_nthc_zero n nil)

theorem prf_nthc_funcc_1 (s ts : Term) : Prf (nthc (funcc s ts) (numeralM 1) =eq s) := by
  show Prf (nthc (cons (succ zero) (cons s (cons ts nil))) (succ (numeralM 0)) =eq s)
  exact prf_eq_trans (prf_nthc_succ (succ zero) (cons s (cons ts nil)) (numeralM 0))
    (prf_nthc_zero s (cons ts nil))

theorem prf_nthc_funcc_2 (s ts : Term) : Prf (nthc (funcc s ts) (numeralM 2) =eq ts) := by
  show Prf (nthc (cons (succ zero) (cons s (cons ts nil))) (succ (succ (numeralM 0))) =eq ts)
  refine prf_eq_trans (prf_nthc_succ (succ zero) (cons s (cons ts nil)) (succ (numeralM 0))) ?_
  exact prf_eq_trans (prf_nthc_succ s (cons ts nil) (numeralM 0)) (prf_nthc_zero ts nil)

theorem prf_carc_varc (n : Term) : Prf (carc (varc n) =eq numeralM 0) :=
  prf_carc_cons zero (cons n nil)

theorem prf_lenc_varc (n : Term) : Prf (lenc (varc n) =eq numeralM 2) := by
  show Prf (lenc (cons zero (cons n nil)) =eq succ (succ (numeralM 0)))
  exact prf_eq_trans (prf_lenc_cons zero (cons n nil))
    (prf_eq_congr_succ (prf_eq_trans (prf_lenc_cons n nil) (prf_eq_congr_succ prf_lenc_nil)))

theorem prf_carc_funcc (s ts : Term) : Prf (carc (funcc s ts) =eq numeralM 1) :=
  prf_carc_cons (succ zero) (cons s (cons ts nil))

theorem prf_lenc_funcc (s ts : Term) : Prf (lenc (funcc s ts) =eq numeralM 3) := by
  show Prf (lenc (cons (succ zero) (cons s (cons ts nil))) =eq succ (succ (succ (numeralM 0))))
  refine prf_eq_trans (prf_lenc_cons (succ zero) (cons s (cons ts nil))) (prf_eq_congr_succ ?_)
  exact prf_eq_trans (prf_lenc_cons s (cons ts nil))
    (prf_eq_congr_succ (prf_eq_trans (prf_lenc_cons ts nil) (prf_eq_congr_succ prf_lenc_nil)))

/-! ### Los dos constructores satisfacen `isTermCodeS` -/

theorem prf_isTermCodeS_varc (wT wTs n : Term) : Prf (isTermCodeS wT wTs (varc n)) :=
  prf_orL (prf_congr_varc (prf_eq_symm (prf_nthc_varc_1 n)))

theorem prf_isTermCodeS_funcc (wT wTs s ts : Term) :
    Prf (In ts wTs ⇒ isTermCodeS wT wTs (funcc s ts)) := by
  refine prf_deduction ?_
  have h : PrfH [In ts wTs] (In ts wTs) := prfH_hyp_self _
  have hsp : PrfH [In ts wTs]
      (funcc s ts =eq funcc (nthc (funcc s ts) (numeralM 1)) (nthc (funcc s ts) (numeralM 2))) :=
    prf_to_prfH (prf_eq_trans (prf_congr_funcc_snd (prf_eq_symm (prf_nthc_funcc_2 s ts)))
      (prf_congr_funcc_fst (prf_eq_symm (prf_nthc_funcc_1 s ts)))) _
  have hin : PrfH [In ts wTs] (In (nthc (funcc s ts) (numeralM 2)) wTs) :=
    PrfH_congr_In_left (PrfH_eq_symm (prf_to_prfH (prf_nthc_funcc_2 s ts) _)) h
  exact PrfH_orR (PrfH_and_intro hsp hin)

/-- ✅ **MITAD `wT`, forma de ESPINA: CIERRA.** `W'T`/`W'Ts` abstractos, una sola
    hipótesis «map» (la de `wTs`; la de `wT` ni se usa: `isTermCodeB`/`isTermCodeS`
    no consultan `wT`). -/
theorem lift_isTermCodeS (wT wTs W'T W'Ts X : Term)
    (hTs : ∀ u : Term, Prf (In u wTs ⇒ In (liftsc zero u) W'Ts)) :
    Prf (isTermCodeS wT wTs X ⇒ isTermCodeS W'T W'Ts (liftc zero X)) := by
  refine prf_or_elim_imp ?varC ?funcC
  case varC =>
    refine prf_deduction ?_
    let Γ : List Formula := [Formula.eq X (varc (nthc X (numeralM 1)))]
    show PrfH Γ (isTermCodeS W'T W'Ts (liftc zero X))
    have h : PrfH Γ (X =eq varc (nthc X (numeralM 1))) := prfH_hyp_self _
    have hl : PrfH Γ (liftc zero X =eq varc (succ (nthc X (numeralM 1)))) :=
      PrfH_eq_trans (PrfH_congr_liftc h)
        (prf_to_prfH (prf_mp (prf_liftc_var_ge zero (nthc X (numeralM 1)))
          (prf_zero_lt_succ (nthc X (numeralM 1)))) _)
    exact PrfH_congr_isTermCodeS (PrfH_eq_symm hl)
      (prf_to_prfH (prf_isTermCodeS_varc W'T W'Ts (succ (nthc X (numeralM 1)))) _)
  case funcC =>
    refine prf_deduction ?_
    let Γ : List Formula :=
      [land (Formula.eq X (funcc (nthc X (numeralM 1)) (nthc X (numeralM 2))))
            (In (nthc X (numeralM 2)) wTs)]
    show PrfH Γ (isTermCodeS W'T W'Ts (liftc zero X))
    have hh : PrfH Γ (land (Formula.eq X (funcc (nthc X (numeralM 1)) (nthc X (numeralM 2))))
        (In (nthc X (numeralM 2)) wTs)) := prfH_hyp_self _
    have hsp : PrfH Γ (X =eq funcc (nthc X (numeralM 1)) (nthc X (numeralM 2))) :=
      PrfH_and_elim_left hh
    have hin : PrfH Γ (In (nthc X (numeralM 2)) wTs) := PrfH_and_elim_right hh
    have hl : PrfH Γ (liftc zero X
        =eq funcc (nthc X (numeralM 1)) (liftsc zero (nthc X (numeralM 2)))) :=
      PrfH_eq_trans (PrfH_congr_liftc hsp)
        (prf_to_prfH (prf_liftc_func zero (nthc X (numeralM 1)) (nthc X (numeralM 2))) _)
    have hin' : PrfH Γ (In (liftsc zero (nthc X (numeralM 2))) W'Ts) :=
      PrfH.mp _ _ _ (prf_to_prfH (hTs (nthc X (numeralM 2))) _) hin
    have hY : PrfH Γ (isTermCodeS W'T W'Ts
        (funcc (nthc X (numeralM 1)) (liftsc zero (nthc X (numeralM 2))))) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeS_funcc W'T W'Ts _ _) _) hin'
    exact PrfH_congr_isTermCodeS (PrfH_eq_symm hl) hY

/-! ## 7 · La ESPINA es ESTRICTAMENTE MÁS FUERTE que la forma ECUACIONAL

    ⇒ pasar a `isTermCodeS` **no debilita la discriminación** medida en
    `sondeos/DiscriminaEcuacional.lean`: todo lo que refuta `isTermCodeB` refuta `isTermCodeS`. -/

theorem prf_isTermCodeB_varc (wT wTs n : Term) : Prf (isTermCodeB wT wTs (varc n)) :=
  prf_orL (prf_and_intro (prf_consOk_cons zero (cons n nil))
    (prf_and_intro (prf_carc_varc n) (prf_lenc_varc n)))

theorem prf_isTermCodeB_funcc (wT wTs s ts : Term) :
    Prf (In ts wTs ⇒ isTermCodeB wT wTs (funcc s ts)) := by
  refine prf_deduction ?_
  have h : PrfH [In ts wTs] (In ts wTs) := prfH_hyp_self _
  have hin : PrfH [In ts wTs] (In (nthc (funcc s ts) (numeralM 2)) wTs) :=
    PrfH_congr_In_left (PrfH_eq_symm (prf_to_prfH (prf_nthc_funcc_2 s ts) _)) h
  exact PrfH_orR (PrfH_and_intro (prf_to_prfH (prf_consOk_cons (succ zero) _) _)
    (PrfH_and_intro (PrfH_and_intro (prf_to_prfH (prf_carc_funcc s ts) _)
      (prf_to_prfH (prf_lenc_funcc s ts) _)) hin))

theorem prf_isTermCodeS_imp_isTermCodeB (wT wTs X : Term) :
    Prf (isTermCodeS wT wTs X ⇒ isTermCodeB wT wTs X) := by
  refine prf_or_elim_imp ?varC ?funcC
  case varC =>
    refine prf_deduction ?_
    let Γ : List Formula := [Formula.eq X (varc (nthc X (numeralM 1)))]
    show PrfH Γ (isTermCodeB wT wTs X)
    have h : PrfH Γ (X =eq varc (nthc X (numeralM 1))) := prfH_hyp_self _
    exact PrfH_congr_isTermCodeB (PrfH_eq_symm h)
      (prf_to_prfH (prf_isTermCodeB_varc wT wTs (nthc X (numeralM 1))) _)
  case funcC =>
    refine prf_deduction ?_
    let Γ : List Formula :=
      [land (Formula.eq X (funcc (nthc X (numeralM 1)) (nthc X (numeralM 2))))
            (In (nthc X (numeralM 2)) wTs)]
    show PrfH Γ (isTermCodeB wT wTs X)
    have hh : PrfH Γ (land (Formula.eq X (funcc (nthc X (numeralM 1)) (nthc X (numeralM 2))))
        (In (nthc X (numeralM 2)) wTs)) := prfH_hyp_self _
    have hsp : PrfH Γ (X =eq funcc (nthc X (numeralM 1)) (nthc X (numeralM 2))) :=
      PrfH_and_elim_left hh
    have hin : PrfH Γ (In (nthc X (numeralM 2)) wTs) := PrfH_and_elim_right hh
    exact PrfH_congr_isTermCodeB (PrfH_eq_symm hsp)
      (PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeB_funcc wT wTs _ _) _) hin)

/-! ## 8 · ¿Qué forma se ve OBLIGADO a tener `W'`?

    * **`W'T`** (mitad de TÉRMINOS) sí admite forma UNIFORME: es `liftsc zero wT`,
      porque **`liftsc` ES el map de `liftc`** (`ax_liftsc_nil`/`ax_liftsc_cons`).
      §8.1 lo comprueba sobre listas literales.
    * **`W'Ts`** (mitad de LISTAS) **no** admite forma uniforme: haría falta el map DE
      `liftsc`, un nivel más arriba, que no está en la teoría. Pero **no hace falta**:
      para un testigo LITERAL la imagen es el término literal `objList (L.map (liftsc zero))`
      — cero símbolos nuevos. §8.2 descarga ambas hipótesis «map». -/

/-- §8.1 · `liftsc zero` **es** el map de `liftc zero` sobre listas literales. -/
theorem prf_liftsc_objList (c : Term) : ∀ L : List Term,
    Prf (liftsc c (objList L) =eq objList (L.map (liftc c)))
  | []      => prf_liftsc_nil c
  | t :: ts => by
      show Prf (liftsc c (cons t (objList ts)) =eq cons (liftc c t) (objList (ts.map (liftc c))))
      exact prf_eq_trans (prf_liftsc_cons c t (objList ts))
        (prf_congr_cons_tail (prf_liftsc_objList c ts))

/-! ### §8.2 · Descarga de las hipótesis «map» sobre testigos LITERALES -/

theorem prf_In_cons_head (u t : Term) : Prf (In u (cons u t)) :=
  prf_mp (prf_In_of_boundedIn u (cons u t))
    (prf_mp (prf_boundedIn_head u u t) (prf_refl u))

theorem prf_In_cons_tail_imp (u h t : Term) : Prf (In u t ⇒ In u (cons h t)) :=
  impT (prf_boundedIn_of_In u t)
    (impT (prf_boundedIn_tail u h t) (prf_In_of_boundedIn u (cons h t)))

/-- **La hipótesis `mapsT` es DEMOSTRABLE para toda lista LITERAL**, con la imagen
    `objList (L.map (liftc zero))` — que además es igual a `liftsc zero (objList L)` (§8.1). -/
theorem prf_mapsT_objList : ∀ (L : List Term) (u : Term),
    Prf (In u (objList L) ⇒ In (liftc zero u) (objList (L.map (liftc zero))))
  | [],     u => impT (prf_boundedIn_of_In u nil)
                   (impT (prf_boundedIn_nil u) (Prf.incl (Prfᵢ.efq _)))
  | a :: L, u => by
      show Prf (In u (cons a (objList L))
        ⇒ In (liftc zero u) (cons (liftc zero a) (objList (L.map (liftc zero)))))
      refine impT (impT (prf_boundedIn_of_In u (cons a (objList L)))
        (prf_boundedIn_cons u a (objList L))) (prf_or_elim_imp ?_ ?_)
      · refine prf_deduction ?_
        have h : PrfH [Formula.eq u a] (u =eq a) := prfH_hyp_self _
        exact PrfH_congr_In_left (PrfH_eq_symm (PrfH_congr_liftc h))
          (prf_to_prfH (prf_In_cons_head (liftc zero a) (objList (L.map (liftc zero)))) _)
      · exact impT (prf_In_of_boundedIn u (objList L))
          (impT (prf_mapsT_objList L u)
            (prf_In_cons_tail_imp (liftc zero u) (liftc zero a) (objList (L.map (liftc zero)))))

/-- Ídem para la mitad de LISTAS: la imagen es `objList (L.map (liftsc zero))`, un término
    LITERAL. **No hace falta ningún «map de `liftsc`».** -/
theorem prf_mapsTs_objList : ∀ (L : List Term) (u : Term),
    Prf (In u (objList L) ⇒ In (liftsc zero u) (objList (L.map (liftsc zero))))
  | [],     u => impT (prf_boundedIn_of_In u nil)
                   (impT (prf_boundedIn_nil u) (Prf.incl (Prfᵢ.efq _)))
  | a :: L, u => by
      show Prf (In u (cons a (objList L))
        ⇒ In (liftsc zero u) (cons (liftsc zero a) (objList (L.map (liftsc zero)))))
      refine impT (impT (prf_boundedIn_of_In u (cons a (objList L)))
        (prf_boundedIn_cons u a (objList L))) (prf_or_elim_imp ?_ ?_)
      · refine prf_deduction ?_
        have h : PrfH [Formula.eq u a] (u =eq a) := prfH_hyp_self _
        exact PrfH_congr_In_left (PrfH_eq_symm (PrfH_congr_liftsc h))
          (prf_to_prfH (prf_In_cons_head (liftsc zero a) (objList (L.map (liftsc zero)))) _)
      · exact impT (prf_In_of_boundedIn u (objList L))
          (impT (prf_mapsTs_objList L u)
            (prf_In_cons_tail_imp (liftsc zero u) (liftsc zero a) (objList (L.map (liftsc zero)))))

/-! ## 9 · EL CIERRE COMPUESTO sobre testigos literales -/

/-- Las DOS mitades a la vez, con testigos LITERALES y sus imágenes explícitas. -/
theorem lift_par_objList (LT LTs : List Term) (X : Term) :
    Prf (isTermCodeS (objList LT) (objList LTs) X
      ⇒ isTermCodeS (objList (LT.map (liftc zero))) (objList (LTs.map (liftsc zero)))
          (liftc zero X)) :=
  lift_isTermCodeS _ _ _ _ X (prf_mapsTs_objList LTs)

theorem lift_par_objList_s (LT LTs : List Term) (X : Term) :
    Prf (isTermsCodeB (objList LT) (objList LTs) X
      ⇒ isTermsCodeB (objList (LT.map (liftc zero))) (objList (LTs.map (liftsc zero)))
          (liftsc zero X)) :=
  lift_isTermsCodeB _ _ _ _ X (prf_mapsT_objList LT) (prf_mapsTs_objList LTs)

/-! ## 10 · EL PUENTE QUE FALTA, MEDIDO — la forma ecuacional cierra **exactamente** módulo
       DOS principios de INVERSIÓN de `lenc`, que la teoría NO tiene.

    Los únicos axiomas de `lenc`/`carc`/`cdrc` son `ax_lenc_nil`, `ax_lenc_cons`, `ax_carc`,
    `ax_cdrc`: **sólo computan sobre constructores**. No hay ninguna inversión. Aquí se
    aíslan las dos que harían falta, **como hipótesis Lean** (no como axiomas: el footprint
    sigue net‑0), y se comprueba que con ellas —y sólo con ellas— el puente sale. -/

theorem PrfH_congr_lenc {Γ : List Formula} {t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (lenc t₁ =eq lenc t₂) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 t₁)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc t₁) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (lenc t₁)) Γ)

theorem PrfH_congr_nthc_lst {Γ : List Formula} {w₁ w₂ : Term} (i : Term)
    (h : PrfH Γ (w₁ =eq w₂)) : PrfH Γ (nthc w₁ i =eq nthc w₂ i) := by
  let f : Formula :=
    Formula.eq (nthc (liftTerm 0 w₁) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w₁ i) (nthc s i) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS w₂) ▸ PrfH_leibniz_subst (A := f) h
    ((hS w₁) ▸ prf_to_prfH (prf_refl (nthc w₁ i)) Γ)

/-- **(I1)** `lenc t = σ n ⇒ t = cons (carc t) (cdrc t)`. **NO es un axioma de la teoría.** -/
abbrev Inv1 : Prop := ∀ t n : Term, Prf (Formula.eq (lenc t) (succ n) ⇒ consOk t)

/-- **(I2)** `lenc t = 0 ⇒ t = nil`. **NO es un axioma de la teoría.** -/
abbrev Inv2 : Prop := ∀ t : Term, Prf (Formula.eq (lenc t) zero ⇒ Formula.eq t nil)

/-- Un paso de «pelado»: de `consOk t` y `lenc t = σ n` sale `lenc (cdrc t) = n`
    (`ax_lenc_cons` + inyectividad del sucesor). Esto SÍ es gratis. -/
theorem PrfH_lenc_cdrc {Γ : List Formula} {t n : Term}
    (hc : PrfH Γ (consOk t)) (hl : PrfH Γ (lenc t =eq succ n)) :
    PrfH Γ (lenc (cdrc t) =eq n) :=
  PrfH.mp _ _ _ (prf_to_prfH (prf_succ_inj (lenc (cdrc t)) n) _)
    (PrfH_eq_trans
      (PrfH_eq_symm (PrfH_eq_trans (PrfH_congr_lenc hc)
        (prf_to_prfH (prf_lenc_cons (carc t) (cdrc t)) _))) hl)

/-- **EL PUENTE**, derivado de (I1)+(I2): la forma ECUACIONAL implica la de ESPINA. -/
theorem bridge_of_inversions (hI1 : Inv1) (hI2 : Inv2) (wT wTs X : Term) :
    Prf (isTermCodeB wT wTs X ⇒ isTermCodeS wT wTs X) := by
  refine prf_or_elim_imp ?varC ?funcC
  case varC =>
    refine prf_deduction ?_
    let Γ : List Formula := [cOk X (varOkT X)]
    show PrfH Γ (isTermCodeS wT wTs X)
    have hh : PrfH Γ (cOk X (varOkT X)) := prfH_hyp_self _
    have hc : PrfH Γ (consOk X) := PrfH_and_elim_left hh
    have hv : PrfH Γ (varOkT X) := PrfH_and_elim_right hh
    have hcar : PrfH Γ (carc X =eq numeralM 0) := PrfH_and_elim_left hv
    have hlen : PrfH Γ (lenc X =eq numeralM 2) := PrfH_and_elim_right hv
    have h1 : PrfH Γ (lenc (cdrc X) =eq numeralM 1) := PrfH_lenc_cdrc hc hlen
    have hc2 : PrfH Γ (consOk (cdrc X)) :=
      PrfH.mp _ _ _ (prf_to_prfH (hI1 (cdrc X) (numeralM 0)) _) h1
    have h2 : PrfH Γ (lenc (cdrc (cdrc X)) =eq numeralM 0) := PrfH_lenc_cdrc hc2 h1
    have hnil : PrfH Γ (cdrc (cdrc X) =eq nil) :=
      PrfH.mp _ _ _ (prf_to_prfH (hI2 (cdrc (cdrc X))) _) h2
    have hX : PrfH Γ (X =eq varc (carc (cdrc X))) :=
      PrfH_eq_trans hc (PrfH_eq_trans (PrfH_congr_cons_head hcar)
        (PrfH_congr_cons_tail (PrfH_eq_trans hc2 (PrfH_congr_cons_tail hnil))))
    have hnth : PrfH Γ (nthc X (numeralM 1) =eq carc (cdrc X)) :=
      PrfH_eq_trans (PrfH_congr_nthc_lst (numeralM 1) hX)
        (prf_to_prfH (prf_nthc_varc_1 (carc (cdrc X))) _)
    exact PrfH_orL (PrfH_eq_trans hX (PrfH_congr_cons_tail
      (PrfH_congr_cons_head (PrfH_eq_symm hnth))))
  case funcC =>
    refine prf_deduction ?_
    let Γ : List Formula := [cOk X (funcOkT wTs X)]
    show PrfH Γ (isTermCodeS wT wTs X)
    have hh : PrfH Γ (cOk X (funcOkT wTs X)) := prfH_hyp_self _
    have hc : PrfH Γ (consOk X) := PrfH_and_elim_left hh
    have hf : PrfH Γ (funcOkT wTs X) := PrfH_and_elim_right hh
    have hcar : PrfH Γ (carc X =eq numeralM 1) := PrfH_and_elim_left (PrfH_and_elim_left hf)
    have hlen : PrfH Γ (lenc X =eq numeralM 3) := PrfH_and_elim_right (PrfH_and_elim_left hf)
    have hin : PrfH Γ (In (nthc X (numeralM 2)) wTs) := PrfH_and_elim_right hf
    have h1 : PrfH Γ (lenc (cdrc X) =eq numeralM 2) := PrfH_lenc_cdrc hc hlen
    have hc2 : PrfH Γ (consOk (cdrc X)) :=
      PrfH.mp _ _ _ (prf_to_prfH (hI1 (cdrc X) (numeralM 1)) _) h1
    have h2 : PrfH Γ (lenc (cdrc (cdrc X)) =eq numeralM 1) := PrfH_lenc_cdrc hc2 h1
    have hc3 : PrfH Γ (consOk (cdrc (cdrc X))) :=
      PrfH.mp _ _ _ (prf_to_prfH (hI1 (cdrc (cdrc X)) (numeralM 0)) _) h2
    have h3 : PrfH Γ (lenc (cdrc (cdrc (cdrc X))) =eq numeralM 0) := PrfH_lenc_cdrc hc3 h2
    have hnil : PrfH Γ (cdrc (cdrc (cdrc X)) =eq nil) :=
      PrfH.mp _ _ _ (prf_to_prfH (hI2 (cdrc (cdrc (cdrc X)))) _) h3
    have hX : PrfH Γ (X =eq funcc (carc (cdrc X)) (carc (cdrc (cdrc X)))) :=
      PrfH_eq_trans hc (PrfH_eq_trans (PrfH_congr_cons_head hcar)
        (PrfH_congr_cons_tail (PrfH_eq_trans hc2 (PrfH_congr_cons_tail
          (PrfH_eq_trans hc3 (PrfH_congr_cons_tail hnil))))))
    have hn1 : PrfH Γ (nthc X (numeralM 1) =eq carc (cdrc X)) :=
      PrfH_eq_trans (PrfH_congr_nthc_lst (numeralM 1) hX)
        (prf_to_prfH (prf_nthc_funcc_1 (carc (cdrc X)) (carc (cdrc (cdrc X)))) _)
    have hn2 : PrfH Γ (nthc X (numeralM 2) =eq carc (cdrc (cdrc X))) :=
      PrfH_eq_trans (PrfH_congr_nthc_lst (numeralM 2) hX)
        (prf_to_prfH (prf_nthc_funcc_2 (carc (cdrc X)) (carc (cdrc (cdrc X)))) _)
    refine PrfH_orR (PrfH_and_intro ?_ hin)
    exact PrfH_eq_trans hX (PrfH_eq_trans
      (PrfH_congr_cons_tail (PrfH_congr_cons_tail
        (PrfH_congr_cons_head (PrfH_eq_symm hn2))))
      (PrfH_congr_cons_tail (PrfH_congr_cons_head (PrfH_eq_symm hn1))))

/-- **LA MEDIDA FINAL de la mitad `wT`**: con la forma ECUACIONAL intacta, la clausura bajo
    `liftc zero` sale **exactamente** módulo (I1)+(I2) — nada más. -/
theorem lift_isTermCodeB_modulo_inversion (hI1 : Inv1) (hI2 : Inv2)
    (wT wTs W'T W'Ts X : Term)
    (hTs : ∀ u : Term, Prf (In u wTs ⇒ In (liftsc zero u) W'Ts)) :
    Prf (isTermCodeB wT wTs X ⇒ isTermCodeB W'T W'Ts (liftc zero X)) :=
  impT (bridge_of_inversions hI1 hI2 wT wTs X)
    (impT (lift_isTermCodeS wT wTs W'T W'Ts X hTs)
      (prf_isTermCodeS_imp_isTermCodeB W'T W'Ts (liftc zero X)))

/-! ## 11 · SUBIR AL PAR (`pairOk`) — el transporte POR ÍNDICE

    `prf_pairOk_gen` (`sondeos/DiscriminaEcuacional.lean` §4) ensambla `pairOk p` a partir de
    (i) `lenc (carc p) = n̄`, (ii) `lenc (cdrc p) = m̄` y (iii) los hechos POR ÍNDICE
    `isTermCodeB (carc p) (cdrc p) (nthc (carc p) k̄)`. Aquí se producen las tres piezas para
    el par IMAGEN, que es literal:  `p' = cons (objList (LT.map (liftc 0))) (objList (LTs.map (liftsc 0)))`. -/

def nthTerm : List Term → Nat → Term
  | [],     _     => nil
  | a :: _, 0     => a
  | _ :: L, k + 1 => nthTerm L k

theorem nthTerm_map (f : Term → Term) : ∀ (L : List Term) (k : Nat),
    k < L.length → nthTerm (L.map f) k = f (nthTerm L k)
  | [],     k,     h => absurd h (by simp)
  | a :: L, 0,     _ => rfl
  | a :: L, k + 1, h => nthTerm_map f L k (by simpa using h)

/-- (i)+(ii): la longitud de una lista literal es su numeral. -/
theorem prf_lenc_objList : ∀ L : List Term, Prf (lenc (objList L) =eq numeralM L.length)
  | []     => prf_lenc_nil
  | a :: L => prf_eq_trans (prf_lenc_cons a (objList L))
                (prf_eq_congr_succ (prf_lenc_objList L))

/-- (iii): la casilla `k` de una lista literal es su `k`-ésimo elemento. -/
theorem prf_nthc_objList : ∀ (L : List Term) (k : Nat), k < L.length →
    Prf (nthc (objList L) (numeralM k) =eq nthTerm L k)
  | [],     k,     h => absurd h (by simp)
  | a :: L, 0,     _ => prf_nthc_zero a (objList L)
  | a :: L, k + 1, h => by
      show Prf (nthc (cons a (objList L)) (succ (numeralM k)) =eq nthTerm L k)
      exact prf_eq_trans (prf_nthc_succ a (objList L) (numeralM k))
        (prf_nthc_objList L k (by simpa using h))

theorem prf_congr_isTermCodeS {wT wTs X₁ X₂ : Term} (h : Prf (X₁ =eq X₂))
    (hN : Prf (isTermCodeS wT wTs X₁)) : Prf (isTermCodeS wT wTs X₂) := by
  let f : Formula := isTermCodeS (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = isTermCodeS wT wTs s := by
    intro s
    simp only [f, isTermCodeS, land, lor, In, varc, funcc, nthc, cons, nil, zero, succ,
      substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, substTerm_numeralM, if_true]
  exact (hS X₂) ▸ prf_leibniz_subst (A := f) h ((hS X₁) ▸ hN)

theorem prf_congr_isTermsCodeB {wT wTs X₁ X₂ : Term} (h : Prf (X₁ =eq X₂))
    (hN : Prf (isTermsCodeB wT wTs X₁)) : Prf (isTermsCodeB wT wTs X₂) := by
  let f : Formula := isTermsCodeB (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = isTermsCodeB wT wTs s := by
    intro s
    simp only [f, isTermsCodeB, cOk, consOk, land, lor, In, carc, cdrc, cons, nil, zero,
      substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS X₂) ▸ prf_leibniz_subst (A := f) h ((hS X₁) ▸ hN)

/-- **Transporte POR ÍNDICE, mitad `wT`.** Exactamente la premisa (iii) que
    `prf_pairOk_gen` consume, ya trasladada al par IMAGEN. -/
theorem lift_index_T (LT LTs : List Term) (k : Nat) (hk : k < LT.length)
    (h : Prf (isTermCodeS (objList LT) (objList LTs) (nthc (objList LT) (numeralM k)))) :
    Prf (isTermCodeS (objList (LT.map (liftc zero))) (objList (LTs.map (liftsc zero)))
          (nthc (objList (LT.map (liftc zero))) (numeralM k))) := by
  have h1 := prf_mp (lift_isTermCodeS (objList LT) (objList LTs)
    (objList (LT.map (liftc zero))) (objList (LTs.map (liftsc zero)))
    (nthc (objList LT) (numeralM k)) (prf_mapsTs_objList LTs)) h
  have e1 := prf_nthc_objList (LT.map (liftc zero)) k (by simpa using hk)
  rw [nthTerm_map (liftc zero) LT k hk] at e1
  have he : Prf (nthc (objList (LT.map (liftc zero))) (numeralM k)
      =eq liftc zero (nthc (objList LT) (numeralM k))) :=
    prf_eq_trans e1 (prf_congr_liftc (prf_eq_symm (prf_nthc_objList LT k hk)))
  exact prf_congr_isTermCodeS (prf_eq_symm he) h1

/-- **Transporte POR ÍNDICE, mitad `wTs`.** Aquí el predicado NO se toca: es
    `isTermsCodeB` tal cual. -/
theorem lift_index_Ts (LT LTs : List Term) (k : Nat) (hk : k < LTs.length)
    (h : Prf (isTermsCodeB (objList LT) (objList LTs) (nthc (objList LTs) (numeralM k)))) :
    Prf (isTermsCodeB (objList (LT.map (liftc zero))) (objList (LTs.map (liftsc zero)))
          (nthc (objList (LTs.map (liftsc zero))) (numeralM k))) := by
  have h1 := prf_mp (lift_isTermsCodeB (objList LT) (objList LTs)
    (objList (LT.map (liftc zero))) (objList (LTs.map (liftsc zero)))
    (nthc (objList LTs) (numeralM k))
    (prf_mapsT_objList LT) (prf_mapsTs_objList LTs)) h
  have e1 := prf_nthc_objList (LTs.map (liftsc zero)) k (by simpa using hk)
  rw [nthTerm_map (liftsc zero) LTs k hk] at e1
  have he : Prf (nthc (objList (LTs.map (liftsc zero))) (numeralM k)
      =eq liftsc zero (nthc (objList LTs) (numeralM k))) :=
    prf_eq_trans e1 (prf_congr_liftsc (prf_eq_symm (prf_nthc_objList LTs k hk)))
  exact prf_congr_isTermsCodeB (prf_eq_symm he) h1

/-- Las longitudes del par IMAGEN coinciden con las del original (premisas (i)/(ii)). -/
theorem lenc_image_T (LT : List Term) :
    Prf (lenc (objList (LT.map (liftc zero))) =eq numeralM LT.length) := by
  have := prf_lenc_objList (LT.map (liftc zero))
  simpa using this

theorem lenc_image_Ts (LTs : List Term) :
    Prf (lenc (objList (LTs.map (liftsc zero))) =eq numeralM LTs.length) := by
  have := prf_lenc_objList (LTs.map (liftsc zero))
  simpa using this

end LiftMap

/-! ## 12 · FOOTPRINT -/

#print axioms LiftMap.lift_isTermsCodeB
#print axioms LiftMap.lift_isTermCodeS
#print axioms LiftMap.prf_isTermCodeS_imp_isTermCodeB
#print axioms LiftMap.prf_liftsc_objList
#print axioms LiftMap.prf_mapsT_objList
#print axioms LiftMap.prf_mapsTs_objList
#print axioms LiftMap.lift_par_objList
#print axioms LiftMap.lift_par_objList_s
#print axioms LiftMap.bridge_of_inversions
#print axioms LiftMap.lift_isTermCodeB_modulo_inversion
#print axioms LiftMap.lift_index_T
#print axioms LiftMap.lift_index_Ts
#print axioms LiftMap.lenc_image_T
#print axioms LiftMap.lenc_image_Ts
