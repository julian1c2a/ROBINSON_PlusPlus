/-
# PILOTO DE CLAUSURA — ¿el testigo de parseo se cierra bajo `substfc`?

Fichero AUTOCONTENIDO (`import ROBINSON_PlusPlus.Meta` y nada más).

    lake env lean Probe/ClausuraSubstfc.lean

Mide el riesgo de la vía (2) (buena‑formación por TESTIGO DE PARSEO): río abajo los 7 tags de
`lineWF` podrían exigir que el RESULTADO de `substfc` vuelva a reconocerse como código de
fórmula. Aquí se toma el disyunto MÁXIMO (tag 5, `implc`, dos hijos de FÓRMULA) con `v t X wF`
ABSTRACTOS y se AVERIGUA qué forma se ve obligado a tener el testigo imagen `W'`.

## VEREDICTO: desenlace (b), y está DEMOSTRADO, no conjeturado

* (a) `W' := wF` es **ABSURDO**: `identity_witness_absurd` deriva `⊢ substfc v t y ≐ y`
  para todo `y`, o sea que la sustitución sería la identidad.
* `W'` está **FORZADO** a contener la imagen elemento a elemento (`forced_map_tag5`), y
  además la imagen bajo los parámetros DESPLAZADOS (`forced_map_tag6`), y además el
  SUSTITUYENDO `t` entero (`forced_substituend`). Los tres, con `w` ABSTRACTA.
* El map sobre lista ABSTRACTA **sí es construible**: el cálculo objeto tiene inducción de
  listas (`Prf.listInd`), así que las ecuaciones nil/cons bastan. `map_mem_tc` lo demuestra
  **net‑0 y sin hipótesis** reusando `ax_substtsc_nil/cons`: la mitad de TÉRMINOS es GRATIS.
  `map_mem_fc` lo repite para fórmulas con **UNA** ecuación hipotética (`ax_substfsc_cons`).
* Obstrucción EXTRA no anticipada: la cláusula de forma `carc ≐ k̄ ∧ lenc ≐ n̄` **no
  reconstruye** `X` (no hay axioma de descomposición de listas). Hay que REFORMULARLA como
  ecuación explícita (`shapeImpl`), que es un FORTALECIMIENTO (`prf_shapeImpl_strengthens`)
  y **cuesta 0 axiomas**.
* `Wtwo` (concat de las dos imágenes) cierra el paso UNITARIO (tags 5 y 6), pero **no es
  punto fijo**: `forced_shift2` fuerza el piso siguiente de la torre de desplazamientos.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.InAxiomsCodePrf ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstArith

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ClausuraSubstfc

/-! ## 0 · La PARTICIÓN, copiada LITERALMENTE de `Probe/PilotoParticion.lean` §1 y §17 -/

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def unOkF (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 2)))
       (In (nthc X (numeralM 1)) w)

def binOkF (wA wB X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (land (In (nthc X (numeralM 1)) wA) (In (nthc X (numeralM 2)) wB))

/-! ## 1 · Aritmética de listas concretas (copia de `PilotoParticion` §16) -/

theorem prf_lenc_c1 (a : Term) : Prf (lenc (cons a nil) =eq numeralM 1) :=
  prf_eq_trans (prf_lenc_cons a nil) (prf_eq_congr_succ prf_lenc_nil)

theorem prf_lenc_c2 (a b : Term) : Prf (lenc (cons a (cons b nil)) =eq numeralM 2) :=
  prf_eq_trans (prf_lenc_cons a (cons b nil)) (prf_eq_congr_succ (prf_lenc_c1 b))

theorem prf_lenc_c3 (a b c : Term) :
    Prf (lenc (cons a (cons b (cons c nil))) =eq numeralM 3) :=
  prf_eq_trans (prf_lenc_cons a (cons b (cons c nil))) (prf_eq_congr_succ (prf_lenc_c2 b c))

theorem prf_nthc_c1 (a b c : Term) : Prf (nthc (cons a (cons b c)) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b c) (numeralM 0)) (prf_nthc_zero b c)

theorem prf_nthc_c2 (a b c d : Term) :
    Prf (nthc (cons a (cons b (cons c d))) (numeralM 2) =eq c) :=
  prf_eq_trans (prf_nthc_succ a (cons b (cons c d)) (numeralM 1)) (prf_nthc_c1 b c d)

theorem prf_cdrc_cons (a b : Term) : Prf (cdrc (cons a b) =eq b) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax a) b
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) := by
  unfold consOk
  exact prf_eq_symm (prf_eq_trans
    (prf_congr_cons_head (prf_carc_cons a b)) (prf_congr_cons_tail (prf_cdrc_cons a b)))

/-! ## 2 · Congruencias (Leibniz) que hacen falta -/

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_congr_nthc_lst {w₁ w₂ : Term} (i : Term) (h : Prf (w₁ =eq w₂)) :
    Prf (nthc w₁ i =eq nthc w₂ i) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 w₁) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w₁ i) (nthc s i) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS w₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS w₁) ▸ prf_to_prfH (prf_refl (nthc w₁ i)) [])) rfl

theorem prf_congr_In_left {u v w : Term} (h : Prf (u =eq v)) (hin : Prf (In u w)) :
    Prf (In v w) := by
  let f : Formula := In (.var 0) (liftTerm 0 w)
  have hS : ∀ s : Term, substFormula 0 s f = In s w := by
    intro s
    simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS v) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h []) ((hS u) ▸ prf_to_prfH hin [])) rfl

/-- Congruencia en el 3er argumento de `substfc` (el CÓDIGO). -/
theorem PrfH_congr_substfc {Γ : List Formula} {v t x y : Term} (h : PrfH Γ (x =eq y)) :
    PrfH Γ (substfc v t x =eq substfc v t y) := by
  let f : Formula := Formula.eq (substfc (liftTerm 0 v) (liftTerm 0 t) (liftTerm 0 x))
                                (substfc (liftTerm 0 v) (liftTerm 0 t) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (substfc v t x) (substfc v t s) := by
    intro s
    simp only [f, substfc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS y) ▸ PrfH_leibniz_subst (A := f) h ((hS x) ▸ prf_to_prfH (prf_refl (substfc v t x)) Γ)

theorem PrfH_congr_nthc_lst {Γ : List Formula} {w₁ w₂ : Term} (i : Term)
    (h : PrfH Γ (w₁ =eq w₂)) : PrfH Γ (nthc w₁ i =eq nthc w₂ i) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 w₁) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w₁ i) (nthc s i) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS w₂) ▸ PrfH_leibniz_subst (A := f) h ((hS w₁) ▸ prf_to_prfH (prf_refl (nthc w₁ i)) Γ)

theorem PrfH_congr_In_left {Γ : List Formula} {u v w : Term}
    (h : PrfH Γ (u =eq v)) (hin : PrfH Γ (In u w)) : PrfH Γ (In v w) := by
  let f : Formula := In (.var 0) (liftTerm 0 w)
  have hS : ∀ s : Term, substFormula 0 s f = In s w := by
    intro s
    simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS v) ▸ PrfH_leibniz_subst (A := f) h ((hS u) ▸ hin)

/-- Congruencia de `implc` en las DOS casillas, a nivel `PrfH` (sin Leibniz nuevo: `implc`
    es `cons`/`cons`/`cons`). -/
theorem PrfH_congr_implc {Γ : List Formula} {a a' b b' : Term}
    (ha : PrfH Γ (a =eq a')) (hb : PrfH Γ (b =eq b')) :
    PrfH Γ (implc a b =eq implc a' b') := by
  unfold implc
  refine PrfH_eq_trans (PrfH_congr_cons_tail (PrfH_congr_cons_head ha)) ?_
  exact PrfH_congr_cons_tail (PrfH_congr_cons_tail (PrfH_congr_cons_head hb))

/-! # ═══════════════════════════════════════════════════════════════════════════
    ## 3 · LO QUE `W'` SE VE OBLIGADO A SER — el resultado NEGATIVO, y es DEMOSTRADO

    No hace falta especular sobre si `W' := wF` sirve: se DERIVA la forma de `W'`.
    Basta instanciar la clausura en el testigo MÍNIMO `wF := cons y nil` y el código
    `X := implc y y`, ambos legítimos; la conclusión obliga a `substfc v t y ∈ W'`.
    ═══════════════════════════════════════════════════════════════════════════ -/

/-- Si `y` está en el testigo, el testigo reconoce `implc y y` como código de fórmula, tag 5. -/
theorem prf_premisa_tag5 (w y : Term) (hy : Prf (In y w)) :
    Prf (cOk (implc y y) (binOkF w w (implc y y) 5)) := by
  refine prf_and_intro (prf_consOk_cons _ _) (prf_and_intro (prf_and_intro ?_ ?_)
    (prf_and_intro ?_ ?_))
  · exact prf_carc_cons (numeralM 5) (cons y (cons y nil))
  · exact prf_lenc_c3 (numeralM 5) y y
  · exact prf_congr_In_left (prf_eq_symm (prf_nthc_c1 (numeralM 5) y (cons y nil))) hy
  · exact prf_congr_In_left (prf_eq_symm (prf_nthc_c2 (numeralM 5) y y nil)) hy

/-- **FORZAMIENTO (tag 5).** Para CUALQUIER testigo `w`: si la clausura vale para el disyunto
    `implc`, el testigo imagen `W'` contiene `substfc v t y` para TODO `y ∈ w`. Es decir:
    `W'` está obligado a contener la IMAGEN ELEMENTO A ELEMENTO — el desenlace **(b)**. -/
theorem forced_map_tag5 (v t w W' : Term)
    (hclo : ∀ (X : Term),
      Prf (cOk X (binOkF w w X 5) ⇒ cOk (substfc v t X) (binOkF W' W' (substfc v t X) 5)))
    (y : Term) (hy : Prf (In y w)) : Prf (In (substfc v t y) W') := by
  have hcon := prf_mp (hclo (implc y y)) (prf_premisa_tag5 w y hy)
  have hin : Prf (In (nthc (substfc v t (implc y y)) (numeralM 1)) W') :=
    prf_and_elim_left (prf_and_elim_right (prf_and_elim_right hcon))
  have heq : Prf (nthc (substfc v t (implc y y)) (numeralM 1) =eq substfc v t y) :=
    prf_eq_trans (prf_congr_nthc_lst (numeralM 1) (prf_substfc_impl v t y y))
      (prf_nthc_c1 (numeralM 5) (substfc v t y) (cons (substfc v t y) nil))
  exact prf_congr_In_left heq hin

/-- Si `y` está en el testigo, el testigo reconoce `forallc y`, tag 6. -/
theorem prf_premisa_tag6 (w y : Term) (hy : Prf (In y w)) :
    Prf (cOk (forallc y) (unOkF w (forallc y) 6)) := by
  refine prf_and_intro (prf_consOk_cons _ _) (prf_and_intro (prf_and_intro ?_ ?_) ?_)
  · exact prf_carc_cons (numeralM 6) (cons y nil)
  · exact prf_lenc_c2 (numeralM 6) y
  · exact prf_congr_In_left (prf_eq_symm (prf_nthc_c1 (numeralM 6) y nil)) hy

/-- **FORZAMIENTO (tag 6).** El MISMO `W'` está obligado a contener también
    `substfc (σv) (liftc 0 t) y` — la imagen bajo los parámetros DESPLAZADOS, porque `∀`
    incrementa el nivel. Dos familias distintas, un solo `W'`. -/
theorem forced_map_tag6 (v t w W' : Term)
    (hclo : ∀ (X : Term),
      Prf (cOk X (unOkF w X 6) ⇒ cOk (substfc v t X) (unOkF W' (substfc v t X) 6)))
    (y : Term) (hy : Prf (In y w)) : Prf (In (substfc (succ v) (liftc zero t) y) W') := by
  have hcon := prf_mp (hclo (forallc y)) (prf_premisa_tag6 w y hy)
  have hin : Prf (In (nthc (substfc v t (forallc y)) (numeralM 1)) W') :=
    prf_and_elim_right (prf_and_elim_right hcon)
  have heq : Prf (nthc (substfc v t (forallc y)) (numeralM 1)
      =eq substfc (succ v) (liftc zero t) y) :=
    prf_eq_trans (prf_congr_nthc_lst (numeralM 1) (prf_substfc_forall v t y))
      (prf_nthc_c1 (numeralM 6) (substfc (succ v) (liftc zero t) y) nil)
  exact prf_congr_In_left heq hin

/-! ### 3bis · El desenlace (a) — «`W' := wF` sirve» — REFUTADO, no meramente no probado -/

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

theorem prf_eq_of_in_singleton {z y : Term} (h : Prf (In z (cons y nil))) : Prf (z =eq y) := by
  have hor : Prf (lor (z =eq y) (In z nil)) :=
    prf_mp (prf_and_elim_left (prf_in_cons_iff z y nil)) h
  have h1 : Prf ((z =eq y) ⇒ (z =eq y)) := prf_deduction (prfH_hyp_self _)
  have h2 : Prf (In z nil ⇒ (z =eq y)) :=
    prf_deduction (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq (z =eq y)))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_not_in_nil z) _) (prfH_hyp_self _)))
  exact prf_mp (prf_or_elim_imp h1 h2) hor

/-- **(a) ES ABSURDO.** Si el testigo ORIGINAL valiese también para la imagen, la teoría
    probaría que `substfc` es la IDENTIDAD sobre todo código: `⊢ substfc v t y ≐ y`. -/
theorem identity_witness_absurd (v t : Term)
    (hclo : ∀ (w X : Term),
      Prf (cOk X (binOkF w w X 5) ⇒ cOk (substfc v t X) (binOkF w w (substfc v t X) 5)))
    (y : Term) : Prf (substfc v t y =eq y) := by
  have hcon := prf_mp (hclo (cons y nil) (implc y y))
    (prf_premisa_tag5 (cons y nil) y (prf_in_cons_head y nil))
  have hin : Prf (In (nthc (substfc v t (implc y y)) (numeralM 1)) (cons y nil)) :=
    prf_and_elim_left (prf_and_elim_right (prf_and_elim_right hcon))
  have heq : Prf (nthc (substfc v t (implc y y)) (numeralM 1) =eq substfc v t y) :=
    prf_eq_trans (prf_congr_nthc_lst (numeralM 1) (prf_substfc_impl v t y y))
      (prf_nthc_c1 (numeralM 5) (substfc v t y) (cons (substfc v t y) nil))
  exact prf_eq_of_in_singleton (prf_congr_In_left heq hin)

/-! # ═══════════════════════════════════════════════════════════════════════════
    ## 4 · LA SEGUNDA OBSTRUCCIÓN: la CLÁUSULA DE FORMA `carc`/`lenc` NO RECONSTRUYE `X`

    Para disparar `ax_substfc_impl` hace falta `X ≐ implc A B` LITERAL. Con `X` abstracto
    el disyunto de `PilotoParticion` sólo da `consOk X ∧ carc X ≐ 5̄ ∧ lenc X ≐ 3̄`, y de ahí
    NO sale la forma: `consOk` sólo desmonta el nodo UNA vez, y no hay axioma
    `lenc y ≐ σn → y ≐ cons (carc y) (cdrc y)` (la única vía de descomposición es `consOk`
    mismo, que habría que exigir en CADA nivel de la espina, más `cdrc³ X ≐ nil`).

    La salida es una REFORMULACIÓN (0 axiomas nuevos), exactamente el estilo de los esquemas
    `lineWF` de `Minimal/Axioms.lean` (`carc line ≐ implc (nthc line 2̄) …`). -/

/-- Cláusula de forma REFORMULADA: la ecuación explícita, no `carc`+`lenc`. -/
def shapeImpl (X : Term) : Formula :=
  Formula.eq X (implc (nthc X (numeralM 1)) (nthc X (numeralM 2)))

def implOkS (w X : Term) : Formula :=
  land (shapeImpl X) (land (In (nthc X (numeralM 1)) w) (In (nthc X (numeralM 2)) w))

/-- La reformulación la SATISFACEN los códigos reales. -/
theorem prf_shapeImpl_implc (a b : Term) : Prf (shapeImpl (implc a b)) :=
  prf_eq_symm (prf_congr_implc
    (prf_nthc_c1 (numeralM 5) a (cons b nil)) (prf_nthc_c2 (numeralM 5) a b nil))

/-- La reformulación es un FORTALECIMIENTO: implica la cláusula vieja entera (`consOk`
    incluido) ⇒ no se pierde poder discriminante frente al código basura. -/
theorem prf_shapeImpl_strengthens (X : Term) :
    Prf (shapeImpl X ⇒ land (land (Formula.eq (carc X) (numeralM 5))
                                  (Formula.eq (lenc X) (numeralM 3))) (consOk X)) := by
  refine prf_deduction ?_
  let A : Term := nthc X (numeralM 1)
  let B : Term := nthc X (numeralM 2)
  let f : Formula :=
    land (land (Formula.eq (carc (.var 0)) (numeralM 5)) (Formula.eq (lenc (.var 0)) (numeralM 3)))
         (Formula.eq (.var 0) (cons (carc (.var 0)) (cdrc (.var 0))))
  have hS : ∀ s : Term, substFormula 0 s f =
      land (land (Formula.eq (carc s) (numeralM 5)) (Formula.eq (lenc s) (numeralM 3)))
           (consOk s) := by
    intro s
    simp only [f, consOk, land, carc, cdrc, lenc, cons, substFormula, substTerm, substTerms,
      substTerm_numeralM, if_true]
  have hbase : PrfH [shapeImpl X] (substFormula 0 (implc A B) f) := by
    rw [hS]
    exact prf_to_prfH (prf_and_intro
      (prf_and_intro (prf_carc_cons (numeralM 5) (cons A (cons B nil)))
        (prf_lenc_c3 (numeralM 5) A B)) (prf_consOk_cons _ _)) _
  have hres : PrfH [shapeImpl X] (substFormula 0 X f) :=
    PrfH_leibniz_subst (A := f) (PrfH_eq_symm (prfH_hyp_self (shapeImpl X))) hbase
  rw [hS] at hres
  exact hres

/-! ## 5 · LA SUFICIENCIA: con la forma reformulada, el ÚNICO residuo es el MAP -/

/-- **La clausura del tag 5 sale ENTERA de una sola hipótesis: el MAP.** `v t X w W'` son
    todos ABSTRACTOS. Nótese que `hmap` es exactamente lo que §3 demostró NECESARIO. -/
theorem closure_tag5_of_map (v t X w W' : Term)
    (hmap : ∀ y : Term, Prf (In y w ⇒ In (substfc v t y) W')) :
    Prf (implOkS w X ⇒ implOkS W' (substfc v t X)) := by
  refine prf_deduction ?_
  let Γ : List Formula := [implOkS w X]
  let A : Term := nthc X (numeralM 1)
  let B : Term := nthc X (numeralM 2)
  let X' : Term := substfc v t X
  let A' : Term := substfc v t A
  let B' : Term := substfc v t B
  have h : PrfH Γ (implOkS w X) := prfH_hyp_self _
  have hsh : PrfH Γ (Formula.eq X (implc A B)) := PrfH_and_elim_left h
  have hin1 : PrfH Γ (In A w) := PrfH_and_elim_left (PrfH_and_elim_right h)
  have hin2 : PrfH Γ (In B w) := PrfH_and_elim_right (PrfH_and_elim_right h)
  have h4 : PrfH Γ (Formula.eq X' (implc A' B')) :=
    PrfH_eq_trans (PrfH_congr_substfc hsh) (prf_to_prfH (prf_substfc_impl v t A B) Γ)
  have h5 : PrfH Γ (Formula.eq (nthc X' (numeralM 1)) A') :=
    PrfH_eq_trans (PrfH_congr_nthc_lst (numeralM 1) h4)
      (prf_to_prfH (prf_nthc_c1 (numeralM 5) A' (cons B' nil)) Γ)
  have h6 : PrfH Γ (Formula.eq (nthc X' (numeralM 2)) B') :=
    PrfH_eq_trans (PrfH_congr_nthc_lst (numeralM 2) h4)
      (prf_to_prfH (prf_nthc_c2 (numeralM 5) A' B' nil) Γ)
  refine PrfH_and_intro ?_ (PrfH_and_intro ?_ ?_)
  · exact PrfH_eq_trans h4 (PrfH_congr_implc (PrfH_eq_symm h5) (PrfH_eq_symm h6))
  · exact PrfH_congr_In_left (PrfH_eq_symm h5)
      (PrfH.mp _ _ _ (prf_to_prfH (hmap A) Γ) hin1)
  · exact PrfH_congr_In_left (PrfH_eq_symm h6)
      (PrfH.mp _ _ _ (prf_to_prfH (hmap B) Γ) hin2)

/-! # ═══════════════════════════════════════════════════════════════════════════
    ## 6 · ¿CUÁNTO CUESTA EL MAP? — la mitad de TÉRMINOS sale GRATIS

    `substtsc` YA es el map de `substtc` (ax_substtsc_nil/cons). Y el cálculo objeto TIENE
    inducción de listas (`Prf.listInd` / `prf_list_induction`), así que las ecuaciones
    nil/cons bastan para el lema de pertenencia sobre lista ABSTRACTA. Se demuestra aquí,
    net‑0 y sin ninguna hipótesis: es el PATRÓN que la mitad de FÓRMULAS tendría que copiar.
    ═══════════════════════════════════════════════════════════════════════════ -/

theorem PrfH_congr_substtc {Γ : List Formula} {v t x y : Term} (h : PrfH Γ (x =eq y)) :
    PrfH Γ (substtc v t x =eq substtc v t y) := by
  let f : Formula := Formula.eq (substtc (liftTerm 0 v) (liftTerm 0 t) (liftTerm 0 x))
                                (substtc (liftTerm 0 v) (liftTerm 0 t) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (substtc v t x) (substtc v t s) := by
    intro s
    simp only [f, substtc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS y) ▸ PrfH_leibniz_subst (A := f) h ((hS x) ▸ prf_to_prfH (prf_refl (substtc v t x)) Γ)

/-- **EL MAP DE TÉRMINOS, GRATIS.** `w` ABSTRACTA. Inducción de listas + las 2 ecuaciones
    ya axiomatizadas de `substtsc`. Footprint: la base sancionada, cero axiomas nuevos. -/
theorem map_mem_tc (v t y : Term) : ∀ w : Term,
    Prf (In y w ⇒ In (substtc v t y) (substtsc v t w)) := by
  have key : Prf (Formula.forall (Formula.impl (In (liftTerm 0 y) (.var 0))
      (In (liftTerm 0 (substtc v t y))
          (substtsc (liftTerm 0 v) (liftTerm 0 t) (.var 0))))) := by
    refine prf_list_induction _ ?base ?step
    · have hb : Prf (Formula.impl (In y nil) (In (substtc v t y) (substtsc v t nil))) :=
        prf_deduction (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
          (PrfH.mp _ _ _ (prf_to_prfH (prf_not_in_nil y) _) (prfH_hyp_self _)))
      simpa only [substFormula, substTerm, substTerms, In, substtc, substtsc, nil, cons, zero,
        FOL.substTerm_liftTerm, if_true] using hb
    · refine Prf.gen _ (Prf.gen _ ?_)
      simp only [liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms, In,
        cons, substtc, substtsc, norm21, FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      let Y : Term := liftTerm 1 (liftTerm 0 y)
      let V : Term := liftTerm 1 (liftTerm 0 v)
      let T : Term := liftTerm 1 (liftTerm 0 t)
      refine prf_deduction (deduction_aux ?_
        (In Y (cons (.var 1) (.var 0)))
        [Formula.impl (In Y (.var 0)) (In (substtc V T Y) (substtsc V T (.var 0)))] rfl)
      let IHf : Formula :=
        Formula.impl (In Y (.var 0)) (In (substtc V T Y) (substtsc V T (.var 0)))
      let Ah : Formula := In Y (cons (.var 1) (.var 0))
      have hsplit : PrfH [Ah, IHf] (lor (Y =eq (.var 1)) (In Y (.var 0))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_in_cons_iff Y (.var 1) (.var 0))) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      refine PrfH_or_elim hsplit ?_ ?_
      · refine PrfH_eq_subst_in
          (PrfH_eq_symm (prf_to_prfH (prf_substtsc_cons V T (.var 1) (.var 0)) _)) ?_
        exact PrfH_congr_In_left
          (PrfH_eq_symm (PrfH_congr_substtc (PrfH.hyp _ _ (List.Mem.head _))))
          (prf_to_prfH (prf_in_cons_head (substtc V T (.var 1)) (substtsc V T (.var 0))) _)
      · refine PrfH_eq_subst_in
          (PrfH_eq_symm (prf_to_prfH (prf_substtsc_cons V T (.var 1) (.var 0)) _)) ?_
        exact PrfH_in_cons_tail _
          (PrfH.mp _ _ _ (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
            (PrfH.hyp _ _ (List.Mem.head _)))
  intro w
  have hL := prf_spec key w
  simpa only [substFormula, substTerm, substTerms, In, substtc, substtsc,
    FOL.substTerm_liftTerm, if_true] using hL

/-! # ═══════════════════════════════════════════════════════════════════════════
    ## 7 · LA MITAD DE FÓRMULAS: el MISMO patrón, con UN símbolo y UNA ecuación nuevos

    `substfsc` NO existe (`Term.func "substfsc"` es sólo un constructor de término: aquí no
    se añade ningún axioma de Lean ni de la teoría). Sus ecuaciones se toman como HIPÓTESIS
    y se mide cuáles hacen falta: para la PERTENENCIA basta la de `cons`.
    ═══════════════════════════════════════════════════════════════════════════ -/

/-- El map de `substfc` sobre listas de códigos de FÓRMULA. Símbolo NUEVO, sin axiomas. -/
def substfsc (v t l : Term) : Term := Term.func "substfsc" [v, t, l]

/-- La ecuación `cons` que HARÍA FALTA axiomatizar, en la forma cerrada que tendría en
    `Minimal/Axioms.lean` (espejo EXACTO de `ax_substtsc_cons`). -/
def ax_substfsc_cons : Formula :=
  forall_4 (substfsc (.var 3) (.var 2) (cons (.var 1) (.var 0))
    =eq cons (substfc (.var 3) (.var 2) (.var 1)) (substfsc (.var 3) (.var 2) (.var 0)))

/-- La ecuación `nil` que la acompañaría (NO la usa el lema de pertenencia). -/
def ax_substfsc_nil : Formula :=
  forall_2 (substfsc (.var 1) (.var 0) nil =eq nil)

/-- **EL MAP DE FÓRMULAS, con UNA sola ecuación hipotética.** Misma inducción de listas que
    `map_mem_tc`; `w` ABSTRACTA. La ecuación `nil` NO se usa (la base sale por explosión). -/
theorem map_mem_fc (v t y : Term)
    (hcons : ∀ (v' t' a b : Term),
      Prf (substfsc v' t' (cons a b) =eq cons (substfc v' t' a) (substfsc v' t' b))) :
    ∀ w : Term, Prf (In y w ⇒ In (substfc v t y) (substfsc v t w)) := by
  have key : Prf (Formula.forall (Formula.impl (In (liftTerm 0 y) (.var 0))
      (In (liftTerm 0 (substfc v t y))
          (substfsc (liftTerm 0 v) (liftTerm 0 t) (.var 0))))) := by
    refine prf_list_induction _ ?base ?step
    · have hb : Prf (Formula.impl (In y nil) (In (substfc v t y) (substfsc v t nil))) :=
        prf_deduction (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
          (PrfH.mp _ _ _ (prf_to_prfH (prf_not_in_nil y) _) (prfH_hyp_self _)))
      simpa only [substFormula, substTerm, substTerms, In, substfc, substfsc, nil, cons, zero,
        FOL.substTerm_liftTerm, if_true] using hb
    · refine Prf.gen _ (Prf.gen _ ?_)
      simp only [liftFormula, liftTerm, liftTerms, substFormula, substTerm, substTerms, In,
        cons, substfc, substfsc, norm21, FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
      let Y : Term := liftTerm 1 (liftTerm 0 y)
      let V : Term := liftTerm 1 (liftTerm 0 v)
      let T : Term := liftTerm 1 (liftTerm 0 t)
      refine prf_deduction (deduction_aux ?_
        (In Y (cons (.var 1) (.var 0)))
        [Formula.impl (In Y (.var 0)) (In (substfc V T Y) (substfsc V T (.var 0)))] rfl)
      let IHf : Formula :=
        Formula.impl (In Y (.var 0)) (In (substfc V T Y) (substfsc V T (.var 0)))
      let Ah : Formula := In Y (cons (.var 1) (.var 0))
      have hsplit : PrfH [Ah, IHf] (lor (Y =eq (.var 1)) (In Y (.var 0))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_in_cons_iff Y (.var 1) (.var 0))) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      refine PrfH_or_elim hsplit ?_ ?_
      · refine PrfH_eq_subst_in
          (PrfH_eq_symm (prf_to_prfH (hcons V T (.var 1) (.var 0)) _)) ?_
        exact PrfH_congr_In_left
          (PrfH_eq_symm (PrfH_congr_substfc (PrfH.hyp _ _ (List.Mem.head _))))
          (prf_to_prfH (prf_in_cons_head (substfc V T (.var 1)) (substfsc V T (.var 0))) _)
      · refine PrfH_eq_subst_in
          (PrfH_eq_symm (prf_to_prfH (hcons V T (.var 1) (.var 0)) _)) ?_
        exact PrfH_in_cons_tail _
          (PrfH.mp _ _ _ (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
            (PrfH.hyp _ _ (List.Mem.head _)))
  intro w
  have hL := prf_spec key w
  simpa only [substFormula, substTerm, substTerms, In, substfc, substfsc,
    FOL.substTerm_liftTerm, if_true] using hL

/-- **CIERRE DEL TAG 5**, todo ABSTRACTO, con el testigo imagen EXPLÍCITO `substfsc v t w`. -/
theorem closure_tag5_substfsc (v t X w : Term)
    (hcons : ∀ (v' t' a b : Term),
      Prf (substfsc v' t' (cons a b) =eq cons (substfc v' t' a) (substfsc v' t' b))) :
    Prf (implOkS w X ⇒ implOkS (substfsc v t w) (substfc v t X)) :=
  closure_tag5_of_map v t X w (substfsc v t w) (fun y => map_mem_fc v t y hcons w)

/-! ## 8 · EL TAG 6 (`forallc`) — mismo cierre, pero con los parámetros DESPLAZADOS -/

def shapeAll (X : Term) : Formula := Formula.eq X (forallc (nthc X (numeralM 1)))

def allOkS (w X : Term) : Formula := land (shapeAll X) (In (nthc X (numeralM 1)) w)

theorem PrfH_congr_forallc {Γ : List Formula} {a a' : Term} (h : PrfH Γ (a =eq a')) :
    PrfH Γ (forallc a =eq forallc a') := by
  unfold forallc
  exact PrfH_congr_cons_tail (PrfH_congr_cons_head h)

theorem closure_tag6_of_map (v t X w W' : Term)
    (hmap : ∀ y : Term, Prf (In y w ⇒ In (substfc (succ v) (liftc zero t) y) W')) :
    Prf (allOkS w X ⇒ allOkS W' (substfc v t X)) := by
  refine prf_deduction ?_
  let Γ : List Formula := [allOkS w X]
  let A : Term := nthc X (numeralM 1)
  let X' : Term := substfc v t X
  let A'' : Term := substfc (succ v) (liftc zero t) A
  have h : PrfH Γ (allOkS w X) := prfH_hyp_self _
  have hsh : PrfH Γ (Formula.eq X (forallc A)) := PrfH_and_elim_left h
  have hin : PrfH Γ (In A w) := PrfH_and_elim_right h
  have h4 : PrfH Γ (Formula.eq X' (forallc A'')) :=
    PrfH_eq_trans (PrfH_congr_substfc hsh) (prf_to_prfH (prf_substfc_forall v t A) Γ)
  have h5 : PrfH Γ (Formula.eq (nthc X' (numeralM 1)) A'') :=
    PrfH_eq_trans (PrfH_congr_nthc_lst (numeralM 1) h4)
      (prf_to_prfH (prf_nthc_c1 (numeralM 6) A'' nil) Γ)
  refine PrfH_and_intro ?_ ?_
  · exact PrfH_eq_trans h4 (PrfH_congr_forallc (PrfH_eq_symm h5))
  · exact PrfH_congr_In_left (PrfH_eq_symm h5) (PrfH.mp _ _ _ (prf_to_prfH (hmap A) Γ) hin)

/-! ## 9 · UN SOLO `W'` PARA LOS DOS TAGS: la CONCATENACIÓN de las DOS imágenes

    Los tags con binder (`∀`/`∃`) piden la imagen bajo `(σv, liftc 0 t)`; los demás, bajo
    `(v,t)`. Para el paso UNITARIO basta `concat` (axiomatizado: `ax_L3_in_concat`). -/

noncomputable def Wtwo (v t w : Term) : Term :=
  concat (substfsc v t w) (substfsc (succ v) (liftc zero t) w)

theorem closure_tag5_Wtwo (v t X w : Term)
    (hcons : ∀ (v' t' a b : Term),
      Prf (substfsc v' t' (cons a b) =eq cons (substfc v' t' a) (substfsc v' t' b))) :
    Prf (implOkS w X ⇒ implOkS (Wtwo v t w) (substfc v t X)) :=
  closure_tag5_of_map v t X w (Wtwo v t w) (fun y =>
    impT (map_mem_fc v t y hcons w)
      (prf_In_mono_right_imp (substfc v t y)
        (substfsc (succ v) (liftc zero t) w) (substfsc v t w)))

theorem closure_tag6_Wtwo (v t X w : Term)
    (hcons : ∀ (v' t' a b : Term),
      Prf (substfsc v' t' (cons a b) =eq cons (substfc v' t' a) (substfsc v' t' b))) :
    Prf (allOkS w X ⇒ allOkS (Wtwo v t w) (substfc v t X)) :=
  closure_tag6_of_map v t X w (Wtwo v t w) (fun y =>
    impT (map_mem_fc (succ v) (liftc zero t) y hcons w)
      (prf_In_mono_imp (substfc (succ v) (liftc zero t) y)
        (substfsc (succ v) (liftc zero t) w) (substfsc v t w)))

/-- El AXIOMA cerrado da exactamente la hipótesis usada: la cuenta es **1 axioma nuevo**
    (+ el de `nil`, que la pertenencia no necesita pero sí la aritmética del testigo). -/
theorem hcons_of_ax (hax : Prf ax_substfsc_cons) :
    ∀ (v t a b : Term),
      Prf (substfsc v t (cons a b) =eq cons (substfc v t a) (substfsc v t b)) := by
  intro v t a b
  have hh := prf_spec (prf_spec (prf_spec (prf_spec hax v) t) a) b
  simp [ax_substfsc_cons, substFormula, substTerm, substTerms, substfsc, substfc, cons, nil,
    zero, succ, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, substTerm_liftLiftLift,
    substTerms_liftLiftLift] at hh
  exact hh

/-! ## 10 · LA TORRE: `Wtwo` NO ES UN PUNTO FIJO

    Basta reinstanciar el forzamiento del tag 6 en los parámetros ya desplazados: el testigo
    de la IMAGEN vuelve a estar obligado a contener el desplazamiento SIGUIENTE. Con `n`
    binders anidados hacen falta los `n+1` pisos — el map simple NO se cierra. -/

theorem forced_shift2 (v t w W' : Term)
    (hclo : ∀ (X : Term),
      Prf (cOk X (unOkF w X 6) ⇒ cOk (substfc (succ v) (liftc zero t) X)
             (unOkF W' (substfc (succ v) (liftc zero t) X) 6)))
    (y : Term) (hy : Prf (In y w)) :
    Prf (In (substfc (succ (succ v)) (liftc zero (liftc zero t)) y) W') :=
  forced_map_tag6 (succ v) (liftc zero t) w W' hclo y hy

/-! ## 11 · LA TERCERA OBLIGACIÓN, que NINGÚN map cubre: el TESTIGO DEL SUSTITUYENDO

    En el disyunto `varc` la imagen de `substtc v t (varc v)` es **`t` mismo**, un código
    ARBITRARIO que no está en el testigo de `X`. Luego el testigo imagen está obligado a
    contener `t` — y, por `wfAll`, un testigo COMPLETO de `t`. Eso no es transformación del
    testigo original: es un PARÁMETRO EXTRA que el enunciado de clausura debe recibir. -/

theorem prf_premisa_tag4 (w y : Term) (hy : Prf (In y w)) :
    Prf (cOk (eqc y y) (binOkF w w (eqc y y) 4)) := by
  refine prf_and_intro (prf_consOk_cons _ _) (prf_and_intro (prf_and_intro ?_ ?_)
    (prf_and_intro ?_ ?_))
  · exact prf_carc_cons (numeralM 4) (cons y (cons y nil))
  · exact prf_lenc_c3 (numeralM 4) y y
  · exact prf_congr_In_left (prf_eq_symm (prf_nthc_c1 (numeralM 4) y (cons y nil))) hy
  · exact prf_congr_In_left (prf_eq_symm (prf_nthc_c2 (numeralM 4) y y nil)) hy

/-- **FORZAMIENTO (tag 4, `eqc`).** Si el testigo contiene el código de la variable
    sustituida, el testigo imagen está obligado a contener el SUSTITUYENDO `t` entero. -/
theorem forced_substituend (v t w W' : Term)
    (hclo : ∀ (X : Term),
      Prf (cOk X (binOkF w w X 4) ⇒ cOk (substfc v t X) (binOkF W' W' (substfc v t X) 4)))
    (hy : Prf (In (varc v) w)) : Prf (In t W') := by
  have hcon := prf_mp (hclo (eqc (varc v) (varc v)))
    (prf_premisa_tag4 w (varc v) hy)
  have hin : Prf (In (nthc (substfc v t (eqc (varc v) (varc v))) (numeralM 1)) W') :=
    prf_and_elim_left (prf_and_elim_right (prf_and_elim_right hcon))
  have heq : Prf (nthc (substfc v t (eqc (varc v) (varc v))) (numeralM 1) =eq t) :=
    prf_eq_trans
      (prf_eq_trans (prf_congr_nthc_lst (numeralM 1) (prf_substfc_eq v t (varc v) (varc v)))
        (prf_nthc_c1 (numeralM 4) (substtc v t (varc v)) (cons (substtc v t (varc v)) nil)))
      (prf_mp (prf_substtc_var_eq v t v) (prf_refl v))
  exact prf_congr_In_left heq hin

/-! ## 12 · FOOTPRINT -/

#print axioms forced_map_tag5
#print axioms forced_map_tag6
#print axioms identity_witness_absurd
#print axioms prf_shapeImpl_implc
#print axioms prf_shapeImpl_strengthens
#print axioms closure_tag5_of_map
#print axioms closure_tag6_of_map
#print axioms map_mem_tc
#print axioms map_mem_fc
#print axioms hcons_of_ax
#print axioms closure_tag5_substfsc
#print axioms closure_tag5_Wtwo
#print axioms closure_tag6_Wtwo
#print axioms forced_shift2
#print axioms forced_substituend

end ClausuraSubstfc
