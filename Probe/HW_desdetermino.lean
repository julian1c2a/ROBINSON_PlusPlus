/-
# `prf_hasWitF_real` — LA NO-VACUIDAD DE LA GUARDA DE `pcc_eval_substfc`,
#  CONSTRUIDA **DESDE EL SORT TERMINO** (ruta B).

Fichero AUTOCONTENIDO (`import ROBINSON_PlusPlus.Meta` y nada mas).

    lake env lean Probe\HW_desdetermino.lean

## Que se prueba

    theorem prf_isFC1_real (phi : Formula) :
        Prf (isFC1 (objList (fcodesF phi)) (objList (tcodesF phi)) (formCodeM phi))

    theorem prf_hasWitF_real (phi : Formula) : Prf (hasWitF (formCodeM phi))

con `fcodesF` / `tcodesF` COMPUTABLES:
  * `fcodesF phi` = subcodigos de FORMULA de `phi` (cierre por subformulas);
  * `tcodesF phi` = `tcodes1s (termsOfF phi)` = cierre por SUBTERMINOS de todos los
    terminos que aparecen en `phi` (dentro de atomos y de ecuaciones).

## De donde sale cada mitad

  * `wfAll1 wT`  — de la mitad TERMINO, que ya estaba hecha: `okE1_Ts` de
    `sondeos/ClausuraLiftSinWTs.lean` §5, aplicado a `termsOfF phi` en vez de a los
    subterminos de UN termino. **Cero trabajo nuevo**: la inducción de `okE1_T`/`okE1_Ts`
    es genérica en el testigo `W` (sólo pide clausura De Bruijn y un ORACULO de
    pertenencia), luego vale palabra por palabra para la union.
  * `wfAllF wF wT` — LO UNICO NUEVO. Ocho nodos, todos en forma ECUACIONAL.
  * `In c wF`    — `mem_self_fcodesF`.

## Lo que se midió y NO hizo falta
  * `argsIn wT Y` es POSICIONAL (`∀ i < lenc Y, In (nthc Y i) wT`): **no** exige que la
    lista de argumentos `Y` este ENTERA en `wT` como objeto, solo sus ELEMENTOS. El riesgo
    señalado en el encargo NO se materializa y el diseño de dos listas basta.
  * `prf_isFormCodeE2_str` (E ⇒ B) NO se usa: no hace falta para la satisfacibilidad.
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

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace HWDesdeTermino

/-! ############################################################################
    ## §0 · Combinadores (copias LITERALES de `sondeos/ClausuraLiftSinWTs.lean` §0)
    ############################################################################ -/

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

/-! ############################################################################
    ## §1 · COPIA LITERAL del reconocedor de codigo de TERMINO sin `wTs`
       (`sondeos/ClausuraLiftSinWTs.lean:109-145`, identico al `ENS` de
        `sondeos/EvalSubstfcPrf.lean:5996-6022`).
    ############################################################################ -/

def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))

def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def shapeNul (X : Term) (k : Nat) : Formula := Formula.eq X (cons (numeralM k) nil)

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))

def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))

def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)

def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

/-! ### Fontaneria De Bruijn del bloque de TERMINO -/

theorem liftF_argsIn (k : Nat) (wT Y : Term) :
    liftFormula k (argsIn wT Y) = argsIn (liftTerm k wT) (liftTerm k Y) := by
  simp only [argsIn, argsInBody, liftFormula, lt, lenc, nthc, In, liftTerm, liftTerms,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem substF_argsIn (v : Nat) (s wT Y : Term) :
    substFormula v s (argsIn wT Y) = argsIn (substTerm v s wT) (substTerm v s Y) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [argsIn, argsInBody, substFormula, substTerm, substTerms, lt, lenc, nthc, In,
    liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ, reduceIte, if_true,
    FOL.substTerm_lift_comm_zero]

theorem liftF_isTermCodeE1 (k : Nat) (wT X : Term) :
    liftFormula k (isTermCodeE1 wT X) = isTermCodeE1 (liftTerm k wT) (liftTerm k X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, liftFormula, liftF_argsIn,
    nthc, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]

theorem substF_isTermCodeE1 (v : Nat) (s wT X : Term) :
    substFormula v s (isTermCodeE1 wT X)
      = isTermCodeE1 (substTerm v s wT) (substTerm v s X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, substFormula, substF_argsIn,
    nthc, cons, nil, zero, substTerm, substTerms, substTerm_numeralM]

theorem liftF_wfAll1 (k : Nat) (w : Term) :
    liftFormula k (wfAll1 w) = wfAll1 (liftTerm k w) := by
  simp only [wfAll1, wfAll1Body, liftFormula, liftF_isTermCodeE1, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem substF_wfAll1 (v : Nat) (s w : Term) :
    substFormula v s (wfAll1 w) = wfAll1 (substTerm v s w) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [wfAll1, wfAll1Body, substFormula, substF_isTermCodeE1, lt, lenc, nthc,
    substTerm, substTerms, liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ,
    reduceIte, if_true, FOL.substTerm_lift_comm_zero]

theorem liftF_isTC1 (k : Nat) (w c : Term) :
    liftFormula k (isTC1 w c) = isTC1 (liftTerm k w) (liftTerm k c) := by
  simp only [isTC1, land, In, liftFormula, liftF_wfAll1, liftTerm, liftTerms]

theorem substF_isTC1 (v : Nat) (s w c : Term) :
    substFormula v s (isTC1 w c) = isTC1 (substTerm v s w) (substTerm v s c) := by
  simp only [isTC1, land, In, substFormula, substF_wfAll1, substTerm, substTerms]

/-! ### Leibniz y congruencias -/

theorem PrfH_congr_argsIn {Γ : List Formula} {wT Y₁ Y₂ : Term} (h : PrfH Γ (Y₁ =eq Y₂))
    (ha : PrfH Γ (argsIn wT Y₁)) : PrfH Γ (argsIn wT Y₂) := by
  have hS : ∀ s : Term, substFormula 0 s (argsIn (liftTerm 0 wT) (.var 0)) = argsIn wT s := by
    intro s
    simp only [substF_argsIn, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS Y₂) ▸ PrfH_leibniz_subst (A := argsIn (liftTerm 0 wT) (.var 0)) h ((hS Y₁) ▸ ha)

theorem PrfH_congr_isTermCodeE1 {Γ : List Formula} {wT X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (ha : PrfH Γ (isTermCodeE1 wT X₁)) : PrfH Γ (isTermCodeE1 wT X₂) := by
  have hS : ∀ s : Term,
      substFormula 0 s (isTermCodeE1 (liftTerm 0 wT) (.var 0)) = isTermCodeE1 wT s := by
    intro s
    simp only [substF_isTermCodeE1, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := isTermCodeE1 (liftTerm 0 wT) (.var 0)) h ((hS X₁) ▸ ha)

theorem PrfH_congr_In_left {Γ : List Formula} {u v w : Term} (h : PrfH Γ (u =eq v))
    (hin : PrfH Γ (In u w)) : PrfH Γ (In v w) := by
  have hS : ∀ s : Term, substFormula 0 s (In (.var 0) (liftTerm 0 w)) = In s w := by
    intro s
    simp only [In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS v) ▸ PrfH_leibniz_subst (A := In (.var 0) (liftTerm 0 w)) h ((hS u) ▸ hin)

theorem prf_congr_argsIn {wT Y₁ Y₂ : Term} (h : Prf (Y₁ =eq Y₂)) (ha : Prf (argsIn wT Y₁)) :
    Prf (argsIn wT Y₂) :=
  prfH_nil_to_prf (PrfH_congr_argsIn (prf_to_prfH h []) (prf_to_prfH ha [])) rfl

theorem prf_congr_In_left {u v w : Term} (h : Prf (u =eq v)) (hin : Prf (In u w)) :
    Prf (In v w) :=
  prfH_nil_to_prf (PrfH_congr_In_left (prf_to_prfH h []) (prf_to_prfH hin [])) rfl

/-! ### `∀` acotado con cota ABSTRACTA igual a un numeral -/

theorem prf_bdAll_numeral (Φ : Formula) (hΦ : substFormula 0 (.var 0) Φ = Φ) : ∀ (n : Nat),
    (∀ k : Nat, k < n → Prf (substFormula 0 (numeralM k) Φ)) →
      Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM n)) Φ))
  | 0, _ => by
      refine Prf.gen _ (prf_deduction ?_)
      exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq Φ))
        (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _)))
  | n + 1, h => by
      have ih := prf_bdAll_numeral Φ hΦ n (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have hself : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) (numeralM n)) Φ)
          = Formula.impl (lt (.var 0) (numeralM n)) Φ := by
        simp only [substFormula, lt, substTerm, substTerms, substTerm_numeralM, hΦ, if_true]
      refine Prf.gen _ (prf_deduction ?_)
      have hsplit : PrfH [lt (.var 0) (numeralM (n + 1))]
          (lor (lt (.var 0) (numeralM n)) (Formula.eq (.var 0) (numeralM n))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) (numeralM n)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      refine PrfH_or_elim hsplit ?brA ?brB
      case brA =>
        exact PrfH.mp _ _ _ (prf_to_prfH (hself ▸ prf_spec ih (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      case brB =>
        have hinst : Prf (substFormula 0 (numeralM n) Φ) := h n (Nat.lt_succ_self n)
        have heq : PrfH (Formula.eq (.var 0) (numeralM n) :: [lt (.var 0) (numeralM (n + 1))])
            (Formula.eq (numeralM n) (.var 0)) :=
          PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _))
        have := PrfH_leibniz_subst (A := Φ) heq (prf_to_prfH hinst _)
        rwa [hΦ] at this

theorem prf_bdAll_of_bound (Φ : Formula) (b : Term) (n : Nat)
    (hΦ : substFormula 0 (.var 0) Φ = Φ)
    (hb : Prf (Formula.eq b (numeralM n)))
    (h : ∀ k : Nat, k < n → Prf (substFormula 0 (numeralM k) Φ)) :
    Prf (Formula.forall (Formula.impl (lt (.var 0) b) Φ)) := by
  have key : Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM n)) Φ)) :=
    prf_bdAll_numeral Φ hΦ n h
  have hself : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) (numeralM n)) Φ)
      = Formula.impl (lt (.var 0) (numeralM n)) Φ := by
    simp only [substFormula, lt, substTerm, substTerms, substTerm_numeralM, hΦ, if_true]
  refine Prf.gen _ (prf_deduction ?_)
  exact PrfH.mp _ _ _ (prf_to_prfH (hself ▸ prf_spec key (.var 0)) _)
    (ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH hb _) (PrfH.hyp _ _ (List.Mem.head _)))

/-! ### `nthc` en las posiciones 1 y 2 -/

theorem prf_nthc_c1 (a b c : Term) : Prf (nthc (cons a (cons b c)) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b c) (numeralM 0)) (prf_nthc_zero b c)

theorem prf_nthc_c2 (a b c d : Term) :
    Prf (nthc (cons a (cons b (cons c d))) (numeralM 2) =eq c) :=
  prf_eq_trans (prf_nthc_succ a (cons b (cons c d)) (numeralM 1)) (prf_nthc_c1 b c d)

/-! ### Los dos moldes de nodo de TERMINO, en forma ECUACIONAL -/

theorem prf_isTermCodeE1_var (W a : Term) : Prf (isTermCodeE1 W (varc a)) :=
  prf_orL (prf_eq_symm (prf_congr_cons_tail (prf_congr_cons_head
    (prf_nthc_c1 (numeralM 0) a nil))))

theorem prf_isTermCodeE1_func (W S C : Term) (h : Prf (argsIn W C)) :
    Prf (isTermCodeE1 W (funcc S C)) :=
  prf_orR (prf_and_intro
    (prf_eq_symm (prf_congr_cons_tail (prf_eq_trans
      (prf_congr_cons_head (prf_nthc_c1 (numeralM 1) S (cons C nil)))
      (prf_congr_cons_tail (prf_congr_cons_head (prf_nthc_c2 (numeralM 1) S C nil))))))
    (prf_congr_argsIn (prf_eq_symm (prf_nthc_c2 (numeralM 1) S C nil)) h))

theorem prf_argsIn_of_closed (W C : Term) (n : Nat)
    (hWl : liftTerm 0 W = W) (hCl : liftTerm 0 C = C)
    (hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W)
    (hCs : ∀ (v : Nat) (s : Term), substTerm v s C = C)
    (hlen : Prf (lenc C =eq numeralM n))
    (h : ∀ k : Nat, k < n → Prf (In (nthc C (numeralM k)) W)) :
    Prf (argsIn W C) := by
  have hAI : argsIn W C
      = Formula.forall (Formula.impl (lt (.var 0) (lenc C)) (In (nthc C (.var 0)) W)) := by
    simp only [argsIn, argsInBody, lt, lenc, nthc, In, liftTerm, liftTerms, hWl, hCl]
  rw [hAI]
  refine prf_bdAll_of_bound _ (lenc C) n ?_ hlen ?_
  · simp only [In, nthc, substFormula, substTerm, substTerms, hWs, hCs, if_true]
  · intro k hk
    have hk' := h k hk
    simpa only [In, nthc, substFormula, substTerm, substTerms, hWs, hCs,
      substTerm_numeralM, if_true, reduceIte] using hk'

/-! ### `lenc`/`nthc` de `termsCodeM` -/

theorem prf_lenc_termsCodeM : ∀ ts : List Term,
    Prf (lenc (termsCodeM ts) =eq numeralM ts.length)
  | []      => prf_lenc_nil
  | t :: ts =>
      prf_eq_trans (prf_lenc_cons (termCodeM t) (termsCodeM ts))
        (prf_eq_congr_succ (prf_lenc_termsCodeM ts))

theorem prf_nthc_termsCodeM : ∀ (ts : List Term) (k : Nat) (x : Term), ts[k]? = some x →
    Prf (nthc (termsCodeM ts) (numeralM k) =eq termCodeM x)
  | [],      k,     x, h => by simp at h
  | t :: ts, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact prf_nthc_zero (termCodeM t) (termsCodeM ts)
  | t :: ts, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact prf_eq_trans (prf_nthc_succ (termCodeM t) (termsCodeM ts) (numeralM k))
        (prf_nthc_termsCodeM ts k x h)

theorem mem_of_getElem? : ∀ (L : List Term) (k : Nat) (x : Term), L[k]? = some x → List.Mem x L
  | [],      k,     x, h => by simp at h
  | e :: es, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact List.Mem.head _
  | e :: es, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact List.Mem.tail _ (mem_of_getElem? es k x h)

/-! ### EL TESTIGO DE TERMINO: `tcodes1` / `tcodes1s` -/

mutual
def tcodes1 : Term → List Term
  | .var n     => [termCodeM (.var n)]
  | .func s ts => termCodeM (.func s ts) :: tcodes1s ts
def tcodes1s : List Term → List Term
  | []      => []
  | t :: ts => tcodes1 t ++ tcodes1s ts
end

theorem mem_self_tcodes1 (t : Term) : List.Mem (termCodeM t) (tcodes1 t) := by
  cases t with
  | var n     => simp only [tcodes1]; exact List.Mem.head _
  | func s ts => simp only [tcodes1]; exact List.Mem.head _

theorem mem_tcodes1s_of_mem : ∀ (ts : List Term) (t : Term), List.Mem t ts →
    List.Mem (termCodeM t) (tcodes1s ts)
  | [],      t, h => by cases h
  | u :: us, t, h => by
      simp only [tcodes1s]
      rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_append.mpr (Or.inl (mem_self_tcodes1 t))
      · exact List.mem_append.mpr (Or.inr (mem_tcodes1s_of_mem us t h'))

/-- `tcodes1s` es un `flatMap`: reparte por `++`. -/
theorem tcodes1s_append : ∀ (as bs : List Term),
    tcodes1s (as ++ bs) = tcodes1s as ++ tcodes1s bs
  | [],      bs => by simp only [tcodes1s, List.nil_append]
  | a :: as, bs => by
      simp only [tcodes1s, List.cons_append, tcodes1s_append as bs, List.append_assoc]

def CodeClosed (x : Term) : Prop :=
  (∀ c : Nat, liftTerm c x = x) ∧ (∀ (v : Nat) (s : Term), substTerm v s x = x)

theorem closed_termCodeM (t : Term) : CodeClosed (termCodeM t) :=
  ⟨fun c => liftTerm_termCodeM c t, fun v s => substTerm_termCodeM v s t⟩

theorem closed_formCodeM (φ : Formula) : CodeClosed (formCodeM φ) :=
  ⟨fun c => liftTerm_formCodeM c φ, fun v s => substTerm_formCodeM v s φ⟩

mutual
theorem closed_mem_tcodes1 : ∀ (t x : Term), List.Mem x (tcodes1 t) → CodeClosed x
  | .var n, x, h => by
      simp only [tcodes1] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termCodeM (.var n)
      · cases h'
  | .func s ts, x, h => by
      simp only [tcodes1] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termCodeM (.func s ts)
      · exact closed_mem_tcodes1s ts x h'
theorem closed_mem_tcodes1s : ∀ (ts : List Term) (x : Term),
    List.Mem x (tcodes1s ts) → CodeClosed x
  | [], x, h => by simp only [tcodes1s] at h; cases h
  | t :: ts, x, h => by
      simp only [tcodes1s] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_tcodes1 t x hA
      · exact closed_mem_tcodes1s ts x hB
end

/-! ### `objList` -/

theorem liftTerm_objList (c : Nat) : ∀ (L : List Term),
    (∀ x : Term, List.Mem x L → liftTerm c x = x) → liftTerm c (objList L) = objList L
  | [],      _ => rfl
  | e :: es, h => by
      simp only [objList, cons, liftTerm, liftTerms, h e (List.Mem.head _),
        liftTerm_objList c es (fun x hx => h x (List.Mem.tail _ hx))]

theorem substTerm_objList (v : Nat) (s : Term) : ∀ (L : List Term),
    (∀ x : Term, List.Mem x L → substTerm v s x = x) → substTerm v s (objList L) = objList L
  | [],      _ => rfl
  | e :: es, h => by
      simp only [objList, cons, substTerm, substTerms, h e (List.Mem.head _),
        substTerm_objList v s es (fun x hx => h x (List.Mem.tail _ hx))]

theorem prf_lenc_objList : ∀ L : List Term,
    Prf (Formula.eq (lenc (objList L)) (numeralM L.length))
  | []      => prf_lenc_nil
  | e :: es =>
      prf_eq_trans (prf_lenc_cons e (objList es)) (prf_eq_congr_succ (prf_lenc_objList es))

theorem prf_nthc_objList : ∀ (L : List Term) (k : Nat) (x : Term), L[k]? = some x →
    Prf (Formula.eq (nthc (objList L) (numeralM k)) x)
  | [],      k,     x, h => by simp at h
  | e :: es, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact prf_nthc_zero e (objList es)
  | e :: es, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact prf_eq_trans (prf_nthc_succ e (objList es) (numeralM k))
        (prf_nthc_objList es k x h)

theorem prf_In_objList : ∀ (L : List Term) (x : Term), List.Mem x L → Prf (In x (objList L))
  | [],      x, h => by cases h
  | e :: es, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact prf_in_cons_head x (objList es)
      · exact prf_in_cons_tail e (prf_In_objList es x h')

/-! ### LA INDUCCION DE TERMINO — copia literal de `okE1_T`/`okE1_Ts` -/

mutual
theorem okE1_T : ∀ (t : Term) (W : Term)
    (_hW : ∀ c : Nat, liftTerm c W = W) (_hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W)
    (_ho : ∀ y : Term, List.Mem y (tcodes1 t) → Prf (In y W))
    (x : Term), List.Mem x (tcodes1 t) → Prf (isTermCodeE1 W x)
  | .var n, W, hW, hWs, ho, x, h => by
      simp only [tcodes1] at h
      rcases List.mem_cons.mp h with rfl | h'
      · show Prf (isTermCodeE1 W (termCodeM (.var n)))
        exact prf_isTermCodeE1_var W (numeralM n)
      · cases h'
  | .func s ts, W, hW, hWs, ho, x, h => by
      simp only [tcodes1] at h
      rcases List.mem_cons.mp h with rfl | h'
      · show Prf (isTermCodeE1 W (termCodeM (.func s ts)))
        refine prf_isTermCodeE1_func W (strCodeM s) (termsCodeM ts) ?_
        refine prf_argsIn_of_closed W (termsCodeM ts) ts.length (hW 0)
          (liftTerm_termsCodeM 0 ts) hWs (fun v s' => substTerm_termsCodeM v s' ts)
          (prf_lenc_termsCodeM ts) ?_
        intro k hk
        obtain ⟨u, hu⟩ : ∃ u, ts[k]? = some u := ⟨ts[k], getElem?_pos ts k hk⟩
        refine prf_congr_In_left (prf_eq_symm (prf_nthc_termsCodeM ts k u hu)) ?_
        refine ho (termCodeM u) ?_
        simp only [tcodes1]
        exact List.Mem.tail _ (mem_tcodes1s_of_mem ts u (mem_of_getElem? ts k u hu))
      · exact okE1_Ts ts W hW hWs
          (fun y hy => ho y (by simp only [tcodes1]; exact List.Mem.tail _ hy)) x h'
theorem okE1_Ts : ∀ (ts : List Term) (W : Term)
    (_hW : ∀ c : Nat, liftTerm c W = W) (_hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W)
    (_ho : ∀ y : Term, List.Mem y (tcodes1s ts) → Prf (In y W))
    (x : Term), List.Mem x (tcodes1s ts) → Prf (isTermCodeE1 W x)
  | [], W, hW, hWs, ho, x, h => by simp only [tcodes1s] at h; cases h
  | t :: ts, W, hW, hWs, ho, x, h => by
      simp only [tcodes1s] at h
      rcases List.mem_append.mp h with hA | hB
      · exact okE1_T t W hW hWs
          (fun y hy => ho y (by
            simp only [tcodes1s]; exact List.mem_append.mpr (Or.inl hy))) x hA
      · exact okE1_Ts ts W hW hWs
          (fun y hy => ho y (by
            simp only [tcodes1s]; exact List.mem_append.mpr (Or.inr hy))) x hB
end

/-- **La mitad TERMINO, generalizada a una LISTA de terminos.** Es `prf_isTC1_tcodes`
    de `ClausuraLiftSinWTs.lean:1010` con `okE1_Ts` en lugar de `okE1_T`: la induccion
    era ya generica en `W`, luego no hay trabajo nuevo. -/
theorem prf_wfAll1_tcodes1s (ts : List Term) : Prf (wfAll1 (objList (tcodes1s ts))) := by
  let L : List Term := tcodes1s ts
  let W : Term := objList L
  have hWl : ∀ c : Nat, liftTerm c W = W := fun c =>
    liftTerm_objList c L (fun x hx => (closed_mem_tcodes1s ts x hx).1 c)
  have hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W := fun v s =>
    substTerm_objList v s L (fun x hx => (closed_mem_tcodes1s ts x hx).2 v s)
  have horacle : ∀ y : Term, List.Mem y L → Prf (In y W) := fun y hy => prf_In_objList L y hy
  have hAI : wfAll1 W
      = Formula.forall (Formula.impl (lt (.var 0) (lenc W))
          (isTermCodeE1 W (nthc W (.var 0)))) := by
    simp only [wfAll1, wfAll1Body, lt, lenc, nthc, liftF_isTermCodeE1, liftTerm, liftTerms, hWl]
  rw [hAI]
  refine prf_bdAll_of_bound _ (lenc W) L.length ?_ (prf_lenc_objList L) ?_
  · simp only [substF_isTermCodeE1, nthc, substTerm, substTerms, hWs, if_true]
  · intro k hk
    obtain ⟨x, hx⟩ : ∃ x, L[k]? = some x := ⟨L[k], getElem?_pos L k hk⟩
    have hnode : Prf (isTermCodeE1 W x) :=
      okE1_Ts ts W hWl hWs horacle x (mem_of_getElem? L k x hx)
    have hres : Prf (isTermCodeE1 W (nthc W (numeralM k))) :=
      prfH_nil_to_prf (PrfH_congr_isTermCodeE1
        (prf_to_prfH (prf_eq_symm (prf_nthc_objList L k x hx)) [])
        (prf_to_prfH hnode [])) rfl
    simpa only [substF_isTermCodeE1, nthc, substTerm, substTerms, hWs,
      substTerm_numeralM, if_true, reduceIte] using hres

/-- El caso de UN termino (control: coincide con `SinWTs.prf_isTC1_tcodes`). -/
theorem prf_isTC1_tcodes (t : Term) : Prf (isTC1 (objList (tcodes1 t)) (termCodeM t)) := by
  refine prf_and_intro ?_ (prf_In_objList (tcodes1 t) (termCodeM t) (mem_self_tcodes1 t))
  have h : tcodes1 t = tcodes1s [t] := by
    simp only [tcodes1s, List.append_nil]
  rw [h]
  exact prf_wfAll1_tcodes1s [t]

/-! ############################################################################
    ## §2 · COPIA LITERAL del reconocedor de codigo de **FORMULA**
       (`sondeos/EvalSubstfcPrf.lean:6095-6135` y `:8243`, namespace `ENS`).
    ############################################################################ -/

def lorAll : Formula → List Formula → Formula
  | a, []      => a
  | a, b :: bs => lor a (lorAll b bs)

/-- tag 2 · `botc` -/
def clBot (X : Term) : Formula := shapeNul X 2
/-- tag 3 · `atomc p ts` : casilla 1 OPACA (simbolo), casilla 2 LISTA de terminos. -/
def clAtom (wT X : Term) : Formula :=
  land (shapeBin X 3) (argsIn wT (nthc X (numeralM 2)))
/-- tag 4 · `eqc a b` : las DOS casillas son codigos de TERMINO. -/
def clEq (wT X : Term) : Formula :=
  land (shapeBin X 4)
    (land (In (nthc X (numeralM 1)) wT) (In (nthc X (numeralM 2)) wT))
/-- tags 5/7/8 · `implc`/`andc`/`orc` : las DOS casillas son codigos de FORMULA. -/
def clBin (wF X : Term) (k : Nat) : Formula :=
  land (shapeBin X k)
    (land (In (nthc X (numeralM 1)) wF) (In (nthc X (numeralM 2)) wF))
/-- tags 6/9 · `forallc`/`exc` : UNA casilla de FORMULA. -/
def clUn (wF X : Term) (k : Nat) : Formula :=
  land (shapeUn X k) (In (nthc X (numeralM 1)) wF)

def isFormCodeE2 (wF wT X : Term) : Formula :=
  lorAll (clBot X)
    [ clAtom wT X
    , clEq wT X
    , clBin wF X 5
    , clUn wF X 6
    , clBin wF X 7
    , clBin wF X 8
    , clUn wF X 9 ]

def wfAllFBody (wF wT : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc wF)))
    (isFormCodeE2 (liftTerm 0 wF) (liftTerm 0 wT) (nthc (liftTerm 0 wF) (.var 0)))

def wfAllF (wF wT : Term) : Formula := Formula.forall (wfAllFBody wF wT)

def isFC1 (wF wT c : Term) : Formula :=
  land (land (wfAll1 wT) (wfAllF wF wT)) (In c wF)

def hasWitF (c : Term) : Formula :=
  Formula.ex (Formula.ex (isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 c))))

/-! ### Fontaneria De Bruijn del bloque de FORMULA -/

theorem liftF_isFormCodeE2 (k : Nat) (wF wT X : Term) :
    liftFormula k (isFormCodeE2 wF wT X)
      = isFormCodeE2 (liftTerm k wF) (liftTerm k wT) (liftTerm k X) := by
  simp only [isFormCodeE2, lorAll, clBot, clAtom, clEq, clBin, clUn, shapeNul, shapeUn,
    shapeBin, lor, land, In, liftFormula, liftF_argsIn, nthc, cons, nil, zero,
    liftTerm, liftTerms, liftTerm_numeralM]

theorem substF_isFormCodeE2 (v : Nat) (s wF wT X : Term) :
    substFormula v s (isFormCodeE2 wF wT X)
      = isFormCodeE2 (substTerm v s wF) (substTerm v s wT) (substTerm v s X) := by
  simp only [isFormCodeE2, lorAll, clBot, clAtom, clEq, clBin, clUn, shapeNul, shapeUn,
    shapeBin, lor, land, In, substFormula, substF_argsIn, nthc, cons, nil, zero,
    substTerm, substTerms, substTerm_numeralM]

theorem liftF_wfAllF (k : Nat) (wF wT : Term) :
    liftFormula k (wfAllF wF wT) = wfAllF (liftTerm k wF) (liftTerm k wT) := by
  simp only [wfAllF, wfAllFBody, liftFormula, liftF_isFormCodeE2, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem substF_wfAllF (v : Nat) (s wF wT : Term) :
    substFormula v s (wfAllF wF wT) = wfAllF (substTerm v s wF) (substTerm v s wT) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [wfAllF, wfAllFBody, substFormula, substF_isFormCodeE2, lt, lenc, nthc,
    substTerm, substTerms, liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ,
    reduceIte, if_true, FOL.substTerm_lift_comm_zero]

theorem liftF_isFC1 (k : Nat) (wF wT c : Term) :
    liftFormula k (isFC1 wF wT c)
      = isFC1 (liftTerm k wF) (liftTerm k wT) (liftTerm k c) := by
  simp only [isFC1, land, In, liftFormula, liftF_wfAll1, liftF_wfAllF, liftTerm, liftTerms]

theorem substF_isFC1 (v : Nat) (s wF wT c : Term) :
    substFormula v s (isFC1 wF wT c)
      = isFC1 (substTerm v s wF) (substTerm v s wT) (substTerm v s c) := by
  simp only [isFC1, land, In, substFormula, substF_wfAll1, substF_wfAllF, substTerm, substTerms]

theorem PrfH_congr_isFormCodeE2 {Γ : List Formula} {wF wT X₁ X₂ : Term}
    (h : PrfH Γ (X₁ =eq X₂)) (ha : PrfH Γ (isFormCodeE2 wF wT X₁)) :
    PrfH Γ (isFormCodeE2 wF wT X₂) := by
  have hS : ∀ s : Term,
      substFormula 0 s (isFormCodeE2 (liftTerm 0 wF) (liftTerm 0 wT) (.var 0))
        = isFormCodeE2 wF wT s := by
    intro s
    simp only [substF_isFormCodeE2, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS X₂) ▸
    PrfH_leibniz_subst (A := isFormCodeE2 (liftTerm 0 wF) (liftTerm 0 wT) (.var 0)) h
      ((hS X₁) ▸ ha)

/-! ############################################################################
    ## §3 · LOS OCHO MOLDES DE NODO DE FORMULA, en forma ECUACIONAL.

    Cada uno cuesta MENOS que su gemelo posicional: una sola ecuacion `shape*` en
    lugar de `consOk ∧ carc ≐ k̄ ∧ lenc ≐ n̄`.
    ############################################################################ -/

/-- Inyeccion en el disyunto `i` de `lorAll`. -/
theorem inj_bot  {WF WT X : Term} (h : Prf (clBot X))      : Prf (isFormCodeE2 WF WT X) := by
  simp only [isFormCodeE2, lorAll]; exact prf_orL h
theorem inj_atom {WF WT X : Term} (h : Prf (clAtom WT X))  : Prf (isFormCodeE2 WF WT X) := by
  simp only [isFormCodeE2, lorAll]; exact prf_orR (prf_orL h)
theorem inj_eq   {WF WT X : Term} (h : Prf (clEq WT X))    : Prf (isFormCodeE2 WF WT X) := by
  simp only [isFormCodeE2, lorAll]; exact prf_orR (prf_orR (prf_orL h))
theorem inj_bin5 {WF WT X : Term} (h : Prf (clBin WF X 5)) : Prf (isFormCodeE2 WF WT X) := by
  simp only [isFormCodeE2, lorAll]; exact prf_orR (prf_orR (prf_orR (prf_orL h)))
theorem inj_un6  {WF WT X : Term} (h : Prf (clUn WF X 6))  : Prf (isFormCodeE2 WF WT X) := by
  simp only [isFormCodeE2, lorAll]
  exact prf_orR (prf_orR (prf_orR (prf_orR (prf_orL h))))
theorem inj_bin7 {WF WT X : Term} (h : Prf (clBin WF X 7)) : Prf (isFormCodeE2 WF WT X) := by
  simp only [isFormCodeE2, lorAll]
  exact prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orL h)))))
theorem inj_bin8 {WF WT X : Term} (h : Prf (clBin WF X 8)) : Prf (isFormCodeE2 WF WT X) := by
  simp only [isFormCodeE2, lorAll]
  exact prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orL h))))))
theorem inj_un9  {WF WT X : Term} (h : Prf (clUn WF X 9))  : Prf (isFormCodeE2 WF WT X) := by
  simp only [isFormCodeE2, lorAll]
  exact prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR (prf_orR h))))))

/-- `shapeNul` de un nodo NULARIO real. -/
theorem prf_shapeNul_cons (k : Nat) : Prf (shapeNul (cons (numeralM k) nil) k) :=
  prf_refl _

/-- `shapeUn` de un nodo UNARIO real. -/
theorem prf_shapeUn_cons (k : Nat) (a : Term) :
    Prf (shapeUn (cons (numeralM k) (cons a nil)) k) :=
  prf_eq_symm (prf_congr_cons_tail (prf_congr_cons_head (prf_nthc_c1 (numeralM k) a nil)))

/-- `shapeBin` de un nodo BINARIO real. -/
theorem prf_shapeBin_cons (k : Nat) (a b : Term) :
    Prf (shapeBin (cons (numeralM k) (cons a (cons b nil))) k) :=
  prf_eq_symm (prf_congr_cons_tail (prf_eq_trans
    (prf_congr_cons_head (prf_nthc_c1 (numeralM k) a (cons b nil)))
    (prf_congr_cons_tail (prf_congr_cons_head (prf_nthc_c2 (numeralM k) a b nil)))))

theorem prf_clBot_bot : Prf (clBot (formCodeM Formula.bottom)) := by
  simp only [clBot, formCodeM]
  exact prf_shapeNul_cons 2

theorem prf_clBin_cons (WF : Term) (k : Nat) (ca cb : Term)
    (ha : Prf (In ca WF)) (hb : Prf (In cb WF)) :
    Prf (clBin WF (cons (numeralM k) (cons ca (cons cb nil))) k) :=
  prf_and_intro (prf_shapeBin_cons k ca cb)
    (prf_and_intro
      (prf_congr_In_left (prf_eq_symm (prf_nthc_c1 (numeralM k) ca (cons cb nil))) ha)
      (prf_congr_In_left (prf_eq_symm (prf_nthc_c2 (numeralM k) ca cb nil)) hb))

theorem prf_clUn_cons (WF : Term) (k : Nat) (ca : Term) (ha : Prf (In ca WF)) :
    Prf (clUn WF (cons (numeralM k) (cons ca nil)) k) :=
  prf_and_intro (prf_shapeUn_cons k ca)
    (prf_congr_In_left (prf_eq_symm (prf_nthc_c1 (numeralM k) ca nil)) ha)

/-- `clEq wT X` es LITERALMENTE `clBin wT X 4` (misma forma, otra lista). -/
theorem clEq_eq_clBin (wT X : Term) : clEq wT X = clBin wT X 4 := rfl

theorem prf_clEq_cons (WT ca cb : Term)
    (ha : Prf (In ca WT)) (hb : Prf (In cb WT)) :
    Prf (clEq WT (cons (numeralM 4) (cons ca (cons cb nil)))) := by
  rw [clEq_eq_clBin]
  exact prf_clBin_cons WT 4 ca cb ha hb

/-- **EL NODO `atomc`** — aqui es donde engancha la mitad de TERMINO: la casilla 2
    NO se pide como objeto en `wT`, sino POSICIONALMENTE (`argsIn`), o sea que basta
    con que los CODIGOS DE LOS ARGUMENTOS esten en `wT`. -/
theorem prf_clAtom_cons (WT cp : Term) (ts : List Term)
    (hWTl : liftTerm 0 WT = WT)
    (hWTs : ∀ (v : Nat) (s : Term), substTerm v s WT = WT)
    (h : ∀ u : Term, List.Mem u ts → Prf (In (termCodeM u) WT)) :
    Prf (clAtom WT (cons (numeralM 3) (cons cp (cons (termsCodeM ts) nil)))) := by
  refine prf_and_intro (prf_shapeBin_cons 3 cp (termsCodeM ts)) ?_
  refine prf_congr_argsIn
    (prf_eq_symm (prf_nthc_c2 (numeralM 3) cp (termsCodeM ts) nil)) ?_
  refine prf_argsIn_of_closed WT (termsCodeM ts) ts.length hWTl
    (liftTerm_termsCodeM 0 ts) hWTs (fun v s => substTerm_termsCodeM v s ts)
    (prf_lenc_termsCodeM ts) ?_
  intro k hk
  obtain ⟨u, hu⟩ : ∃ u, ts[k]? = some u := ⟨ts[k], getElem?_pos ts k hk⟩
  exact prf_congr_In_left (prf_eq_symm (prf_nthc_termsCodeM ts k u hu))
    (h u (mem_of_getElem? ts k u hu))

/-! ############################################################################
    ## §4 · LAS DOS LISTAS TESTIGO, COMPUTABLES.
    ############################################################################ -/

/-- Los subcodigos de FORMULA de `phi` (cierre por subformulas). -/
def fcodesF : Formula → List Term
  | .bottom          => [formCodeM Formula.bottom]
  | .atom p ts       => [formCodeM (Formula.atom p ts)]
  | .eq t u          => [formCodeM (Formula.eq t u)]
  | .impl a b        => formCodeM (Formula.impl a b) :: (fcodesF a ++ fcodesF b)
  | Formula.forall a => formCodeM (Formula.forall a) :: fcodesF a
  | .and a b         => formCodeM (Formula.and a b) :: (fcodesF a ++ fcodesF b)
  | .or a b          => formCodeM (Formula.or a b) :: (fcodesF a ++ fcodesF b)
  | .ex a            => formCodeM (Formula.ex a) :: fcodesF a

/-- Los TERMINOS que aparecen en `phi` (dentro de atomos y ecuaciones). -/
def termsOfF : Formula → List Term
  | .bottom          => []
  | .atom p ts       => ts
  | .eq t u          => [t, u]
  | .impl a b        => termsOfF a ++ termsOfF b
  | Formula.forall a => termsOfF a
  | .and a b         => termsOfF a ++ termsOfF b
  | .or a b          => termsOfF a ++ termsOfF b
  | .ex a            => termsOfF a

/-- El testigo de TERMINO: cierre por SUBTERMINOS de todos los terminos de `phi`. -/
def tcodesF (phi : Formula) : List Term := tcodes1s (termsOfF phi)

theorem fcodesF_bot : fcodesF Formula.bottom = [formCodeM Formula.bottom] := rfl
theorem fcodesF_atom (p : String) (ts : List Term) :
    fcodesF (Formula.atom p ts) = [formCodeM (Formula.atom p ts)] := rfl
theorem fcodesF_eqf (t u : Term) :
    fcodesF (Formula.eq t u) = [formCodeM (Formula.eq t u)] := rfl
theorem fcodesF_impl (a b : Formula) :
    fcodesF (Formula.impl a b) = formCodeM (Formula.impl a b) :: (fcodesF a ++ fcodesF b) := rfl
theorem fcodesF_forall (a : Formula) :
    fcodesF (Formula.forall a) = formCodeM (Formula.forall a) :: fcodesF a := rfl
theorem fcodesF_and (a b : Formula) :
    fcodesF (Formula.and a b) = formCodeM (Formula.and a b) :: (fcodesF a ++ fcodesF b) := rfl
theorem fcodesF_or (a b : Formula) :
    fcodesF (Formula.or a b) = formCodeM (Formula.or a b) :: (fcodesF a ++ fcodesF b) := rfl
theorem fcodesF_ex (a : Formula) :
    fcodesF (Formula.ex a) = formCodeM (Formula.ex a) :: fcodesF a := rfl

theorem tcodesF_atom (p : String) (ts : List Term) :
    tcodesF (Formula.atom p ts) = tcodes1s ts := rfl
theorem tcodesF_eqf (t u : Term) : tcodesF (Formula.eq t u) = tcodes1s [t, u] := rfl
theorem tcodesF_impl (a b : Formula) :
    tcodesF (Formula.impl a b) = tcodesF a ++ tcodesF b := by
  simp only [tcodesF, termsOfF, tcodes1s_append]
theorem tcodesF_and (a b : Formula) :
    tcodesF (Formula.and a b) = tcodesF a ++ tcodesF b := by
  simp only [tcodesF, termsOfF, tcodes1s_append]
theorem tcodesF_or (a b : Formula) :
    tcodesF (Formula.or a b) = tcodesF a ++ tcodesF b := by
  simp only [tcodesF, termsOfF, tcodes1s_append]
theorem tcodesF_forall (a : Formula) : tcodesF (Formula.forall a) = tcodesF a := rfl
theorem tcodesF_ex (a : Formula) : tcodesF (Formula.ex a) = tcodesF a := rfl

theorem mem_self_fcodesF (phi : Formula) : List.Mem (formCodeM phi) (fcodesF phi) := by
  cases phi with
  | bottom   => exact List.Mem.head _
  | atom p ts => exact List.Mem.head _
  | eq t u   => exact List.Mem.head _
  | impl a b => exact List.Mem.head _
  | «forall» a => exact List.Mem.head _
  | and a b  => exact List.Mem.head _
  | or a b   => exact List.Mem.head _
  | ex a     => exact List.Mem.head _

theorem closed_mem_fcodesF : ∀ (phi : Formula) (x : Term),
    List.Mem x (fcodesF phi) → CodeClosed x
  | .bottom, x, h => by
      rw [fcodesF_bot] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · cases h'
  | .atom p ts, x, h => by
      rw [fcodesF_atom] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · cases h'
  | .eq t u, x, h => by
      rw [fcodesF_eqf] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · cases h'
  | .impl a b, x, h => by
      rw [fcodesF_impl] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_fcodesF a x hA
        · exact closed_mem_fcodesF b x hB
  | Formula.forall a, x, h => by
      rw [fcodesF_forall] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · exact closed_mem_fcodesF a x h'
  | .and a b, x, h => by
      rw [fcodesF_and] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_fcodesF a x hA
        · exact closed_mem_fcodesF b x hB
  | .or a b, x, h => by
      rw [fcodesF_or] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_fcodesF a x hA
        · exact closed_mem_fcodesF b x hB
  | .ex a, x, h => by
      rw [fcodesF_ex] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM _
      · exact closed_mem_fcodesF a x h'

/-! ############################################################################
    ## §5 · LA INDUCCION DE FORMULA — el analogo de `okE1_T`, ocho casos.

    `WF` es abstracto (solo se consulta via el ORACULO `hoF`); de `WT` se pide
    ademas clausura De Bruijn, porque el nodo `atomc` construye un `∀` acotado.
    ############################################################################ -/

/-! Atajos de pertenencia (para que los `by` en linea quepan en una linea). -/
theorem memL {y : Term} {L R : List Term} (z : Term) (hy : List.Mem y L) :
    List.Mem y (z :: (L ++ R)) := List.Mem.tail _ (List.mem_append.mpr (Or.inl hy))
theorem memR {y : Term} {L R : List Term} (z : Term) (hy : List.Mem y R) :
    List.Mem y (z :: (L ++ R)) := List.Mem.tail _ (List.mem_append.mpr (Or.inr hy))
theorem memA {y : Term} {L R : List Term} (hy : List.Mem y L) :
    List.Mem y (L ++ R) := List.mem_append.mpr (Or.inl hy)
theorem memB {y : Term} {L R : List Term} (hy : List.Mem y R) :
    List.Mem y (L ++ R) := List.mem_append.mpr (Or.inr hy)

theorem okF : ∀ (phi : Formula) (WF WT : Term)
    (_hWTl : ∀ c : Nat, liftTerm c WT = WT)
    (_hWTs : ∀ (v : Nat) (s : Term), substTerm v s WT = WT)
    (_hoF : ∀ y : Term, List.Mem y (fcodesF phi) → Prf (In y WF))
    (_hoT : ∀ y : Term, List.Mem y (tcodesF phi) → Prf (In y WT))
    (x : Term), List.Mem x (fcodesF phi) → Prf (isFormCodeE2 WF WT x)
  | .bottom, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      rw [fcodesF_bot] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact inj_bot prf_clBot_bot
      · cases h'
  | .atom p ts, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      rw [fcodesF_atom] at h
      rcases List.mem_cons.mp h with rfl | h'
      · refine inj_atom ?_
        simp only [formCodeM]
        refine prf_clAtom_cons WT (strCodeM p) ts (hWTl 0) hWTs ?_
        intro u hu
        exact hoT (termCodeM u)
          (by rw [tcodesF_atom]; exact mem_tcodes1s_of_mem ts u hu)
      · cases h'
  | .eq t u, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      rw [fcodesF_eqf] at h
      rcases List.mem_cons.mp h with rfl | h'
      · refine inj_eq ?_
        simp only [formCodeM]
        refine prf_clEq_cons WT (termCodeM t) (termCodeM u) ?_ ?_
        · exact hoT (termCodeM t)
            (by rw [tcodesF_eqf]; exact mem_tcodes1s_of_mem [t, u] t (List.Mem.head _))
        · exact hoT (termCodeM u)
            (by rw [tcodesF_eqf]
                exact mem_tcodes1s_of_mem [t, u] u (List.Mem.tail _ (List.Mem.head _)))
      · cases h'
  | .impl a b, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      rw [fcodesF_impl] at h
      rcases List.mem_cons.mp h with rfl | h'
      · refine inj_bin5 ?_
        simp only [formCodeM]
        refine prf_clBin_cons WF 5 (formCodeM a) (formCodeM b) ?_ ?_
        · exact hoF _ (by rw [fcodesF_impl]; exact memL _ (mem_self_fcodesF a))
        · exact hoF _ (by rw [fcodesF_impl]; exact memR _ (mem_self_fcodesF b))
      · rcases List.mem_append.mp h' with hA | hB
        · exact okF a WF WT hWTl hWTs
            (fun y hy => hoF y (by rw [fcodesF_impl]; exact memL _ hy))
            (fun y hy => hoT y (by rw [tcodesF_impl]; exact memA hy)) x hA
        · exact okF b WF WT hWTl hWTs
            (fun y hy => hoF y (by rw [fcodesF_impl]; exact memR _ hy))
            (fun y hy => hoT y (by rw [tcodesF_impl]; exact memB hy)) x hB
  | Formula.forall a, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      rw [fcodesF_forall] at h
      rcases List.mem_cons.mp h with rfl | h'
      · refine inj_un6 ?_
        simp only [formCodeM]
        refine prf_clUn_cons WF 6 (formCodeM a) ?_
        exact hoF _ (by rw [fcodesF_forall]; exact List.Mem.tail _ (mem_self_fcodesF a))
      · exact okF a WF WT hWTl hWTs
          (fun y hy => hoF y (by rw [fcodesF_forall]; exact List.Mem.tail _ hy))
          (fun y hy => hoT y (by rw [tcodesF_forall]; exact hy)) x h'
  | .and a b, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      rw [fcodesF_and] at h
      rcases List.mem_cons.mp h with rfl | h'
      · refine inj_bin7 ?_
        simp only [formCodeM]
        refine prf_clBin_cons WF 7 (formCodeM a) (formCodeM b) ?_ ?_
        · exact hoF _ (by rw [fcodesF_and]; exact memL _ (mem_self_fcodesF a))
        · exact hoF _ (by rw [fcodesF_and]; exact memR _ (mem_self_fcodesF b))
      · rcases List.mem_append.mp h' with hA | hB
        · exact okF a WF WT hWTl hWTs
            (fun y hy => hoF y (by rw [fcodesF_and]; exact memL _ hy))
            (fun y hy => hoT y (by rw [tcodesF_and]; exact memA hy)) x hA
        · exact okF b WF WT hWTl hWTs
            (fun y hy => hoF y (by rw [fcodesF_and]; exact memR _ hy))
            (fun y hy => hoT y (by rw [tcodesF_and]; exact memB hy)) x hB
  | .or a b, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      rw [fcodesF_or] at h
      rcases List.mem_cons.mp h with rfl | h'
      · refine inj_bin8 ?_
        simp only [formCodeM]
        refine prf_clBin_cons WF 8 (formCodeM a) (formCodeM b) ?_ ?_
        · exact hoF _ (by rw [fcodesF_or]; exact memL _ (mem_self_fcodesF a))
        · exact hoF _ (by rw [fcodesF_or]; exact memR _ (mem_self_fcodesF b))
      · rcases List.mem_append.mp h' with hA | hB
        · exact okF a WF WT hWTl hWTs
            (fun y hy => hoF y (by rw [fcodesF_or]; exact memL _ hy))
            (fun y hy => hoT y (by rw [tcodesF_or]; exact memA hy)) x hA
        · exact okF b WF WT hWTl hWTs
            (fun y hy => hoF y (by rw [fcodesF_or]; exact memR _ hy))
            (fun y hy => hoT y (by rw [tcodesF_or]; exact memB hy)) x hB
  | .ex a, WF, WT, hWTl, hWTs, hoF, hoT, x, h => by
      rw [fcodesF_ex] at h
      rcases List.mem_cons.mp h with rfl | h'
      · refine inj_un9 ?_
        simp only [formCodeM]
        refine prf_clUn_cons WF 9 (formCodeM a) ?_
        exact hoF _ (by rw [fcodesF_ex]; exact List.Mem.tail _ (mem_self_fcodesF a))
      · exact okF a WF WT hWTl hWTs
          (fun y hy => hoF y (by rw [fcodesF_ex]; exact List.Mem.tail _ hy))
          (fun y hy => hoT y (by rw [tcodesF_ex]; exact hy)) x h'

/-! ############################################################################
    ## §6 · EL ENSAMBLAJE
    ############################################################################ -/

theorem prf_wfAllF_fcodesF (phi : Formula) :
    Prf (wfAllF (objList (fcodesF phi)) (objList (tcodesF phi))) := by
  let LF : List Term := fcodesF phi
  let LT : List Term := tcodesF phi
  let WF : Term := objList LF
  let WT : Term := objList LT
  have hWFl : ∀ c : Nat, liftTerm c WF = WF := fun c =>
    liftTerm_objList c LF (fun x hx => (closed_mem_fcodesF phi x hx).1 c)
  have hWFs : ∀ (v : Nat) (s : Term), substTerm v s WF = WF := fun v s =>
    substTerm_objList v s LF (fun x hx => (closed_mem_fcodesF phi x hx).2 v s)
  have hWTl : ∀ c : Nat, liftTerm c WT = WT := fun c =>
    liftTerm_objList c LT (fun x hx => (closed_mem_tcodes1s (termsOfF phi) x hx).1 c)
  have hWTs : ∀ (v : Nat) (s : Term), substTerm v s WT = WT := fun v s =>
    substTerm_objList v s LT (fun x hx => (closed_mem_tcodes1s (termsOfF phi) x hx).2 v s)
  have hoF : ∀ y : Term, List.Mem y LF → Prf (In y WF) := fun y hy => prf_In_objList LF y hy
  have hoT : ∀ y : Term, List.Mem y LT → Prf (In y WT) := fun y hy => prf_In_objList LT y hy
  have hAI : wfAllF WF WT
      = Formula.forall (Formula.impl (lt (.var 0) (lenc WF))
          (isFormCodeE2 WF WT (nthc WF (.var 0)))) := by
    simp only [wfAllF, wfAllFBody, lt, lenc, nthc, liftTerm, liftTerms, hWFl, hWTl]
  rw [hAI]
  refine prf_bdAll_of_bound _ (lenc WF) LF.length ?_ (prf_lenc_objList LF) ?_
  · simp only [substF_isFormCodeE2, nthc, substTerm, substTerms, hWFs, hWTs, if_true]
  · intro k hk
    obtain ⟨x, hx⟩ : ∃ x, LF[k]? = some x := ⟨LF[k], getElem?_pos LF k hk⟩
    have hnode : Prf (isFormCodeE2 WF WT x) :=
      okF phi WF WT hWTl hWTs hoF hoT x (mem_of_getElem? LF k x hx)
    have hres : Prf (isFormCodeE2 WF WT (nthc WF (numeralM k))) :=
      prfH_nil_to_prf (PrfH_congr_isFormCodeE2
        (prf_to_prfH (prf_eq_symm (prf_nthc_objList LF k x hx)) [])
        (prf_to_prfH hnode [])) rfl
    simpa only [substF_isFormCodeE2, nthc, substTerm, substTerms, hWFs, hWTs,
      substTerm_numeralM, if_true, reduceIte] using hres

theorem prf_wfAll1_tcodesF (phi : Formula) : Prf (wfAll1 (objList (tcodesF phi))) :=
  prf_wfAll1_tcodes1s (termsOfF phi)

/-- **★ LA NO-VACUIDAD, CON TESTIGOS EXPLICITOS Y COMPUTABLES ★**
    La guarda de `pcc_eval_substfc` la satisface TODO codigo de formula REAL. -/
theorem prf_isFC1_real (phi : Formula) :
    Prf (isFC1 (objList (fcodesF phi)) (objList (tcodesF phi)) (formCodeM phi)) :=
  prf_and_intro
    (prf_and_intro (prf_wfAll1_tcodesF phi) (prf_wfAllF_fcodesF phi))
    (prf_In_objList (fcodesF phi) (formCodeM phi) (mem_self_fcodesF phi))

/-- **★ `prf_hasWitF_real` ★** — la forma con los DOS testigos CUANTIFICADOS, que es
    la que consume `pcc_eval_substfc_wit`. -/
theorem prf_hasWitF_real (phi : Formula) : Prf (hasWitF (formCodeM phi)) := by
  have hWFl : ∀ c : Nat, liftTerm c (objList (fcodesF phi)) = objList (fcodesF phi) :=
    fun c => liftTerm_objList c (fcodesF phi)
      (fun x hx => (closed_mem_fcodesF phi x hx).1 c)
  have hWFs : ∀ (v : Nat) (s : Term),
      substTerm v s (objList (fcodesF phi)) = objList (fcodesF phi) :=
    fun v s => substTerm_objList v s (fcodesF phi)
      (fun x hx => (closed_mem_fcodesF phi x hx).2 v s)
  show Prf (Formula.ex (Formula.ex
    (isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (formCodeM phi))))))
  refine prf_ex_intro (objList (fcodesF phi)) ?_
  have e0 : (0 = 1) = False := eq_false (by omega)
  have e1 : (0 > 1) = False := eq_false (by omega)
  have h1 : substFormula 0 (objList (fcodesF phi)) (Formula.ex
        (isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (formCodeM phi)))))
      = Formula.ex (isFC1 (objList (fcodesF phi)) (.var 0) (formCodeM phi)) := by
    simp only [substFormula, substF_isFC1, substTerm, liftTerm_formCodeM,
      substTerm_formCodeM, hWFl, hWFs, Nat.reduceAdd, e0, e1, if_false, reduceIte, if_true]
  rw [h1]
  refine prf_ex_intro (objList (tcodesF phi)) ?_
  have h2 : substFormula 0 (objList (tcodesF phi))
        (isFC1 (objList (fcodesF phi)) (.var 0) (formCodeM phi))
      = isFC1 (objList (fcodesF phi)) (objList (tcodesF phi)) (formCodeM phi) := by
    simp only [substF_isFC1, substTerm, hWFs, substTerm_formCodeM, if_true]
  rw [h2]
  exact prf_isFC1_real phi

/-- La gemela de TERMINO, que la guarda completa de `pcc_eval_substfc_wit` tambien pide
    (`land (hasWit s) (hasWitF f)`): para el sustituyendo `s`. -/
theorem prf_hasWit_real (t : Term) : Prf (hasWit (termCodeM t)) := by
  refine prf_ex_intro (objList (tcodes1 t)) ?_
  have h : substFormula 0 (objList (tcodes1 t)) (isTC1 (.var 0) (liftTerm 0 (termCodeM t)))
      = isTC1 (objList (tcodes1 t)) (termCodeM t) := by
    simp only [substF_isTC1, substTerm, if_true, FOL.substTerm_liftTerm]
  rw [h]
  exact prf_isTC1_tcodes t

/-- **★ LA GUARDA ENTERA DE `ENS.pcc_eval_substfc_wit`, DESCARGADA ★**

    `ENS.pcc_eval_substfc_wit (v s f) : Prf (land (hasWit s) (hasWitF f) ⇒ targetSubstfc v s f)`.
    Este es su ANTECEDENTE instanciado en codigos REALES: `s := ⌜t⌝ₜ`, `f := ⌜phi⌝`.
    O sea que `pcc_eval_substfc` **no es vacio**: se aplica a todo `t` y todo `phi`. -/
theorem prf_guard_substfc_real (t : Term) (phi : Formula) :
    Prf (land (hasWit (termCodeM t)) (hasWitF (formCodeM phi))) :=
  prf_and_intro (prf_hasWit_real t) (prf_hasWitF_real phi)

end HWDesdeTermino

/-! ############################################################################
    ## §7 · CONTROLES
    ############################################################################ -/

namespace HWDesdeTermino
section CONTROLES

/-! ### C1 · Las definiciones copiadas son las de `ENS`, desplegadas en simbolos
       de PRODUCCION (nada de `rfl` circular contra mi propia copia). -/

example (wF wT c : Term) :
    isFC1 wF wT c
      = Formula.and
          (Formula.and
            (Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc wT)))
              (isTermCodeE1 (liftTerm 0 wT) (nthc (liftTerm 0 wT) (.var 0)))))
            (Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc wF)))
              (isFormCodeE2 (liftTerm 0 wF) (liftTerm 0 wT) (nthc (liftTerm 0 wF) (.var 0))))))
          (In c wF) := rfl

example (wF wT X : Term) :
    isFormCodeE2 wF wT X
      = lor (Formula.eq X (cons (numeralM 2) nil))
         (lor (land (Formula.eq X (cons (numeralM 3)
                 (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))))
                (Formula.forall (Formula.impl
                  (lt (.var 0) (liftTerm 0 (lenc (nthc X (numeralM 2)))))
                  (In (nthc (liftTerm 0 (nthc X (numeralM 2))) (.var 0)) (liftTerm 0 wT)))))
          (lor (clEq wT X)
           (lor (clBin wF X 5)
            (lor (clUn wF X 6)
             (lor (clBin wF X 7)
              (lor (clBin wF X 8) (clUn wF X 9))))))) := rfl

example (c : Term) :
    hasWitF c = Formula.ex (Formula.ex (isFC1 (.var 1) (.var 0)
      (liftTerm 0 (liftTerm 0 c)))) := rfl

/-! ### C2 · `argsIn` es POSICIONAL: NO pide la lista de argumentos como objeto en `wT`.
       (Era el riesgo señalado en el encargo; queda MEDIDO y descartado.) -/

example (wT Y : Term) :
    argsIn wT Y
      = Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
          (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))) := rfl

example (wT Y : Term) : True := by
  fail_if_success exact (rfl : argsIn wT Y = In Y wT)
  trivial

/-! ### C3 · Los testigos NO son triviales: un elemento por subformula / subtermino. -/

def phiA : Formula := Formula.eq (Term.func "f" [Term.var 0]) (Term.var 1)
def phiB : Formula :=
  Formula.impl (Formula.atom "P" [Term.func "g" [Term.var 0]]) (Formula.forall phiA)

example : (fcodesF phiA).length = 1 := by rfl
example : (tcodesF phiA).length = 3 := by rfl
example : (fcodesF phiB).length = 4 := by rfl
example : (tcodesF phiB).length = 5 := by rfl

/-! ### C4 · Instancias CONCRETAS del teorema. -/

theorem CTRL_A : Prf (isFC1 (objList (fcodesF phiA)) (objList (tcodesF phiA)) (formCodeM phiA)) :=
  prf_isFC1_real phiA
theorem CTRL_B : Prf (isFC1 (objList (fcodesF phiB)) (objList (tcodesF phiB)) (formCodeM phiB)) :=
  prf_isFC1_real phiB
theorem CTRL_B_wit : Prf (hasWitF (formCodeM phiB)) := prf_hasWitF_real phiB
theorem CTRL_B_guard :
    Prf (land (hasWit (termCodeM (Term.func "f" [Term.var 0]))) (hasWitF (formCodeM phiB))) :=
  prf_guard_substfc_real (Term.func "f" [Term.var 0]) phiB

/-! ### C4b · LOS TESTIGOS SON LIMPIOS: `wF` sólo contiene codigos de FORMULA y `wT`
       sólo codigos de TERMINO. Es el invariante que hace que la DISCRIMINACION ya
       probada (`EvalSubstfcPrf.lean` §14: `CRIT_isFC1_rejects_varc`,
       `CRIT_E2_rejects_varc`, `CRIT_E2_rejects_funcc`) aplique a estas listas: no hay
       ningun `varc`/`funcc` metido en `wF` ni ningun codigo de formula en `wT`. -/

theorem fcodesF_only_formCodes : ∀ (phi : Formula) (x : Term),
    List.Mem x (fcodesF phi) → ∃ ψ : Formula, x = formCodeM ψ
  | .bottom, x, h => by
      rw [fcodesF_bot] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨Formula.bottom, rfl⟩
      · cases h'
  | .atom p ts, x, h => by
      rw [fcodesF_atom] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨Formula.atom p ts, rfl⟩
      · cases h'
  | .eq t u, x, h => by
      rw [fcodesF_eqf] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨Formula.eq t u, rfl⟩
      · cases h'
  | .impl a b, x, h => by
      rw [fcodesF_impl] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨Formula.impl a b, rfl⟩
      · rcases List.mem_append.mp h' with hA | hB
        · exact fcodesF_only_formCodes a x hA
        · exact fcodesF_only_formCodes b x hB
  | Formula.forall a, x, h => by
      rw [fcodesF_forall] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨Formula.forall a, rfl⟩
      · exact fcodesF_only_formCodes a x h'
  | .and a b, x, h => by
      rw [fcodesF_and] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨Formula.and a b, rfl⟩
      · rcases List.mem_append.mp h' with hA | hB
        · exact fcodesF_only_formCodes a x hA
        · exact fcodesF_only_formCodes b x hB
  | .or a b, x, h => by
      rw [fcodesF_or] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨Formula.or a b, rfl⟩
      · rcases List.mem_append.mp h' with hA | hB
        · exact fcodesF_only_formCodes a x hA
        · exact fcodesF_only_formCodes b x hB
  | .ex a, x, h => by
      rw [fcodesF_ex] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨Formula.ex a, rfl⟩
      · exact fcodesF_only_formCodes a x h'

mutual
theorem tcodes1_only_termCodes : ∀ (t x : Term),
    List.Mem x (tcodes1 t) → ∃ u : Term, x = termCodeM u
  | .var n, x, h => by
      simp only [tcodes1] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨Term.var n, rfl⟩
      · cases h'
  | .func s ts, x, h => by
      simp only [tcodes1] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨Term.func s ts, rfl⟩
      · exact tcodes1s_only_termCodes ts x h'
theorem tcodes1s_only_termCodes : ∀ (ts : List Term) (x : Term),
    List.Mem x (tcodes1s ts) → ∃ u : Term, x = termCodeM u
  | [], x, h => by simp only [tcodes1s] at h; cases h
  | t :: ts, x, h => by
      simp only [tcodes1s] at h
      rcases List.mem_append.mp h with hA | hB
      · exact tcodes1_only_termCodes t x hA
      · exact tcodes1s_only_termCodes ts x hB
end

theorem tcodesF_only_termCodes (phi : Formula) (x : Term)
    (h : List.Mem x (tcodesF phi)) : ∃ u : Term, x = termCodeM u :=
  tcodes1s_only_termCodes (termsOfF phi) x h

/-! ### C5 · Los enunciados no son reflexividades disfrazadas. -/

example (wF wT X : Term) : True := by
  fail_if_success exact (rfl : isFormCodeE2 wF wT X = isTermCodeE1 wT X)
  trivial

example (phi : Formula) : True := by
  fail_if_success exact (rfl : fcodesF phi = tcodesF phi)
  trivial

/-- El testigo de FORMULA NO contiene codigos de TERMINO (por eso hace falta el
    segundo): para `phiA` son listas DISJUNTAS en longitud y en contenido. -/
example : fcodesF phiA = [formCodeM phiA] := rfl
example : tcodesF phiA
    = [termCodeM (Term.func "f" [Term.var 0]), termCodeM (Term.var 0), termCodeM (Term.var 1)] :=
  rfl

end CONTROLES
end HWDesdeTermino

#print axioms HWDesdeTermino.prf_wfAll1_tcodes1s
#print axioms HWDesdeTermino.prf_isTC1_tcodes
#print axioms HWDesdeTermino.okF
#print axioms HWDesdeTermino.prf_wfAllF_fcodesF
#print axioms HWDesdeTermino.prf_wfAll1_tcodesF
#print axioms HWDesdeTermino.prf_isFC1_real
#print axioms HWDesdeTermino.prf_hasWitF_real
#print axioms HWDesdeTermino.prf_hasWit_real
#print axioms HWDesdeTermino.prf_guard_substfc_real
#print axioms HWDesdeTermino.CTRL_B_guard
#print axioms HWDesdeTermino.CTRL_A
#print axioms HWDesdeTermino.CTRL_B
#print axioms HWDesdeTermino.CTRL_B_wit
#print axioms HWDesdeTermino.fcodesF_only_formCodes
#print axioms HWDesdeTermino.tcodesF_only_termCodes

#check @HWDesdeTermino.prf_isFC1_real
#check @HWDesdeTermino.prf_hasWitF_real
#check @HWDesdeTermino.fcodesF
#check @HWDesdeTermino.tcodesF
