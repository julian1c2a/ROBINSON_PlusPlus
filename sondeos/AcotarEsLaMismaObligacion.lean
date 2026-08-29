/-
# CRÍTICA ADVERSARIAL de `Probe/Lift_acotar.lean`

    lake env lean Probe/CritLift_acotar.lean

Lo que se concede del original (recompilado: EXITCODE 0, 0 errores, 0 warnings, net‑0):
la equivalencia §3/§3.1 (ACOTAR ⇒ CLAUSURA y CLAUSURA ⇒ ACOTAR) es correcta, y la
expresabilidad de la iteración por la CADENA también.

Lo que este fichero MIDE en contra:

* **§1 — el diagnóstico de §6 está MAL ATRIBUIDO.** El informe cierra con «`PasoClausura`
  no se puede dar hoy» y lo achaca al símbolo que falta (`map` de `liftsc`). Falso como
  causa: para TODO `x` que sea un **código** (`x = termCode t`, `t` meta abstracto) la
  clausura sale de PRODUCCIÓN en una línea y **sin ningún map** (`prf_liftTerm_arith`).
  La obstrucción no es el vocabulario: es que en `PasoClausura` el argumento `x` es un
  `Term` ABSTRACTO del que sólo se tiene un testigo OBJETO. Que es justo lo que §3 mide.

* **§2 — el «no existe el map» es una ausencia de SÍMBOLO DE FUNCIÓN, no de expresión.**
  El propio §2 del original enseña el truco: una operación que no tiene símbolo se
  expresa como RELACIÓN con cuantificación acotada. Aplicado al map de `liftsc`
  (`mapLiftscOk`) sale con símbolos EXISTENTES (censo por `rfl`) y es DESCARGABLE
  net‑0 a longitud concreta con elementos ABSTRACTOS. Lo que queda abierto —y que §6
  no formula— es la versión de longitud ABSTRACTA, que pide inducción objeto, no un
  símbolo.

* **§3 — la equivalencia §3.1 es CASI DEFINICIONAL.** `chainT 1 s` es, por `rfl`,
  `cons s (cons (liftc zero s) nil)`, así que la meta de `Via3UnPiso` es la meta de
  `PasoClausura` módulo una ecuación demostrable. El contenido real del resultado no
  está en la equivalencia sino en la decisión de cuantificar sobre `s` ABSTRACTO — que
  es correcta (en `sondeos/Paso2CasoForall.lean` `paso2_caso_forall (v s f : Term)` los
  tres son abstractos), pero eso NO se establece dentro del fichero criticado.
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
open ROBINSON_PlusPlus.Meta.NatArithPrf ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.ChainPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace CritLiftAcotar

/-! ## §0 · Definiciones — COPIA LITERAL de `sondeos/DiscriminaEcuacional.lean` §1
     (idénticas, carácter a carácter, a las del fichero criticado). -/

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

def bndT  (p : Term) : Term := lenc (carc p)
def bndTs (p : Term) : Term := lenc (cdrc p)

def wfAllT (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndT p)))
    (isTermCodeB (liftTerm 0 (carc p)) (liftTerm 0 (cdrc p))
      (nthc (liftTerm 0 (carc p)) (.var 0))))

def wfAllTs (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndTs p)))
    (isTermsCodeB (liftTerm 0 (carc p)) (liftTerm 0 (cdrc p))
      (nthc (liftTerm 0 (cdrc p)) (.var 0))))

def pairOk (p : Term) : Formula := land (wfAllT p) (wfAllTs p)

def isTCB (p c : Term) : Formula := land (pairOk p) (In c (carc p))

theorem prf_congr_In_left {u v w : Term} (h : Prf (u =eq v)) (hin : Prf (In u w)) :
    Prf (In v w) := by
  let f : Formula := In (.var 0) (liftTerm 0 w)
  have hS : ∀ s : Term, substFormula 0 s f = In s w := by
    intro s
    simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS v) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h []) ((hS u) ▸ prf_to_prfH hin [])) rfl

/-- Copia del `∀` acotado con cota numeral (idéntica a la del fichero criticado). -/
theorem prf_bdAll_numeral (Φ : Formula) (hΦ : substFormula 0 (.var 0) Φ = Φ) : ∀ (n : Nat),
    (∀ k : Nat, k < n → Prf (substFormula 0 (numeralM k) Φ)) →
      Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM n)) Φ))
  | 0, _ => by
      refine Prf.gen _ (prf_deduction ?_)
      exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq Φ))
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

/-! ## §1 · EL DIAGNÓSTICO DE §6 ESTÁ MAL ATRIBUIDO
     La clausura para CÓDIGOS sale de producción, sin map y sin símbolo nuevo. -/

/-- `liftc zero` sobre un CÓDIGO baja al `liftTerm 0` meta. **Producción**
    (`Meta/ArithPrf.lean`, `prf_liftTerm_arith`); `numeral 0 = zero` es `rfl`. -/
theorem prf_liftc_termCode (t : Term) :
    Prf (liftc zero (termCode t) =eq termCode (liftTerm 0 t)) :=
  prf_liftTerm_arith 0 t

/-- Hito (i) del frente, como PARÁMETRO (está probado net‑0 en
    `sondeos/DiscriminaEcuacional.lean`: `prf_isTCB_subCodesT (t) : Prf (isTCB (pairT t)
    (termCodeM t))`, y `termCodeM_eq` identifica `termCodeM` con `termCode`). -/
def HitoI : Type := ∀ u : Term, { p : Term // Prf (isTCB p (termCode u)) }

/-- **La clausura de un paso, RESTRINGIDA A CÓDIGOS, es una línea.**
    Ni `map` de `liftsc`, ni símbolo nuevo, ni axioma: sólo `prf_liftTerm_arith` + Leibniz.
    ⇒ lo que bloquea `PasoClausura` NO es el vocabulario que censa §6, sino que su `x`
    es un `Term` ABSTRACTO (no se sabe que sea un código). -/
def clausura_en_codigos (H : HitoI) (t : Term) :
    { p' : Term // Prf (isTCB p' (liftc zero (termCode t))) } :=
  ⟨(H (liftTerm 0 t)).1,
    prf_and_intro (prf_and_elim_left (H (liftTerm 0 t)).2)
      (prf_congr_In_left (prf_eq_symm (prf_liftc_termCode t))
        (prf_and_elim_right (H (liftTerm 0 t)).2))⟩

/-- Y la ITERACIÓN sobre códigos también es gratis, a cualquier profundidad `j`:
    la torre de lifts colapsa al `liftTerm` meta iterado. (Aquí es donde la vía 3 SÍ
    sería barata… si el sustituyendo fuese un código y no un `Term` abstracto.) -/
def iterLiftc : Nat → Term → Term
  | 0,     s => s
  | (j+1), s => liftc zero (iterLiftc j s)

def iterLiftTerm : Nat → Term → Term
  | 0,     t => t
  | (j+1), t => liftTerm 0 (iterLiftTerm j t)

theorem prf_iterLiftc_termCode : ∀ (j : Nat) (t : Term),
    Prf (iterLiftc j (termCode t) =eq termCode (iterLiftTerm j t))
  | 0,     t => prf_refl (termCode t)
  | (j+1), t => by
      exact prf_eq_trans (prf_congr_liftc (prf_iterLiftc_termCode j t))
        (prf_liftc_termCode (iterLiftTerm j t))

/-- **Toda la torre de testigos de la vía 3, gratis, si el sustituyendo es un CÓDIGO.** -/
def via3_en_codigos (H : HitoI) (t : Term) :
    ∀ j : Nat, { p' : Term // Prf (isTCB p' (iterLiftc j (termCode t))) } :=
  fun j =>
    ⟨(H (iterLiftTerm j t)).1,
      prf_and_intro (prf_and_elim_left (H (iterLiftTerm j t)).2)
        (prf_congr_In_left (prf_eq_symm (prf_iterLiftc_termCode j t))
          (prf_and_elim_right (H (iterLiftTerm j t)).2))⟩

/-! ## §2 · EL «MAP DE `liftsc` NO EXISTE» ES AUSENCIA DE SÍMBOLO, NO DE EXPRESIÓN

    El original resuelve en su §2 la falta de un símbolo de ITERACIÓN pasando a una
    RELACIÓN acotada. El mismo truco vale para el map que §6 declara inexistente. -/

/-- Congruencia de `liftsc` en el argumento lista (no estaba; sale por Leibniz, net‑0). -/
theorem prf_congr_liftsc {c a b : Term} (h : Prf (a =eq b)) :
    Prf (liftsc c a =eq liftsc c b) := by
  let f : Formula :=
    Formula.eq (liftsc (liftTerm 0 c) (liftTerm 0 a)) (liftsc (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (liftsc c a) (liftsc c s) := by
    intro s
    simp only [f, liftsc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ prf_leibniz_subst (A := f) h ((hS a) ▸ prf_refl (liftsc c a))

/-- ⚠️ `nil` es `zero` (Axioms.lean:126) y `simp only [zero]` no lo despliega vía `nil`:
    hacen falta los cuatro lemas locales (misma trampa que reportó el original). -/
theorem substTerm_zero_loc (v : Nat) (u : Term) : substTerm v u zero = zero := by
  simp only [zero, substTerm, substTerms]

theorem liftTerm_zero_loc (c : Nat) : liftTerm c zero = zero := by
  simp only [zero, liftTerm, liftTerms]

theorem substTerm_nil_loc (v : Nat) (u : Term) : substTerm v u nil = nil := by
  simp only [nil, zero, substTerm, substTerms]

theorem liftTerm_nil_loc (c : Nat) : liftTerm c nil = nil := by
  simp only [nil, zero, liftTerm, liftTerms]

theorem substTerm_var_self (u : Term) : substTerm 0 u (.var 0) = u := by
  simp only [substTerm, if_true]

theorem substTerm_nthc_loc (v : Nat) (u W i : Term) :
    substTerm v u (nthc W i) = nthc (substTerm v u W) (substTerm v u i) := by
  simp only [nthc, substTerm, substTerms]

theorem substTerm_liftsc0_loc (v : Nat) (u X : Term) :
    substTerm v u (liftsc zero X) = liftsc zero (substTerm v u X) := by
  simp only [liftsc, substTerm, substTerms, substTerm_zero_loc]

/-- «`W'` es el map de `liftsc zero` sobre `W`», por posiciones. Símbolos EXISTENTES. -/
def mapLiftscBody (W W' : Term) : Formula :=
  Formula.eq (nthc W' (.var 0)) (liftsc zero (nthc W (.var 0)))

def mapLiftscOk (W W' b : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) b)
    (mapLiftscBody (liftTerm 0 W) (liftTerm 0 W')))

/-- CENSO: sólo `nthc`, `liftsc`, `lt` — todos en `Minimal/Axioms.lean`. -/
theorem mapLiftscOk_censo (W W' b : Term) :
    mapLiftscOk W W' b
      = Formula.forall (Formula.impl (lt (.var 0) b)
          (Formula.eq (nthc (liftTerm 0 W') (.var 0))
                      (liftsc zero (nthc (liftTerm 0 W) (.var 0))))) := rfl

/-- **Y NO ES VACÍO**: a longitud concreta se descarga net‑0, con los elementos
    ABSTRACTOS (sólo se les pide ser cerrados, la misma hipótesis que usa el original
    en `prf_liftChainOk_chainT`). -/
theorem prf_mapLiftscOk_dos (a b : Term)
    (hal : ∀ c : Nat, liftTerm c a = a) (has : ∀ (v : Nat) (u : Term), substTerm v u a = a)
    (hbl : ∀ c : Nat, liftTerm c b = b) (hbs : ∀ (v : Nat) (u : Term), substTerm v u b = b) :
    Prf (mapLiftscOk (cons a (cons b nil))
                     (cons (liftsc zero a) (cons (liftsc zero b) nil)) (numeralM 2)) := by
  have hWl : liftTerm 0 (cons a (cons b nil)) = cons a (cons b nil) := by
    simp only [cons, liftTerm, liftTerms, hal, hbl, liftTerm_nil_loc]
  have hWs : ∀ (v : Nat) (u : Term),
      substTerm v u (cons a (cons b nil)) = cons a (cons b nil) := by
    intro v u; simp only [cons, substTerm, substTerms, has, hbs, substTerm_nil_loc]
  have hW'l : liftTerm 0 (cons (liftsc zero a) (cons (liftsc zero b) nil))
      = cons (liftsc zero a) (cons (liftsc zero b) nil) := by
    simp only [cons, liftsc, liftTerm, liftTerms, hal, hbl, liftTerm_zero_loc, liftTerm_nil_loc]
  have hW's : ∀ (v : Nat) (u : Term),
      substTerm v u (cons (liftsc zero a) (cons (liftsc zero b) nil))
        = cons (liftsc zero a) (cons (liftsc zero b) nil) := by
    intro v u
    simp only [cons, liftsc, substTerm, substTerms, has, hbs, substTerm_zero_loc,
      substTerm_nil_loc]
  simp only [mapLiftscOk, hWl, hW'l]
  refine prf_bdAll_numeral
    (mapLiftscBody (cons a (cons b nil))
      (cons (liftsc zero a) (cons (liftsc zero b) nil))) ?_ 2 ?_
  · simp only [mapLiftscBody, substFormula, substTerm_nthc_loc, substTerm_liftsc0_loc,
      hWs, hW's, substTerm_var_self]
  · intro k hk
    have hnorm : ∀ m : Nat,
        substFormula 0 (numeralM m)
          (mapLiftscBody (cons a (cons b nil))
            (cons (liftsc zero a) (cons (liftsc zero b) nil)))
          = Formula.eq (nthc (cons (liftsc zero a) (cons (liftsc zero b) nil)) (numeralM m))
              (liftsc zero (nthc (cons a (cons b nil)) (numeralM m))) := by
      intro m
      simp only [mapLiftscBody, substFormula, substTerm_nthc_loc, substTerm_liftsc0_loc,
        hWs, hW's, substTerm_var_self]
    have hk2 : Or (k = 0) (k = 1) := by omega
    rcases hk2 with rfl | rfl
    · rw [hnorm 0]
      exact prf_eq_trans (prf_nthc_zero (liftsc zero a) (cons (liftsc zero b) nil))
        (prf_eq_symm (prf_congr_liftsc (prf_nthc_zero a (cons b nil))))
    · rw [hnorm 1]
      have hL : Prf (nthc (cons (liftsc zero a) (cons (liftsc zero b) nil)) (numeralM 1)
          =eq liftsc zero b) :=
        prf_eq_trans (prf_nthc_succ (liftsc zero a) (cons (liftsc zero b) nil) (numeralM 0))
          (prf_nthc_zero (liftsc zero b) nil)
      have hR : Prf (nthc (cons a (cons b nil)) (numeralM 1) =eq b) :=
        prf_eq_trans (prf_nthc_succ a (cons b nil) (numeralM 0)) (prf_nthc_zero b nil)
      exact prf_eq_trans hL (prf_eq_symm (prf_congr_liftsc hR))

/-! ## §3 · LA EQUIVALENCIA §3.1 ES CASI DEFINICIONAL

    `chainT 1 s` es, por `rfl`, la lista de DOS casillas `[s, liftc zero s]`; la meta de
    `Via3UnPiso` («testigo de la casilla 1») es la meta de `PasoClausura` módulo la
    ecuación `nthc [s, liftc 0 s] 1̄ =eq liftc 0 s`, que es producción pura. El resultado
    NO está en la equivalencia: está en cuantificar sobre `s` ABSTRACTO. -/

def chainT : Nat → Term → Term
  | 0,     s => cons s nil
  | (j+1), s => cons s (chainT j (liftc zero s))

theorem chainT_uno (s : Term) : chainT 1 s = cons s (cons (liftc zero s) nil) := rfl

theorem prf_casilla_uno (s : Term) :
    Prf (nthc (chainT 1 s) (numeralM 1) =eq liftc zero s) :=
  prf_eq_trans (prf_nthc_succ s (cons (liftc zero s) nil) (numeralM 0))
    (prf_nthc_zero (liftc zero s) nil)

/-! ## §4 · CENSO DE LO QUE EL ORIGINAL NO MIDE

    `acotarPremisa` / `chainWitnessed` (la lectura de la vía 3 en la que la cadena se
    PIDE COMO PREMISA en vez de construirse) aparecen en `Probe/Lift_acotar.lean`
    exactamente DOS veces: en su propia definición y en el `rfl` de censo
    `acotarPremisa_shape`. Ningún teorema del fichero las consume. Esa lectura —la única
    bajo la cual la vía 3 podría ser más barata que la clausura— queda EXPRESADA y NO
    MEDIDA. (Verificado con `grep -n "acotarPremisa\|chainWitnessed"`.) -/

end CritLiftAcotar

#print axioms CritLiftAcotar.prf_liftc_termCode
#print axioms CritLiftAcotar.clausura_en_codigos
#print axioms CritLiftAcotar.prf_iterLiftc_termCode
#print axioms CritLiftAcotar.via3_en_codigos
#print axioms CritLiftAcotar.prf_congr_liftsc
#print axioms CritLiftAcotar.mapLiftscOk_censo
#print axioms CritLiftAcotar.prf_mapLiftscOk_dos
#print axioms CritLiftAcotar.chainT_uno
#print axioms CritLiftAcotar.prf_casilla_uno
