/-
# VÍA 3 — **ACOTAR** el número de lifts. Medida.

Fichero AUTOCONTENIDO (`import ROBINSON_PlusPlus.Meta` y nada más).

    lake env lean Probe/Lift_acotar.lean

## La pregunta

El caso `∀`/`∃` del PASO 2 (`pcc_eval_substfc`) cierra entero salvo

    hLift : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))))

(`sondeos/Paso2CasoForall.lean`, `paso2_caso_forall`), o sea `pcc_eval_liftc`, que pide
`isTermCode s`; y a la siguiente profundidad de binder pide `isTermCode (liftc zero s)`,
o sea CLAUSURA de `isTermCode` bajo `liftc zero`.

VÍA 3 (recomendación del crítico): no hace falta clausura, basta que el testigo contenga
`liftc 0` iterado `j` veces para `j ≤ cota`, con la cota = profundidad de binders de `f`.

**PRIMER OBSTÁCULO, que este fichero resuelve antes que nada**: «liftc 0 iterado j veces»
NO es `liftc j`. ¿Se puede EXPRESAR en el lenguaje objeto sin añadir símbolo?

## VEREDICTO

**§1 — el obstáculo de expresividad NO existe.** `iterLiftc` es una recursión META que
produce anidamientos del símbolo `liftc` que YA está en la teoría (§1.1), y la propiedad
«L es la cadena de lifts» se expresa con símbolos EXISTENTES por el truco de la CADENA
(relación de UN paso, cuantificada acotadamente): §2. Compilado, net‑0, con `s` ABSTRACTO
(cerrado) y `n` concreto. **CERO símbolos nuevos.**

**§3 — pero la vía 3 NO CIERRA, y por una razón peor que la de expresividad: es la MISMA
obligación.** Se demuestra una EQUIVALENCIA, en las dos direcciones y compilada:

* `acotar_da_clausura` — los datos de la vía 3 **a UN solo piso** ya SON un testigo de
  `liftc zero s`. O sea: ACOTAR ⇒ CLAUSURA (instancia a instancia).
* `clausura_da_acotar` — y al revés, con la clausura de un paso se fabrica la cadena
  ENTERA con sus testigos, por recursión META en `n`.

⇒ **ACOTAR ≡ CLAUSURA.** Acotar no es una ruta más barata: es la misma ruta con
contabilidad extra (una lista `L`, una lista de testigos `P`, dos conjuntos nuevos y una
comparación de cota). No compra nada.

**§4 — y encima la cota es ABSTRACTA.** La construcción de §2 es una recursión META en `n`;
sirve para `n` concreto. En el uso real `f` es un CÓDIGO ABSTRACTO (los 7 reflectores llevan
`substfc`/`liftfc` sobre argumento abstracto), luego su profundidad de binders no es un `Nat`
de Lean, y la cadena habría que producirla con una existencia OBJETO cuyo paso inductivo es,
otra vez, `clausura_da_acotar`, o sea la clausura de un paso.

**§6 — y el símbolo nuevo, si acaso, hace falta en la CLAUSURA, no en la iteración.** Censo del
vocabulario: los únicos `map` de la teoría son `liftsc` (map de `liftc`) y `substtsc` (map de
`substtc`). La mitad `wT` del testigo se mapea GRATIS con `liftsc zero`; la mitad `wTs` (lista
de códigos de LISTA de términos) pediría un map DE `liftsc`, que **no está en el censo**.

## Símbolos nuevos: NINGUNO
`iterLiftc` y `chainT` son funciones de **Lean** `Nat → Term → Term`; su salida es un árbol
de `Term.func "liftc"`/`Term.func "cons"` ya existentes. No hay ningún `Term.func` con nombre
nuevo en este fichero (censo en §5 por `rfl`).
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

namespace LiftAcotar

/-! ## §0 · Las definiciones del testigo, copiadas de `sondeos/DiscriminaEcuacional.lean` §1 -/

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

/-- `p` es un par de testigos VÁLIDO y `c` está en la mitad de TÉRMINOS.
    (= `isTermCode c` en forma testigo‑explícita, la que usa todo el frente.) -/
def isTCB (p c : Term) : Formula := land (pairOk p) (In c (carc p))

/-! ### Leibniz en el 1er argumento de `In` (copia de `DiscriminaEcuacional` §2) -/

theorem prf_congr_In_left {u v w : Term} (h : Prf (u =eq v)) (hin : Prf (In u w)) :
    Prf (In v w) := by
  let f : Formula := In (.var 0) (liftTerm 0 w)
  have hS : ∀ s : Term, substFormula 0 s f = In s w := by
    intro s
    simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS v) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h []) ((hS u) ▸ prf_to_prfH hin [])) rfl

/-! ### El `∀` acotado con cota numeral (copia de `DiscriminaEcuacional` §3) -/

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

/-! ## §1 · `liftc 0` ITERADO: es META, y NO es `liftc j`

    `iterLiftc` es una función de **Lean**. Su salida es un árbol de `Term.func "liftc"`,
    símbolo que ya está en `Minimal/Axioms.lean:464`. **No introduce ningún símbolo.** -/

/-- `liftc zero` aplicado `j` veces. Recursión **META**. -/
def iterLiftc : Nat → Term → Term
  | 0,     s => s
  | (j+1), s => liftc zero (iterLiftc j s)

theorem iterLiftc_zero (s : Term) : iterLiftc 0 s = s := rfl
theorem iterLiftc_succ (j : Nat) (s : Term) :
    iterLiftc (j+1) s = liftc zero (iterLiftc j s) := rfl

/-- Conmutación: iterar por fuera = iterar por dentro. La usa la cadena. -/
theorem iterLiftc_push : ∀ (j : Nat) (s : Term),
    iterLiftc j (liftc zero s) = iterLiftc (j+1) s
  | 0,     s => rfl
  | (j+1), s => by simp only [iterLiftc, iterLiftc_push j s]

/-! ### §1.1 · CONTROL NEGATIVO: `iterLiftc j` ≠ `liftc j̄` — las dos caras -/

/-- Cara SINTÁCTICA: `liftc 0 (liftc 0 s)` y `liftc 2̄ s` son términos DISTINTOS. -/
theorem iter_ne_liftc_syn (s : Term) : iterLiftc 2 s ≠ liftc (numeralM 2) s := by
  intro h
  simp only [iterLiftc, liftc, numeralM, zero, succ, Term.func.injEq, List.cons.injEq] at h
  exact absurd h.2.1.1 (by simp only [zero_sym, succ_sym]; decide)

/-- Cara SEMÁNTICA (nivel META, sobre el `liftTerm` real que `liftc` aritmetiza):
    dos lifts en 0 mandan `#0 ↦ #2`; un lift en 2 deja `#0` quieto. -/
theorem iter_ne_liftc_sem :
    liftTerm 0 (liftTerm 0 (Term.var 0)) ≠ liftTerm 2 (Term.var 0) := by
  simp only [liftTerm, Nat.lt_irrefl, reduceIte, Nat.zero_lt_two]
  decide

/-! ## §2 · LA CADENA — «`liftc 0` iterado» SÍ se expresa con símbolos EXISTENTES

    Truco estándar (y ya usado en producción por `chainOk`): en vez de un símbolo de
    iteración, se pide que una LISTA cumpla la relación de UN paso entre posiciones
    consecutivas, cuantificada ACOTADAMENTE. Cero símbolos nuevos. -/

/-- El cuerpo: la posición `i+1` es el `liftc zero` de la posición `i`. -/
def liftStepBody (L : Term) : Formula :=
  Formula.eq (nthc L (succ (.var 0))) (liftc zero (nthc L (.var 0)))

/-- **`L` es una cadena de lifts hasta la cota `b`.** Enunciado OBJETO, símbolos existentes. -/
def liftChainOk (L b : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 b)) (liftStepBody (liftTerm 0 L)))

theorem liftChainOk_closed (L b : Term) (hL : liftTerm 0 L = L) (hb : liftTerm 0 b = b) :
    liftChainOk L b = Formula.forall (Formula.impl (lt (.var 0) b) (liftStepBody L)) := by
  simp only [liftChainOk, hL, hb]

/-- La cadena META `[s, liftc 0 s, liftc 0 (liftc 0 s), …]` de longitud `n+1`. -/
def chainT : Nat → Term → Term
  | 0,     s => cons s nil
  | (j+1), s => cons s (chainT j (liftc zero s))

/-! ### §2.1 · Clausura sintáctica de la cadena (para `s` cerrado) -/

theorem substTerm_zero_loc (v : Nat) (u : Term) : substTerm v u zero = zero := by
  simp only [zero, substTerm, substTerms]

theorem liftTerm_zero_loc (c : Nat) : liftTerm c zero = zero := by
  simp only [zero, liftTerm, liftTerms]

theorem substTerm_chainT : ∀ (n : Nat) (s : Term),
    (∀ (v : Nat) (u : Term), substTerm v u s = s) →
      ∀ (v : Nat) (u : Term), substTerm v u (chainT n s) = chainT n s
  | 0,     s, hs => by
      intro v u
      simp only [chainT, cons, nil, substTerm, substTerms, hs, substTerm_zero_loc]
  | (j+1), s, hs => by
      intro v u
      have hls : ∀ (v : Nat) (u : Term), substTerm v u (liftc zero s) = liftc zero s := by
        intro v u; simp only [liftc, substTerm, substTerms, hs, substTerm_zero_loc]
      simp only [chainT, cons, substTerm, substTerms, hs, substTerm_chainT j _ hls v u]

theorem liftTerm_chainT : ∀ (n : Nat) (s : Term), (∀ c : Nat, liftTerm c s = s) →
      ∀ c : Nat, liftTerm c (chainT n s) = chainT n s
  | 0,     s, hs => by
      intro c
      simp only [chainT, cons, nil, liftTerm, liftTerms, hs, liftTerm_zero_loc]
  | (j+1), s, hs => by
      intro c
      have hls : ∀ c : Nat, liftTerm c (liftc zero s) = liftc zero s := by
        intro c; simp only [liftc, liftTerm, liftTerms, hs, liftTerm_zero_loc]
      simp only [chainT, cons, liftTerm, liftTerms, hs, liftTerm_chainT j _ hls c]

theorem substTerm_iterLiftc : ∀ (j : Nat) (s : Term),
    (∀ (v : Nat) (u : Term), substTerm v u s = s) →
      ∀ (v : Nat) (u : Term), substTerm v u (iterLiftc j s) = iterLiftc j s
  | 0,     s, hs => hs
  | (j+1), s, hs => by
      intro v u
      simp only [iterLiftc, liftc, substTerm, substTerms, substTerm_zero_loc,
        substTerm_iterLiftc j s hs v u]

/-! ### §2.2 · Aritmética objeto de la cadena -/

theorem prf_lenc_chainT : ∀ (n : Nat) (s : Term),
    Prf (lenc (chainT n s) =eq numeralM (n+1))
  | 0,     s => by
      exact prf_eq_trans (prf_lenc_cons s nil) (prf_eq_congr_succ prf_lenc_nil)
  | (j+1), s => by
      exact prf_eq_trans (prf_lenc_cons s (chainT j (liftc zero s)))
        (prf_eq_congr_succ (prf_lenc_chainT j (liftc zero s)))

/-- **La casilla `k` de la cadena es `liftc 0` iterado `k` veces.**
    ⚠️ `Nat.le` EXPLÍCITO: con `open Minimal.Axioms`, `≤` resuelve al orden OBJETO. -/
theorem prf_nthc_chainT : ∀ (n k : Nat), Nat.le k n → ∀ (s : Term),
    Prf (nthc (chainT n s) (numeralM k) =eq iterLiftc k s)
  | 0,     0,     _,  s => by exact prf_nthc_zero s nil
  | (n+1), 0,     _,  s => by exact prf_nthc_zero s (chainT n (liftc zero s))
  | (n+1), (k+1), hk, s => by
      have hk' : Nat.le k n := Nat.le_of_succ_le_succ hk
      have h1 : Prf (nthc (chainT (n+1) s) (numeralM (k+1))
          =eq nthc (chainT n (liftc zero s)) (numeralM k)) := by
        exact prf_nthc_succ s (chainT n (liftc zero s)) (numeralM k)
      have h2 := prf_nthc_chainT n k hk' (liftc zero s)
      exact iterLiftc_push k s ▸ prf_eq_trans h1 h2

/-! ### §2.3 · **RESULTADO POSITIVO**: la cadena concreta ES una cadena de lifts, net‑0 -/

theorem prf_liftChainOk_chainT (n : Nat) (s : Term)
    (hs : ∀ (v : Nat) (u : Term), substTerm v u s = s)
    (hl : ∀ c : Nat, liftTerm c s = s) :
    Prf (liftChainOk (chainT n s) (numeralM n)) := by
  have hLc : liftTerm 0 (chainT n s) = chainT n s := liftTerm_chainT n s hl 0
  have hLs : ∀ (v : Nat) (u : Term), substTerm v u (chainT n s) = chainT n s :=
    substTerm_chainT n s hs
  rw [liftChainOk_closed _ _ hLc (liftTerm_numeralM 0 n)]
  refine prf_bdAll_numeral (liftStepBody (chainT n s)) ?_ n ?_
  · simp only [liftStepBody, nthc, liftc, succ, zero, substFormula, substTerm, substTerms,
      hLs, if_true]
  · intro k hk
    have hnorm : substFormula 0 (numeralM k) (liftStepBody (chainT n s))
        = Formula.eq (nthc (chainT n s) (succ (numeralM k)))
                     (liftc zero (nthc (chainT n s) (numeralM k))) := by
      simp only [liftStepBody, nthc, liftc, succ, zero, substFormula, substTerm, substTerms,
        hLs, substTerm_numeralM, if_true]
    rw [hnorm]
    have hA : Prf (nthc (chainT n s) (numeralM (k+1)) =eq iterLiftc (k+1) s) :=
      prf_nthc_chainT n (k+1) hk s
    have hB : Prf (nthc (chainT n s) (numeralM k) =eq iterLiftc k s) :=
      prf_nthc_chainT n k (Nat.le_of_succ_le hk) s
    exact prf_eq_trans hA (prf_eq_symm (prf_congr_liftc hB))

/-! ## §3 · **LA MEDIDA**: ACOTAR ≡ CLAUSURA

    La vía 3 pide, además de la cadena `L`, un testigo para CADA piso (porque `pcc_eval_liftc`
    a profundidad `j` se aplica al sustituyendo de ese piso, y pide su `isTermCode`). Ese dato
    es exactamente la clausura, y recíprocamente. -/

/-- **(⇒) Los datos de la vía 3 a UN solo piso YA SON la clausura de un paso.**
    `p₁` testigo de la casilla 1, y la casilla 1 es `liftc zero s` por la relación de cadena
    ⇒ `p₁` es testigo de `liftc zero s`. -/
theorem acotar_da_clausura (s p₁ L : Term)
    (hchain : Prf (nthc L (numeralM 1) =eq liftc zero (nthc L (numeralM 0))))
    (h0 : Prf (nthc L (numeralM 0) =eq s))
    (hw1 : Prf (isTCB p₁ (nthc L (numeralM 1)))) :
    Prf (isTCB p₁ (liftc zero s)) := by
  have heq : Prf (nthc L (numeralM 1) =eq liftc zero s) :=
    prf_eq_trans hchain (prf_congr_liftc h0)
  exact prf_and_intro (prf_and_elim_left hw1)
    (prf_congr_In_left heq (prf_and_elim_right hw1))

/-- Especialización a la cadena concreta: `chainT` cumple las dos hipótesis de arriba. -/
theorem acotar_da_clausura_chainT (n : Nat) (s p₁ : Term) (hn : Nat.le 1 n)
    (hw1 : Prf (isTCB p₁ (nthc (chainT n s) (numeralM 1)))) :
    Prf (isTCB p₁ (liftc zero s)) := by
  refine acotar_da_clausura s p₁ (chainT n s) ?_ ?_ hw1
  · have hA : Prf (nthc (chainT n s) (numeralM 1) =eq iterLiftc 1 s) :=
      prf_nthc_chainT n 1 hn s
    have hB : Prf (nthc (chainT n s) (numeralM 0) =eq iterLiftc 0 s) :=
      prf_nthc_chainT n 0 (Nat.zero_le n) s
    exact prf_eq_trans hA (prf_eq_symm (prf_congr_liftc hB))
  · exact prf_nthc_chainT n 0 (Nat.zero_le n) s

/-- El tipo del dato «clausura de UN paso, en forma testigo‑explícita». -/
def PasoClausura : Type :=
  ∀ (x p : Term), Prf (isTCB p x) → { p' : Term // Prf (isTCB p' (liftc zero x)) }

/-- **(⇐) Con la clausura de UN paso se fabrica la cadena ENTERA con sus testigos.**
    Recursión META en `n`: el piso `j` sale de aplicar `cl` `j` veces. -/
def testigoIter (cl : PasoClausura) (x p : Term) (h : Prf (isTCB p x)) :
    ∀ j : Nat, { p' : Term // Prf (isTCB p' (iterLiftc j x)) }
  | 0     => ⟨p, h⟩
  | (j+1) =>
      let r := testigoIter cl x p h j
      ⟨(cl _ r.1 r.2).1, (cl _ r.1 r.2).2⟩

/-- La cadena de la vía 3, con testigo en cada piso, a partir de la clausura de un paso.
    (Parte 1: la relación de cadena; parte 2: el testigo de cada casilla.) -/
theorem clausura_da_acotar_chain (n : Nat) (s : Term)
    (hs : ∀ (v : Nat) (u : Term), substTerm v u s = s)
    (hl : ∀ c : Nat, liftTerm c s = s) :
    Prf (liftChainOk (chainT n s) (numeralM n)) :=
  prf_liftChainOk_chainT n s hs hl

theorem clausura_da_acotar (cl : PasoClausura) (n : Nat) (s p : Term)
    (hp : Prf (isTCB p s)) (k : Nat) (hk : Nat.le k n) :
    Prf (isTCB (testigoIter cl s p hp k).1 (nthc (chainT n s) (numeralM k))) := by
  have hw := (testigoIter cl s p hp k).2
  have hin : Prf (In (nthc (chainT n s) (numeralM k))
      (carc (testigoIter cl s p hp k).1)) :=
    prf_congr_In_left (prf_eq_symm (prf_nthc_chainT n k hk s)) (prf_and_elim_right hw)
  exact prf_and_intro (prf_and_elim_left hw) hin

/-! ### §3.1 · La EQUIVALENCIA, a nivel de DATOS

    Los dos tipos de abajo son inter‑construibles. `Via3UnPiso` es lo MÍNIMO que la vía 3
    necesita (un testigo para la casilla 1 de la cadena de un solo piso); `PasoClausura` es
    exactamente la clausura que la vía 3 quería evitar. -/

/-- Lo mínimo que la vía 3 exige: testigo para la casilla 1 de la cadena `[s, liftc 0 s]`. -/
def Via3UnPiso : Type :=
  ∀ (s p : Term), Prf (isTCB p s) →
    { p' : Term // Prf (isTCB p' (nthc (chainT 1 s) (numeralM 1))) }

/-- **(⇐)** Con la clausura, la vía 3 sale entera y gratis (todos los pisos, todo `n`). -/
def via3_de_clausura (cl : PasoClausura) :
    ∀ (n : Nat) (s p : Term) (hp : Prf (isTCB p s)) (k : Nat), Nat.le k n →
      { p' : Term // Prf (isTCB p' (nthc (chainT n s) (numeralM k))) } :=
  fun n s p hp k hk => ⟨(testigoIter cl s p hp k).1, clausura_da_acotar cl n s p hp k hk⟩

/-- **(⇒)** Y con UN SOLO PISO de la vía 3 se recupera la clausura entera. -/
def clausura_de_via3 (v3 : Via3UnPiso) : PasoClausura :=
  fun x p h => ⟨(v3 x p h).1,
    acotar_da_clausura_chainT 1 x (v3 x p h).1 (Nat.le_refl 1) (v3 x p h).2⟩

/-! ## §4 · Por qué la cota NO puede ser META

    §2 construye la cadena por recursión en un `Nat` de **Lean**. En el uso real la cota es la
    profundidad de binders del código de fórmula `f`, y `f` es ABSTRACTO (es lo que distingue a
    los 7 reflectores: `substfc`/`liftfc` sobre argumento abstracto). Abajo, el enunciado OBJETO
    de la premisa que la vía 3 tendría que descargar, escrito con símbolos EXISTENTES —
    o sea: el problema NO es expresarlo, es PROBARLO, y su inducción en la cota tiene por paso
    sucesor exactamente `PasoClausura`. -/

/-- El testigo de cada piso, como conjunto acotado sobre una lista de testigos `P`. -/
def chainWitnessed (P L b : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 b))
    (In (nthc (liftTerm 0 L) (.var 0)) (carc (nthc (liftTerm 0 P) (.var 0)))))

/-- La premisa ENTERA de la vía 3, expresable: cadena + testigos + cota suficiente.
    (`d` = profundidad de binders de `f`; en la práctica basta la cota burda `d ≤ f`.) -/
def acotarPremisa (P L b : Term) : Formula :=
  land (liftChainOk L b) (chainWitnessed P L b)

/-- CENSO: `acotarPremisa` sólo usa símbolos de `Minimal.Axioms`. El `rfl` lo exhibe. -/
theorem acotarPremisa_shape (P L b : Term) :
    acotarPremisa P L b
      = land
          (Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 b))
            (Formula.eq (nthc (liftTerm 0 L) (succ (.var 0)))
                        (liftc zero (nthc (liftTerm 0 L) (.var 0))))))
          (Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 b))
            (In (nthc (liftTerm 0 L) (.var 0)) (carc (nthc (liftTerm 0 P) (.var 0)))))) := rfl

/-! ## §5 · CENSO DE SÍMBOLOS — ninguno nuevo

    Cada `rfl` exhibe que la construcción de este fichero se despliega en símbolos de
    `Minimal/Axioms.lean` (`liftc`, `cons`, `nil`, `nthc`, `lenc`, `lt`, `carc`, `In`). -/

theorem censo_iterLiftc (s : Term) :
    iterLiftc 3 s = liftc zero (liftc zero (liftc zero s)) := rfl

theorem censo_chainT (s : Term) :
    chainT 2 s = cons s (cons (liftc zero s) (cons (liftc zero (liftc zero s)) nil)) := rfl

theorem censo_liftc_es_el_de_produccion (c t : Term) :
    liftc c t = Term.func "liftc" [c, t] := rfl

/-! ## §6 · DÓNDE SÍ hace falta un símbolo nuevo (censo del vocabulario)

    Censo de los símbolos de función CON NOMBRE de `Minimal/Axioms.lean`
    (`grep -o 'Term.func "…"'`, 15 en total):

        axiomsCodeT carc cdrc lenc liftc liftfc liftsc nthc premsOf runFn
        substfc substtc substtsc tcFn validProofFn

    Los ÚNICOS `map` que hay son `liftsc` (= map de `liftc`, `ax_liftsc_nil/cons`) y
    `substtsc` (= map de `substtc`, `ax_substtsc_nil/cons`). Ambos mapean una operación de
    código de **TÉRMINO** sobre una lista de códigos de término.

    El testigo es `p = cons wT wTs` con `wT` = lista de códigos de TÉRMINO y `wTs` = lista de
    códigos de LISTA DE TÉRMINOS. `PasoClausura` (§3) pide construir la imagen de `p`:

    * mitad `wT` ↦ `liftsc zero wT` — **existe**, es literalmente el map;
    * mitad `wTs` ↦ `map (liftsc zero) wTs` — **NO existe**: sería un map DE `liftsc`, un
      nivel por encima, y no está en el censo. (`liftsc zero wTs` calcularía
      `map (liftc zero) wTs`, que aplica la operación EQUIVOCADA a cada elemento.)

    ⇒ El símbolo nuevo, si hace falta, hace falta en la **CLAUSURA**, no en la ITERACIÓN.
    La vía 3 no lo evita porque §3 demuestra que la vía 3 **es** la clausura. -/

end LiftAcotar

#print axioms LiftAcotar.iter_ne_liftc_syn
#print axioms LiftAcotar.iter_ne_liftc_sem
#print axioms LiftAcotar.prf_nthc_chainT
#print axioms LiftAcotar.prf_liftChainOk_chainT
#print axioms LiftAcotar.acotar_da_clausura
#print axioms LiftAcotar.acotar_da_clausura_chainT
#print axioms LiftAcotar.clausura_da_acotar_chain
#print axioms LiftAcotar.clausura_da_acotar
#print axioms LiftAcotar.via3_de_clausura
#print axioms LiftAcotar.clausura_de_via3
#print axioms LiftAcotar.acotarPremisa_shape
#print axioms LiftAcotar.censo_chainT
