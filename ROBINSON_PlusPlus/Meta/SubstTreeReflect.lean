import ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf
import ROBINSON_PlusPlus.Meta.EvalSubstfcPrf
import ROBINSON_PlusPlus.Meta.CodeTreeReflect
-- ⚠️ Añadido con el nodo `lift` (2026‑09‑09e): lo paga `pcc_eval_liftfc_wit`. Sin ciclo
--    (`EvalLiftfcPrf` no depende de este módulo) y el cierre crece en UN módulo.
import ROBINSON_PlusPlus.Meta.EvalLiftfcPrf
/-!
# `Meta/SubstTreeReflect.lean` — C3: el árbol de código **con nodos `substfc`**

Con ADR‑020 saldado (§3.46), lo que queda de C3 son los **7 reflectores de sustitución**. Su
condición estructural tiene exactamente la misma forma que la de los 14 tags ya cerrados
—`carc #0 = E(nthc #0 i…)`— **salvo que `E` lleva nodos `substfc` y `liftfc`**, que
`Meta/CodeTreeReflect.lean` no conoce.

## Por qué un tipo NUEVO y no extender `CTree`

⛔ **Orden de imports.** El paso caro de un nodo `substfc` es `pcc_eval_substfc`
(`Meta/EvalSubstfcPrf.lean`, B3.4), y `CodeTreeReflect` está **aguas ARRIBA** de ese módulo:
extender `CTree` allí con un constructor `sub` haría imposible probar su caso. Es el mismo
ciclo de imports que ya obligó a bajar lemas en B2. Así que el árbol con `sub` vive **aguas
abajo**, aquí, y `CTree` se queda como está.

## El reparto de los 7, medido

| tags | `liftfc` | `substfc` | `termCodeM` | alcanzable |
|---|---|---|---|---|
| **q1** (9), **q2** (10), **leibniz** (13) | 0 | 1 / 1 / 2 | 0 | ✅ **con lo que B3.4 ya compró** |
| q3 (11), qconf (19) | 1 | 0 | 0 | ⛔ `pcc_eval_liftfc` |
| ind (18) | 1 | 2 | 2 | ⛔ `pcc_eval_liftfc` |
| listInd (20) | 3 | 2 | 2 | ⛔ `pcc_eval_liftfc` |

⇒ `pcc_eval_liftfc` bloquea **4 de los 7**; **tres son alcanzables hoy**. Por eso `STree` trae
de momento **sólo** el nodo `sub`: añadir `lift` sin su evaluación provable sería un
constructor que ningún caso puede cerrar.

## ⭐ Y por qué `hCarc` es de verdad una MP

`pcc_eval_substfc_wit (v s f) : Prf (hasWit s ∧ hasWitF f ⇒ targetSubstfc v s f)` es una
implicación **OBJETO** cuyo antecedente **son** las guardas de ADR‑020. Con `t` abstracto,
`hasWit (nthc t 3)` no es demostrable —eso es lo que hace útil a la guarda—, así que el núcleo
sólo puede pagarla teniéndola **en su contexto**. Para eso están los absorbedores
`hcond_absorbe_1/2/3` de `Meta/LineWFGuardPrf.lean`, que dan al núcleo la fórmula guardada
**entera**: es la propiedad que ADR‑020 compró y aquí se cobra.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.CodeTreeReflect
open ROBINSON_PlusPlus.Meta.LineWFSchemaPrf ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
open ROBINSON_PlusPlus.Meta.LineWFGuardPrf ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.SubstTreeReflect

/-! ## §1 · EL ÁRBOL, CON NODO `sub` -/

/-- Árbol de código con hojas‑accesor **y nodos de sustitución**. Espeja `CTree` añadiendo
    `sub s f` = `substfc 0 s f`, que es lo que los 7 esquemas de sustitución traen y `CTree` no
    puede tener (ver la cabecera: ciclo de imports). -/
inductive STree where
  | leaf : Nat → STree
  | nul  : Nat → STree
  | un   : Nat → STree → STree
  | bin  : Nat → STree → STree → STree
  | sub  : STree → STree → STree
  | lift : Nat → STree → STree
  deriving Repr

namespace STree

/-- La expresión OBJETO del árbol sobre una línea `t`. -/
def objAt (t : Term) : STree → Term
  | leaf i    => nthc t (numeralM i)
  | nul m     => cons (numeralM m) nil
  | un m a    => cons (numeralM m) (cons (a.objAt t) nil)
  | bin m a b => cons (numeralM m) (cons (a.objAt t) (cons (b.objAt t) nil))
  | sub s f   => substfc zero (s.objAt t) (f.objAt t)
  | lift n a  => liftfc (numeralM n) (a.objAt t)

/-- El código ESTÁTICO, con el hueco `⌜v₀⌝` en las hojas. -/
def code : STree → Term
  | leaf i    => nthcT (varc (numeral 0)) (termCode (numeralM i))
  | nul m     => nulT m
  | un m a    => unT m a.code
  | bin m a b => binT m a.code b.code
  | sub s f   => substfcT (termCode zero) s.code f.code
  | lift n a  => liftfcT (termCode (numeralM n)) a.code

/-- Forma **N** (accesores rastreados). -/
def dotN (t : Term) : STree → Term
  | leaf i    => nthcT (tcFn t) (termCode (numeralM i))
  | nul m     => nulT m
  | un m a    => unT m (a.dotN t)
  | bin m a b => binT m (a.dotN t) (b.dotN t)
  | sub s f   => substfcT (termCode zero) (s.dotN t) (f.dotN t)
  | lift n a  => liftfcT (termCode (numeralM n)) (a.dotN t)

/-- Forma **V** (valores punteados). ⚠️ En el nodo `sub` **no** se puntea el `substfc` entero:
    se deja `substfcT` sobre los `dotV` de los hijos, y el salto de
    `(substfc 0 S F)˙` a `substfcT 0̄ Ṡ Ḟ` se paga UNA vez, en `pcc_tc_objAt`, con
    `pcc_eval_substfc_wit` — que es donde entran las guardas de ADR‑020. -/
def dotV (t : Term) : STree → Term
  | leaf i    => tcFn (nthc t (numeralM i))
  | nul m     => nulT m
  | un m a    => unT m (a.dotV t)
  | bin m a b => binT m (a.dotV t) (b.dotV t)
  | sub s f   => substfcT (termCode zero) (s.dotV t) (f.dotV t)
  | lift n a  => liftfcT (termCode (numeralM n)) (a.dotV t)

/-- Cota estricta de los índices de hoja. -/
def maxLeaf : STree → Nat
  | leaf i    => i + 1
  | nul _     => 0
  | un _ a    => a.maxLeaf
  | bin _ a b => Nat.max a.maxLeaf b.maxLeaf
  | sub s f   => Nat.max s.maxLeaf f.maxLeaf
  | lift _ a  => a.maxLeaf

end STree

open STree

/-! ## §2 · LAS IGUALDADES ESTRUCTURALES (inducción pura sobre el árbol) -/

/-- La expresión objeto sobre `#0` es invariante al instanciar el `∀` en `#0`. -/
theorem substTerm_objAt :
    ∀ (T : STree) (t : Term), substTerm 0 t (T.objAt (.var 0)) = T.objAt t
  | .leaf i, t => by
      simp only [objAt, nthc, substTerm, substTerms, substTerm_numeralM, if_true]
  | .nul m, t => by
      simp only [objAt, cons, nil, zero, substTerm, substTerms, substTerm_numeralM]
  | .un m a, t => by
      simp only [objAt, cons, nil, zero, substTerm, substTerms, substTerm_numeralM,
        substTerm_objAt a t]
  | .bin m a b, t => by
      simp only [objAt, cons, nil, zero, substTerm, substTerms, substTerm_numeralM,
        substTerm_objAt a t, substTerm_objAt b t]
  | .sub s f, t => by
      simp only [objAt, substfc, zero, substTerm, substTerms,
        substTerm_objAt s t, substTerm_objAt f t]
  | .lift n a, t => by
      simp only [objAt, liftfc, substTerm, substTerms, substTerm_numeralM,
        substTerm_objAt a t]

theorem substTerm_objAt_var0 (T : STree) :
    substTerm 0 (.var 0) (T.objAt (.var 0)) = T.objAt (.var 0) := substTerm_objAt T (.var 0)

/-- El código estático **es** el `termCode` de la expresión objeto sobre `#0`. -/
theorem code_eq_termCode : ∀ T : STree, T.code = termCode (T.objAt (.var 0))
  | .leaf _ => rfl
  | .nul _ => rfl
  | .un m a => by
      simp only [STree.code, objAt, code_eq_termCode a, unT_termCode]
  | .bin m a b => by
      simp only [STree.code, objAt, code_eq_termCode a, code_eq_termCode b, binT_termCode]
  | .sub s f => by
      simp only [STree.code, objAt, code_eq_termCode s, code_eq_termCode f, substfcT_termCode]
  | .lift n a => by
      simp only [STree.code, objAt, code_eq_termCode a, liftfcT_termCode]

/-- **Evaluación del código punteado**: rellenar el hueco con `ṫ` da la forma rastreada. -/
theorem prf_substtc_code (t : Term) :
    ∀ T : STree, Prf (substtc zero (tcFn t) T.code =eq T.dotN t)
  | .leaf i => by
      refine prf_eq_trans (prf_substtc_nthcT zero (tcFn t) _ _) ?_
      exact prf_congr_nthcT (prf_substtc_varc0 (tcFn t))
        (substtc_inv_termCode_numeralM i (tcFn t))
  | .nul m => prf_substtc_nulT m (tcFn t)
  | .un m a =>
      prf_eq_trans (prf_substtc_unT m (tcFn t) a.code) (prf_congr_unT (prf_substtc_code t a))
  | .bin m a b =>
      prf_eq_trans (prf_substtc_binT m (tcFn t) a.code b.code)
        (prf_congr_binT (prf_substtc_code t a) (prf_substtc_code t b))
  | .sub s f =>
      prf_eq_trans (prf_substtc_substfcT zero (tcFn t) _ s.code f.code)
        (prf_congr_substfcT (prf_substtc_termCode_zero 0 (tcFn t))
          (prf_substtc_code t s) (prf_substtc_code t f))
  | .lift n a =>
      prf_eq_trans (prf_substtc_liftfcT zero (tcFn t) _ a.code)
        (prf_congr_liftfcT (substtc_inv_termCode_numeralM n (tcFn t))
          (prf_substtc_code t a))

/-- `dotN` es `substtc`‑invariante. -/
theorem substtc_inv_dotN (t : Term) :
    ∀ (T : STree) (W : Term), Prf (substtc zero W (T.dotN t) =eq T.dotN t)
  | .leaf i, W => substtc_inv_nthcT_tcFn t i W
  | .nul m, W => prf_substtc_nulT m W
  | .un m a, W =>
      prf_eq_trans (prf_substtc_unT m W (a.dotN t)) (prf_congr_unT (substtc_inv_dotN t a W))
  | .bin m a b, W =>
      prf_eq_trans (prf_substtc_binT m W (a.dotN t) (b.dotN t))
        (prf_congr_binT (substtc_inv_dotN t a W) (substtc_inv_dotN t b W))
  | .sub s f, W =>
      prf_eq_trans (prf_substtc_substfcT zero W _ (s.dotN t) (f.dotN t))
        (prf_congr_substfcT (prf_substtc_termCode_zero 0 W)
          (substtc_inv_dotN t s W) (substtc_inv_dotN t f W))
  | .lift n a, W =>
      prf_eq_trans (prf_substtc_liftfcT zero W _ (a.dotN t))
        (prf_congr_liftfcT (substtc_inv_termCode_numeralM n W) (substtc_inv_dotN t a W))

/-- `dotV` es `substtc`‑invariante. -/
theorem substtc_inv_dotV (t : Term) :
    ∀ (T : STree) (W : Term), Prf (substtc zero W (T.dotV t) =eq T.dotV t)
  | .leaf _, W => substtc_inv_tcFn _ W
  | .nul m, W => prf_substtc_nulT m W
  | .un m a, W =>
      prf_eq_trans (prf_substtc_unT m W (a.dotV t)) (prf_congr_unT (substtc_inv_dotV t a W))
  | .bin m a b, W =>
      prf_eq_trans (prf_substtc_binT m W (a.dotV t) (b.dotV t))
        (prf_congr_binT (substtc_inv_dotV t a W) (substtc_inv_dotV t b W))
  | .sub s f, W =>
      prf_eq_trans (prf_substtc_substfcT zero W _ (s.dotV t) (f.dotV t))
        (prf_congr_substfcT (prf_substtc_termCode_zero 0 W)
          (substtc_inv_dotV t s W) (substtc_inv_dotV t f W))
  | .lift n a, W =>
      prf_eq_trans (prf_substtc_liftfcT zero W _ (a.dotV t))
        (prf_congr_liftfcT (substtc_inv_termCode_numeralM n W) (substtc_inv_dotV t a W))

/-! ### La GUARDA de las dos formas (ADR-020), por la misma inducción -/

theorem prf_hasWit_dotV (t : Term) : ∀ T : STree, Prf (hasWit (T.dotV t))
  | .leaf i    => prf_hasWit_tcFn (nthc t (numeralM i))
  | .nul m     => prf_hasWit_nulT m
  | .un m a    => prf_hasWit_unT m (prf_hasWit_dotV t a)
  | .bin m a b => prf_hasWit_binT m (prf_hasWit_dotV t a) (prf_hasWit_dotV t b)
  | .sub s f   => prf_hasWit_funcc3 _ _ _ _ (prf_hasWit_tc zero)
      (prf_hasWit_dotV t s) (prf_hasWit_dotV t f)
  | .lift n a  => prf_hasWit_liftfcT (prf_hasWit_tc (numeralM n)) (prf_hasWit_dotV t a)

theorem prf_hasWit_dotN (t : Term) : ∀ T : STree, Prf (hasWit (T.dotN t))
  | .leaf i    => prf_hasWit_nthcT (prf_hasWit_tcFn t) (prf_hasWit_tc (numeralM i))
  | .nul m     => prf_hasWit_nulT m
  | .un m a    => prf_hasWit_unT m (prf_hasWit_dotN t a)
  | .bin m a b => prf_hasWit_binT m (prf_hasWit_dotN t a) (prf_hasWit_dotN t b)
  | .sub s f   => prf_hasWit_funcc3 _ _ _ _ (prf_hasWit_tc zero)
      (prf_hasWit_dotN t s) (prf_hasWit_dotN t f)
  | .lift n a  => prf_hasWit_liftfcT (prf_hasWit_tc (numeralM n)) (prf_hasWit_dotN t a)

/-! ## §3 · LA CONDICIÓN‑ÁRBOL Y SU `condD`, COMPUTADO -/

/-- La condición estructural asociada a un árbol con sustituciones. -/
def condOfS (T : STree) : Formula := carc (.var 0) =eq T.objAt (.var 0)

theorem substFormula_condOfS (T : STree) :
    substFormula 0 (.var 0) (condOfS T) = condOfS T := by
  simp only [condOfS, carc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm,
    if_true, substTerm_objAt_var0 T]

theorem substFormula_condOfS_at (T : STree) (t : Term) :
    substFormula 0 t (condOfS T) = (carc t =eq T.objAt t) := by
  simp only [condOfS, carc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm,
    if_true, substTerm_objAt T t]

/-- ⭐ **`condD` de una condición‑árbol CON sustituciones, evaluado.** Idéntico a
    `prf_condD_of_tree_eq` (`Meta/CodeTreeReflect.lean`), y por la misma razón: el `substfc`
    OBJETO del `condD` se distribuye por el árbol hasta las hojas. -/
theorem prf_condD_of_stree_eq (T : STree) (t : Term) :
    Prf (condD (condOfS T) t =eq eqCodeFn (carcT (tcFn t)) (T.dotN t)) := by
  unfold condD condOfS
  refine prf_eq_trans (prf_substfc_eq zero (tcFn t) _ _) ?_
  refine prf_congr_eqCodeFn ?_ (code_eq_termCode T ▸ prf_substtc_code t T)
  exact prf_eq_trans (prf_substtc_carcT zero (tcFn t) _)
    (prf_congr_carcT (prf_substtc_varc0 (tcFn t)))

/-! ## §4 · LOS TRES ÁRBOLES ALCANZABLES HOY, DECLARADOS Y COMPROBADOS

Regla de método de §3.44: la abstracción se casa con el original por `rfl`. Si
`Minimal/Axioms.lean` cambiara uno de estos tres esquemas, el `rfl` deja de compilar. -/

/-- **q1** (tag 9): `concl = (∀A) ⇒ A[t]`, con `A = nthc #0 2` y `t = nthc #0 3`. -/
def treeQ1 : STree := .bin 5 (.un 6 (.leaf 2)) (.sub (.leaf 3) (.leaf 2))

/-- **q2** (tag 10): `concl = A[t] ⇒ ∃A`. -/
def treeQ2 : STree := .bin 5 (.sub (.leaf 3) (.leaf 2)) (.un 9 (.leaf 2))

/-- **leibniz** (tag 13): `concl = (t₁ ≐ t₂) ⇒ (A[t₁] ⇒ A[t₂])`. -/
def treeLeibniz : STree :=
  .bin 5 (.bin 4 (.leaf 3) (.leaf 4))
    (.bin 5 (.sub (.leaf 3) (.leaf 2)) (.sub (.leaf 4) (.leaf 2)))

example : condOfS treeQ1
    = (carc (.var 0) =eq implc (forallc (nthc (.var 0) (numeralM 2)))
        (substfc zero (nthc (.var 0) (numeralM 3)) (nthc (.var 0) (numeralM 2)))) := rfl

example : condOfS treeQ2
    = (carc (.var 0) =eq implc
        (substfc zero (nthc (.var 0) (numeralM 3)) (nthc (.var 0) (numeralM 2)))
        (exc (nthc (.var 0) (numeralM 2)))) := rfl

example : condOfS treeLeibniz
    = (carc (.var 0) =eq implc
        (eqc (nthc (.var 0) (numeralM 3)) (nthc (.var 0) (numeralM 4)))
        (implc (substfc zero (nthc (.var 0) (numeralM 3)) (nthc (.var 0) (numeralM 2)))
               (substfc zero (nthc (.var 0) (numeralM 4)) (nthc (.var 0) (numeralM 2))))) := rfl

/-- ⭐ **Y los tres esquemas ENTEROS, casados con su árbol y su cascada de guardas.** Esto es
    lo que conecta `Minimal/Axioms.lean` con el chasis: el `∃ C` de §2.1 de
    `Meta/LineWFGuardPrf.lean` queda aquí **resuelto**. -/
example : ax_lineWF_q1 =
    forall_ (Formula.impl (tagF 9) (lwfVar ⇔ Formula.and (lencF 4)
      (guardedCond [.witF 2, .wit 3] (condOfS treeQ1)))) := rfl

example : ax_lineWF_q2 =
    forall_ (Formula.impl (tagF 10) (lwfVar ⇔ Formula.and (lencF 4)
      (guardedCond [.witF 2, .wit 3] (condOfS treeQ2)))) := rfl

example : ax_lineWF_leibniz =
    forall_ (Formula.impl (tagF 13) (lwfVar ⇔ Formula.and (lencF 5)
      (guardedCond [.witF 2, .wit 3, .wit 4] (condOfS treeLeibniz)))) := rfl

example : treeQ1.maxLeaf = 4 := rfl
example : treeQ2.maxLeaf = 4 := rfl
example : treeLeibniz.maxLeaf = 5 := rfl

/-! ### Y los DOS que el nodo `lift` acaba de hacer alcanzables (2026‑09‑09e)

⭐ Los dos llevan **un solo `liftfc`, a nivel `zero`, y sobre una hoja** — y la guarda de su
cascada cae **exactamente** sobre esa hoja. Es el mismo hecho estructural que §3.48 registró
para el nodo `sub`: ADR‑020 no eligió dónde poner las guardas, las puso donde el evaluador las
iba a pedir. -/

/-- **q3** (tag 11): `concl = (∀(A ⇒ ↑B)) ⇒ ((∃A) ⇒ B)`, con `A = nthc #0 2`, `B = nthc #0 3`. -/
def treeQ3 : STree :=
  .bin 5 (.un 6 (.bin 5 (.leaf 2) (.lift 0 (.leaf 3))))
    (.bin 5 (.un 9 (.leaf 2)) (.leaf 3))

/-- **qconf** (tag 19): `concl = (∀(↑P ⇒ C)) ⇒ (P ⇒ ∀C)`, con `P = nthc #0 2`, `C = nthc #0 3`. -/
def treeQconf : STree :=
  .bin 5 (.un 6 (.bin 5 (.lift 0 (.leaf 2)) (.leaf 3)))
    (.bin 5 (.leaf 2) (.un 6 (.leaf 3)))

example : ax_lineWF_q3 =
    forall_ (Formula.impl (tagF 11) (lwfVar ⇔ Formula.and (lencF 4)
      (guardedCond [.witF 3] (condOfS treeQ3)))) := rfl

example : ax_lineWF_qconf =
    forall_ (Formula.impl (tagF 19) (lwfVar ⇔ Formula.and (lencF 4)
      (guardedCond [.witF 2] (condOfS treeQconf)))) := rfl

example : treeQ3.maxLeaf = 4 := rfl
example : treeQconf.maxLeaf = 4 := rfl


/-! ## §5 · LAS DOS MITADES DENTRO DE `Prov`

⚠️ **Corrección a lo que dejé escrito en `NEXT-STEPS.md`**: allí puse que el caso `sub` de
`PrfH_dotVN` lo paga `pcc_eval_substfc_wit`. **No es así.** Las dos mitades se reparten:

| pieza | qué prueba | quién paga el nodo `sub` |
|---|---|---|
| `PrfH_tc_objAt` | `(E(t))˙ = dotV` | ⭐ **`pcc_eval_substfc_wit`** — y por eso pide las guardas |
| `PrfH_dotVN` | `dotV = dotN` | pura **congruencia** (`pcc_congr_substfcT_arg2/3_code`) + las hojas |

Es el mismo reparto que en `Meta/CodeTreeReflect.lean`: el salto de valor a accesor vive en
`dotVN`, y el «código del código» en `tc_objAt`. Lo que cambia es **dónde** entra la guarda de
ADR‑020: sólo en `tc_objAt`, y sólo en los nodos `sub`. -/

/-- Las guardas que los nodos `sub` necesitan, y **sólo** ellos: el resto del árbol no pide
    nada. Con `t` abstracto `hasWit (nthc t 3)` no es demostrable —es lo que hace útil a la
    guarda—, así que llegan como hipótesis del contexto, que es donde ADR‑020 las puso. -/
def SGuards (Γ : List Formula) (t : Term) : STree → Prop
  | .leaf _    => True
  | .nul _     => True
  | .un _ a    => SGuards Γ t a
  | .bin _ a b => SGuards Γ t a ∧ SGuards Γ t b
  | .sub s f   => (PrfH Γ (hasWit (s.objAt t)) ∧ PrfH Γ (hasWitF (f.objAt t)))
                    ∧ SGuards Γ t s ∧ SGuards Γ t f
  | .lift _ a  => PrfH Γ (hasWitF (a.objAt t)) ∧ SGuards Γ t a

/-- ⭐ **EL «CÓDIGO DEL CÓDIGO» DEL ÁRBOL, con nodos de sustitución.** El caso `sub` es el
    único con contenido: lo paga `pcc_eval_substfc_wit`, cuyo antecedente OBJETO **son** las
    guardas de ADR‑020 — que `SGuards` exige exactamente ahí. -/
theorem PrfH_tc_objAt {Γ : List Formula} (t : Term) :
    ∀ T : STree, SGuards Γ t T →
      PrfH Γ (provFromCode (eqc (tcFn (T.objAt t)) (T.dotV t)))
  | .leaf _, _ => prf_to_prfH (prf_provFromCode_eqCodeFn_refl _) _
  | .nul m, _ => prf_to_prfH (pcc_dot_nul_symm m) _
  | .un m a, hg =>
      PrfH_eq_trans_code _ _ _ (substtc_inv_tcFn _)
        (prf_to_prfH (pcc_dot_un_symm m (a.objAt t)) _)
        (PrfH.mp _ _ _
          (prf_to_prfH (pcc_congr_unT_code m (tcFn (a.objAt t)) (a.dotV t)
            (substtc_inv_tcFn _) (prf_hasWit_tcFn (a.objAt t)) (prf_hasWit_dotV t a)) _)
          (PrfH_tc_objAt t a hg))
        (prf_hasWit_tcFn _)
        (prf_hasWit_unT m (prf_hasWit_tcFn (a.objAt t)))
        (prf_hasWit_unT m (prf_hasWit_dotV t a))
  | .bin m a b, hg =>
      PrfH_eq_trans_code _ _ _ (substtc_inv_tcFn _)
        (prf_to_prfH (pcc_dot_bin_symm m (a.objAt t) (b.objAt t)) _)
        (PrfH_eq_trans_code _ _ _
          (substtc_inv_binT (substtc_inv_tcFn _) (substtc_inv_tcFn _))
          (PrfH.mp _ _ _
            (prf_to_prfH (pcc_congr_binT_1_code m (tcFn (b.objAt t)) (tcFn (a.objAt t))
              (a.dotV t) (substtc_inv_tcFn _) (substtc_inv_tcFn _)
              (prf_hasWit_tcFn (b.objAt t)) (prf_hasWit_tcFn (a.objAt t))
              (prf_hasWit_dotV t a)) _)
            (PrfH_tc_objAt t a hg.1))
          (PrfH.mp _ _ _
            (prf_to_prfH (pcc_congr_binT_2_code m (a.dotV t) (tcFn (b.objAt t)) (b.dotV t)
              (substtc_inv_dotV t a) (substtc_inv_tcFn _)
              (prf_hasWit_dotV t a) (prf_hasWit_tcFn (b.objAt t))
              (prf_hasWit_dotV t b)) _)
            (PrfH_tc_objAt t b hg.2))
          (prf_hasWit_binT m (prf_hasWit_tcFn (a.objAt t)) (prf_hasWit_tcFn (b.objAt t)))
          (prf_hasWit_binT m (prf_hasWit_dotV t a) (prf_hasWit_tcFn (b.objAt t)))
          (prf_hasWit_binT m (prf_hasWit_dotV t a) (prf_hasWit_dotV t b)))
        (prf_hasWit_tcFn _)
        (prf_hasWit_binT m (prf_hasWit_tcFn (a.objAt t)) (prf_hasWit_tcFn (b.objAt t)))
        (prf_hasWit_binT m (prf_hasWit_dotV t a) (prf_hasWit_dotV t b))
  | .sub s f, hg => by
      -- ⭐ EL CASO CON CONTENIDO. `pcc_eval_substfc_wit` con las guardas del contexto.
      have hev : PrfH Γ (provFromCode (eqc
          (substfcT (tcFn zero) (tcFn (s.objAt t)) (tcFn (f.objAt t)))
          (tcFn (substfc zero (s.objAt t) (f.objAt t))))) :=
        PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_substfc_wit zero (s.objAt t) (f.objAt t)) _)
          (PrfH_and_intro hg.1.1 hg.1.2)
      -- el nivel: `tcFn zero` es el `termCode zero` del árbol (congruencia META)
      have hev0 : PrfH Γ (provFromCode (eqc
          (substfcT (termCode zero) (tcFn (s.objAt t)) (tcFn (f.objAt t)))
          (tcFn (substfc zero (s.objAt t) (f.objAt t))))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
          (prf_congr_eqCodeFn
            (prf_congr_substfcT prf_tc_zero (prf_refl _) (prf_refl _)) (prf_refl _))) _) hev
      have hsym : PrfH Γ (provFromCode (eqc
          (tcFn (substfc zero (s.objAt t) (f.objAt t)))
          (substfcT (termCode zero) (tcFn (s.objAt t)) (tcFn (f.objAt t))))) :=
        PrfH_eq_symm_code _ _
          (substtc_inv_substfcT (prf_substtc_termCode_zero 0)
            (substtc_inv_tcFn _) (substtc_inv_tcFn _))
          hev0
          (prf_hasWit_funcc3 _ _ _ _ (prf_hasWit_tc zero)
            (prf_hasWit_tcFn _) (prf_hasWit_tcFn _))
          (prf_hasWit_tcFn _)
      -- y ahora los dos hijos, por congruencia dentro de `Prov`
      have h2 : PrfH Γ (provFromCode (eqc
          (substfcT (termCode zero) (tcFn (s.objAt t)) (tcFn (f.objAt t)))
          (substfcT (termCode zero) (s.dotV t) (tcFn (f.objAt t))))) :=
        PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_substfcT_arg2_code (termCode zero)
          (tcFn (f.objAt t)) (tcFn (s.objAt t)) (s.dotV t)
          (prf_substtc_termCode_zero 0) (substtc_inv_tcFn _) (substtc_inv_tcFn _)
          (prf_hasWit_tc zero) (prf_hasWit_tcFn _) (prf_hasWit_tcFn _)
          (prf_hasWit_dotV t s)) _) (PrfH_tc_objAt t s hg.2.1)
      have h3 : PrfH Γ (provFromCode (eqc
          (substfcT (termCode zero) (s.dotV t) (tcFn (f.objAt t)))
          (substfcT (termCode zero) (s.dotV t) (f.dotV t)))) :=
        PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_substfcT_arg3_code (termCode zero)
          (s.dotV t) (tcFn (f.objAt t)) (f.dotV t)
          (prf_substtc_termCode_zero 0) (substtc_inv_dotV t s) (substtc_inv_tcFn _)
          (prf_hasWit_tc zero) (prf_hasWit_dotV t s) (prf_hasWit_tcFn _)
          (prf_hasWit_dotV t f)) _) (PrfH_tc_objAt t f hg.2.2)
      have h23 : PrfH Γ (provFromCode (eqc
          (substfcT (termCode zero) (tcFn (s.objAt t)) (tcFn (f.objAt t)))
          (substfcT (termCode zero) (s.dotV t) (f.dotV t)))) :=
        PrfH_eq_trans_code _ _ _
          (substtc_inv_substfcT (prf_substtc_termCode_zero 0)
            (substtc_inv_tcFn _) (substtc_inv_tcFn _))
          h2 h3
          (prf_hasWit_funcc3 _ _ _ _ (prf_hasWit_tc zero)
            (prf_hasWit_tcFn _) (prf_hasWit_tcFn _))
          (prf_hasWit_funcc3 _ _ _ _ (prf_hasWit_tc zero)
            (prf_hasWit_dotV t s) (prf_hasWit_tcFn _))
          (prf_hasWit_funcc3 _ _ _ _ (prf_hasWit_tc zero)
            (prf_hasWit_dotV t s) (prf_hasWit_dotV t f))
      exact PrfH_eq_trans_code _ _ _ (substtc_inv_tcFn _) hsym h23
        (prf_hasWit_tcFn _)
        (prf_hasWit_funcc3 _ _ _ _ (prf_hasWit_tc zero)
          (prf_hasWit_tcFn _) (prf_hasWit_tcFn _))
        (prf_hasWit_funcc3 _ _ _ _ (prf_hasWit_tc zero)
          (prf_hasWit_dotV t s) (prf_hasWit_dotV t f))
  | .lift n a, hg => by
      -- ⭐ EL SEGUNDO CASO CON CONTENIDO, y el que `pcc_eval_liftfc_wit` acaba de desbloquear.
      -- Es el análogo UNARIO del `sub`: un hijo, una guarda (`hasWitF`), una evaluación.
      have hev : PrfH Γ (provFromCode (eqc
          (liftfcT (tcFn (numeralM n)) (tcFn (a.objAt t)))
          (tcFn (liftfc (numeralM n) (a.objAt t))))) :=
        PrfH.mp _ _ _
          (prf_to_prfH (pcc_eval_liftfc_wit (numeralM n) (a.objAt t)) _) hg.1
      -- el nivel: `tcFn (numeralM n)` es el `termCode (numeralM n)` del árbol
      have hev0 : PrfH Γ (provFromCode (eqc
          (liftfcT (termCode (numeralM n)) (tcFn (a.objAt t)))
          (tcFn (liftfc (numeralM n) (a.objAt t))))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
          (prf_congr_eqCodeFn
            (prf_congr_liftfcT (prf_tc_numeralM n) (prf_refl _)) (prf_refl _))) _) hev
      have hsym : PrfH Γ (provFromCode (eqc
          (tcFn (liftfc (numeralM n) (a.objAt t)))
          (liftfcT (termCode (numeralM n)) (tcFn (a.objAt t))))) :=
        PrfH_eq_symm_code _ _
          (substtc_inv_liftfcT (substtc_inv_termCode_numeralM n) (substtc_inv_tcFn _))
          hev0
          (prf_hasWit_liftfcT (prf_hasWit_tc (numeralM n)) (prf_hasWit_tcFn _))
          (prf_hasWit_tcFn _)
      have h2 : PrfH Γ (provFromCode (eqc
          (liftfcT (termCode (numeralM n)) (tcFn (a.objAt t)))
          (liftfcT (termCode (numeralM n)) (a.dotV t)))) :=
        PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_liftfcT_arg2_code (termCode (numeralM n))
          (tcFn (a.objAt t)) (a.dotV t)
          (substtc_inv_termCode_numeralM n) (substtc_inv_tcFn _)
          (prf_hasWit_tc (numeralM n)) (prf_hasWit_tcFn _) (prf_hasWit_dotV t a)) _)
          (PrfH_tc_objAt t a hg.2)
      exact PrfH_eq_trans_code _ _ _ (substtc_inv_tcFn _) hsym h2
        (prf_hasWit_tcFn _)
        (prf_hasWit_liftfcT (prf_hasWit_tc (numeralM n)) (prf_hasWit_tcFn _))
        (prf_hasWit_liftfcT (prf_hasWit_tc (numeralM n)) (prf_hasWit_dotV t a))

/-- ⭐ **`Prov(⌜dotV = dotN⌝)`** para todo árbol cuyas hojas caigan bajo la longitud canónica.
    El nodo `sub` es **pura congruencia**: no pide guardas ni evaluación. -/
theorem PrfH_dotVN {Γ : List Formula} (t : Term) {n : Nat}
    (hlenc : PrfH Γ (lenc t =eq numeralM n)) (T : STree) :
    Nat.le T.maxLeaf n →
      PrfH Γ (provFromCode (eqc (T.dotV t) (T.dotN t))) := by
  induction T with
  | leaf i =>
      intro hb
      have hbound : PrfH Γ (lt (numeralM i) (lenc t)) :=
        PrfH_lt_of_lenc_eq (i := i) (n := n) hb hlenc
      have hev : PrfH Γ (provFromCode (eqc (nthcT (tcFn t) (termCode (numeralM i)))
          (tcFn (nthc t (numeralM i))))) :=
        PrfH.mp _ _ _ (prf_to_prfH (pcc_nthcD_bridge t i) _) hbound
      exact PrfH_eq_symm_code _ _ (substtc_inv_nthcT_tcFn t i) hev
        (prf_hasWit_nthcT (prf_hasWit_tcFn t) (prf_hasWit_tc (numeralM i)))
        (prf_hasWit_tcFn (nthc t (numeralM i)))
  | nul m => intro _; exact prf_to_prfH (prf_provFromCode_eqCodeFn_refl (nulT m)) _
  | un m a ih =>
      intro hb
      exact PrfH.mp _ _ _
        (prf_to_prfH (pcc_congr_unT_code m (a.dotV t) (a.dotN t)
          (substtc_inv_dotV t a) (prf_hasWit_dotV t a) (prf_hasWit_dotN t a)) _) (ih hb)
  | bin m a b iha ihb =>
      intro hb
      have hba : Nat.le a.maxLeaf n := Nat.le_trans (Nat.le_max_left _ _) hb
      have hbb : Nat.le b.maxLeaf n := Nat.le_trans (Nat.le_max_right _ _) hb
      have h1 : PrfH Γ (provFromCode (eqc (binT m (a.dotV t) (b.dotV t))
          (binT m (a.dotN t) (b.dotV t)))) :=
        PrfH.mp _ _ _
          (prf_to_prfH (pcc_congr_binT_1_code m (b.dotV t) (a.dotV t) (a.dotN t)
            (substtc_inv_dotV t b) (substtc_inv_dotV t a)
            (prf_hasWit_dotV t b) (prf_hasWit_dotV t a) (prf_hasWit_dotN t a)) _) (iha hba)
      have h2 : PrfH Γ (provFromCode (eqc (binT m (a.dotN t) (b.dotV t))
          (binT m (a.dotN t) (b.dotN t)))) :=
        PrfH.mp _ _ _
          (prf_to_prfH (pcc_congr_binT_2_code m (a.dotN t) (b.dotV t) (b.dotN t)
            (substtc_inv_dotN t a) (substtc_inv_dotV t b)
            (prf_hasWit_dotN t a) (prf_hasWit_dotV t b) (prf_hasWit_dotN t b)) _) (ihb hbb)
      exact PrfH_eq_trans_code _ _ _
        (substtc_inv_binT (substtc_inv_dotV t a) (substtc_inv_dotV t b)) h1 h2
        (prf_hasWit_binT m (prf_hasWit_dotV t a) (prf_hasWit_dotV t b))
        (prf_hasWit_binT m (prf_hasWit_dotN t a) (prf_hasWit_dotV t b))
        (prf_hasWit_binT m (prf_hasWit_dotN t a) (prf_hasWit_dotN t b))
  | sub s f ihs ihf =>
      intro hb
      have hbs : Nat.le s.maxLeaf n := Nat.le_trans (Nat.le_max_left _ _) hb
      have hbf : Nat.le f.maxLeaf n := Nat.le_trans (Nat.le_max_right _ _) hb
      have h1 : PrfH Γ (provFromCode (eqc
          (substfcT (termCode zero) (s.dotV t) (f.dotV t))
          (substfcT (termCode zero) (s.dotN t) (f.dotV t)))) :=
        PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_substfcT_arg2_code (termCode zero)
          (f.dotV t) (s.dotV t) (s.dotN t)
          (prf_substtc_termCode_zero 0) (substtc_inv_dotV t f) (substtc_inv_dotV t s)
          (prf_hasWit_tc zero) (prf_hasWit_dotV t f) (prf_hasWit_dotV t s)
          (prf_hasWit_dotN t s)) _) (ihs hbs)
      have h2 : PrfH Γ (provFromCode (eqc
          (substfcT (termCode zero) (s.dotN t) (f.dotV t))
          (substfcT (termCode zero) (s.dotN t) (f.dotN t)))) :=
        PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_substfcT_arg3_code (termCode zero)
          (s.dotN t) (f.dotV t) (f.dotN t)
          (prf_substtc_termCode_zero 0) (substtc_inv_dotN t s) (substtc_inv_dotV t f)
          (prf_hasWit_tc zero) (prf_hasWit_dotN t s) (prf_hasWit_dotV t f)
          (prf_hasWit_dotN t f)) _) (ihf hbf)
      exact PrfH_eq_trans_code _ _ _
        (substtc_inv_substfcT (prf_substtc_termCode_zero 0)
          (substtc_inv_dotV t s) (substtc_inv_dotV t f))
        h1 h2
        (prf_hasWit_funcc3 _ _ _ _ (prf_hasWit_tc zero)
          (prf_hasWit_dotV t s) (prf_hasWit_dotV t f))
        (prf_hasWit_funcc3 _ _ _ _ (prf_hasWit_tc zero)
          (prf_hasWit_dotN t s) (prf_hasWit_dotV t f))
        (prf_hasWit_funcc3 _ _ _ _ (prf_hasWit_tc zero)
          (prf_hasWit_dotN t s) (prf_hasWit_dotN t f))
  | lift n a ih =>
      -- pura congruencia, como el `un`: aquí no hay evaluación ni guarda
      intro hb
      exact PrfH.mp _ _ _
        (prf_to_prfH (pcc_congr_liftfcT_arg2_code (termCode (numeralM n))
          (a.dotV t) (a.dotN t)
          (substtc_inv_termCode_numeralM n) (substtc_inv_dotV t a)
          (prf_hasWit_tc (numeralM n)) (prf_hasWit_dotV t a) (prf_hasWit_dotN t a)) _) (ih hb)


/-! ## §6 · EL REFLECTOR DE UNA CONDICIÓN‑ÁRBOL CON SUSTITUCIONES

Mismo esqueleto que `pcc_condD_of_tree` (`Meta/CodeTreeReflect.lean`): puente `carc`, la
hipótesis reescribe el valor, `tc_objAt` lleva a `dotV` y `dotVN` a `dotN`. La única
diferencia es que ahora el núcleo recibe la fórmula guardada **entera** (`G`), porque de ella
salen **las dos** cosas que necesita: la ecuación estructural y las guardas de los nodos `sub`. -/

theorem pcc_condDS_of_stree (T : STree) (t : Term) {n : Nat} (hmax : Nat.le T.maxLeaf n)
    (G : Formula)
    (hstruct : Prf (substFormula 0 t G ⇒ (carc t =eq T.objAt t)))
    (hguards : SGuards [substFormula 0 t G, lenc t =eq numeralM n, lineWF t] t T) :
    HcondCore n t G (condOfS T) := by
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (substFormula 0 t G) [lenc t =eq numeralM n, lineWF t] rfl)
    (lenc t =eq numeralM n) [lineWF t] rfl)
  have hlw : PrfH [substFormula 0 t G, lenc t =eq numeralM n, lineWF t] (lineWF t) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hlenc : PrfH [substFormula 0 t G, lenc t =eq numeralM n, lineWF t]
      (lenc t =eq numeralM n) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hG : PrfH [substFormula 0 t G, lenc t =eq numeralM n, lineWF t]
      (substFormula 0 t G) := PrfH.hyp _ _ (List.Mem.head _)
  have hEQ : PrfH [substFormula 0 t G, lenc t =eq numeralM n, lineWF t]
      (carc t =eq T.objAt t) := PrfH.mp _ _ _ (prf_to_prfH hstruct _) hG
  -- (1) el puente `carc`, que es lo que `lineWF t` compra
  have hcarc : PrfH [substFormula 0 t G, lenc t =eq numeralM n, lineWF t]
      (provFromCode (eqc (carcT (tcFn t)) (tcFn (carc t)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_carcD_bridge t) _) hlw
  -- (2) la hipótesis estructural reescribe el valor, DENTRO de `Prov`
  have hcarc1 : PrfH [substFormula 0 t G, lenc t =eq numeralM n, lineWF t]
      (provFromCode (eqc (carcT (tcFn t)) (tcFn (T.objAt t)))) :=
    PrfH_provCode_congr
      (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) (PrfH_congr_tcFn hEQ)) hcarc
  -- (3) `tc_objAt`: aquí se pagan las guardas de los nodos `sub`
  have hcarc2 : PrfH [substFormula 0 t G, lenc t =eq numeralM n, lineWF t]
      (provFromCode (eqc (carcT (tcFn t)) (T.dotV t))) :=
    PrfH_eq_trans_code _ _ _ (substtc_inv_carcT_tcFn t) hcarc1
      (PrfH_tc_objAt t T hguards)
      (prf_hasWit_carcT (prf_hasWit_tcFn t)) (prf_hasWit_tcFn (T.objAt t))
      (prf_hasWit_dotV t T)
  -- (4) `dotV → dotN`, por inducción sobre el árbol
  have hfin : PrfH [substFormula 0 t G, lenc t =eq numeralM n, lineWF t]
      (provFromCode (eqc (carcT (tcFn t)) (T.dotN t))) :=
    PrfH_eq_trans_code _ _ _ (substtc_inv_carcT_tcFn t) hcarc2
      (PrfH_dotVN t hlenc T hmax)
      (prf_hasWit_carcT (prf_hasWit_tcFn t)) (prf_hasWit_dotV t T) (prf_hasWit_dotN t T)
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_condD_of_stree_eq T t))) _) hfin

/-! ## §7 · LOS TRES TAGS ALCANZABLES, CERRADOS

La obligación administrativa `hC` del chasis, para una condición guardada. -/

theorem substFormula_guardedCond_var0 :
    ∀ (gs : List GuardSlot) (C : Formula), substFormula 0 (.var 0) C = C →
      substFormula 0 (.var 0) (guardedCond gs C) = guardedCond gs C
  | [], C, h => h
  | g :: gs, C, h => by
      have hg : substFormula 0 (.var 0) g.toF = g.toF := by
        cases g with
        | wit i =>
            simp only [GuardSlot.toF, substF_hasWit, nthc, substTerm, substTerms,
              substTerm_numeralM, FOL.substTerm_liftTerm, if_true]
        | witF i =>
            simp only [GuardSlot.toF, substF_hasWitF, nthc, substTerm, substTerms,
              substTerm_numeralM, FOL.substTerm_liftTerm, if_true]
      simp only [guardedCond, substFormula, hg, substFormula_guardedCond_var0 gs C h]

/-- ⭐ **EL CIERRE DE UN TAG DE SUSTITUCIÓN**, genérico: basta declarar su árbol, su lista de
    guardas y descargar las dos obligaciones locales. -/
theorem pcc_lineWF_tracked_of_stree {k n : Nat} (T : STree) (t : Term)
    (gs : List GuardSlot) (hmax : Nat.le T.maxLeaf n) (h1n : 1 < n)
    (hax : Prf (Formula.forall (Formula.impl (tagF k)
      (lwfVar ⇔ Formula.and (lencF n) (guardedCond gs (condOfS T))))))
    (hcond : Hcond n t (guardedCond gs (condOfS T))) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k)
      ⇒ provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_schema t
    (substFormula_guardedCond_var0 gs (condOfS T) (substFormula_condOfS T)) hax hcond h1n


/-! ## §8 · q1 (tag 9), CERRADO — el piloto

⭐ Y aquí se ve por qué ADR‑020 puso la guarda donde la puso: **las casillas guardadas son
exactamente los hijos del nodo `sub`**. `treeQ1 = bin 5 (un 6 (leaf 2)) (sub (leaf 3) (leaf 2))`,
y la cascada del tag 9 es `[witF 2, wit 3]` — la `witF` sobre la casilla 2 (el cuerpo del
`substfc`) y la `wit` sobre la 3 (el sustituyendo). `SGuards` las pide **ahí y sólo ahí**. -/

theorem substF_wit_slot (t : Term) (i : Nat) :
    substFormula 0 t (GuardSlot.wit i).toF = hasWit (nthc t (numeralM i)) := by
  simp only [GuardSlot.toF, substF_hasWit, nthc, substTerm, substTerms, substTerm_numeralM,
    FOL.substTerm_liftTerm, if_true]

theorem substF_witF_slot (t : Term) (i : Nat) :
    substFormula 0 t (GuardSlot.witF i).toF = hasWitF (nthc t (numeralM i)) := by
  simp only [GuardSlot.toF, substF_hasWitF, nthc, substTerm, substTerms, substTerm_numeralM,
    FOL.substTerm_liftTerm, if_true]

/-- El núcleo estructural de **q1**, con la fórmula guardada entera a la vista. -/
theorem pcc_core_q1 (t : Term) :
    HcondCore 4 t (guardedCond [.witF 2, .wit 3] (condOfS treeQ1)) (condOfS treeQ1) := by
  refine pcc_condDS_of_stree treeQ1 t (n := 4) Nat.le.refl _ ?_ ?_
  · refine prf_deduction ?_
    have h := PrfH_and_elim_right (PrfH_and_elim_right
      (prfH_hyp_self (substFormula 0 t (guardedCond [.witF 2, .wit 3] (condOfS treeQ1)))))
    simpa only [guardedCond, substFormula_condOfS_at] using h
  · have hh : PrfH [substFormula 0 t (guardedCond [.witF 2, .wit 3] (condOfS treeQ1)),
        lenc t =eq numeralM 4, lineWF t]
        (substFormula 0 t (guardedCond [.witF 2, .wit 3] (condOfS treeQ1))) :=
      PrfH.hyp _ _ (List.Mem.head _)
    refine ⟨trivial, ⟨?_, ?_⟩, trivial, trivial⟩
    · have h := PrfH_and_elim_left (PrfH_and_elim_right hh)
      simpa only [guardedCond, substF_wit_slot, STree.objAt] using h
    · have h := PrfH_and_elim_left hh
      simpa only [guardedCond, substF_witF_slot, STree.objAt] using h

/-- ⭐⭐⭐ **EL REFLECTOR DEL TAG 9 (`q1`), PROBADO.** El primero de los siete. -/
theorem pcc_lineWF_tracked_q1_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 9)
      ⇒ provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_stree (k := 9) (n := 4) treeQ1 t [.witF 2, .wit 3] Nat.le.refl (by omega)
    (prf_ax (show ax_lineWF_q1 ∈ axioms by simp [axioms]))
    (hcond_absorbe_2 t 4 (.witF 2) (.wit 3) (condOfS treeQ1)
      (pcc_hGuardF 2 4 t (by omega)) (pcc_hGuardT 3 4 t (by omega)) (pcc_core_q1 t))


/-! ## §9 · q2 (tag 10) y leibniz (tag 13), CERRADOS

Con el piloto hecho, cada tag es **declarar su árbol y desempaquetar su cascada**. `leibniz`
tiene **dos** nodos `sub` (`A[t₁]` y `A[t₂]`) y por eso su cascada trae **tres** guardas: la
`witF` sobre el cuerpo, compartida por los dos, y una `wit` por cada sustituyendo. -/

theorem pcc_core_q2 (t : Term) :
    HcondCore 4 t (guardedCond [.witF 2, .wit 3] (condOfS treeQ2)) (condOfS treeQ2) := by
  refine pcc_condDS_of_stree treeQ2 t (n := 4) Nat.le.refl _ ?_ ?_
  · refine prf_deduction ?_
    have h := PrfH_and_elim_right (PrfH_and_elim_right
      (prfH_hyp_self (substFormula 0 t (guardedCond [.witF 2, .wit 3] (condOfS treeQ2)))))
    simpa only [guardedCond, substFormula_condOfS_at] using h
  · have hh : PrfH [substFormula 0 t (guardedCond [.witF 2, .wit 3] (condOfS treeQ2)),
        lenc t =eq numeralM 4, lineWF t]
        (substFormula 0 t (guardedCond [.witF 2, .wit 3] (condOfS treeQ2))) :=
      PrfH.hyp _ _ (List.Mem.head _)
    refine ⟨⟨⟨?_, ?_⟩, trivial, trivial⟩, trivial⟩
    · have h := PrfH_and_elim_left (PrfH_and_elim_right hh)
      simpa only [guardedCond, substF_wit_slot, STree.objAt] using h
    · have h := PrfH_and_elim_left hh
      simpa only [guardedCond, substF_witF_slot, STree.objAt] using h

/-- ⭐⭐⭐ **EL REFLECTOR DEL TAG 10 (`q2`), PROBADO.** -/
theorem pcc_lineWF_tracked_q2_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 10)
      ⇒ provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_stree (k := 10) (n := 4) treeQ2 t [.witF 2, .wit 3]
    Nat.le.refl (by omega)
    (prf_ax (show ax_lineWF_q2 ∈ axioms by simp [axioms]))
    (hcond_absorbe_2 t 4 (.witF 2) (.wit 3) (condOfS treeQ2)
      (pcc_hGuardF 2 4 t (by omega)) (pcc_hGuardT 3 4 t (by omega)) (pcc_core_q2 t))

theorem pcc_core_leibniz (t : Term) :
    HcondCore 5 t (guardedCond [.witF 2, .wit 3, .wit 4] (condOfS treeLeibniz))
      (condOfS treeLeibniz) := by
  refine pcc_condDS_of_stree treeLeibniz t (n := 5) Nat.le.refl _ ?_ ?_
  · refine prf_deduction ?_
    have h := PrfH_and_elim_right (PrfH_and_elim_right (PrfH_and_elim_right
      (prfH_hyp_self (substFormula 0 t
        (guardedCond [.witF 2, .wit 3, .wit 4] (condOfS treeLeibniz))))))
    simpa only [guardedCond, substFormula_condOfS_at] using h
  · have hh : PrfH [substFormula 0 t
        (guardedCond [.witF 2, .wit 3, .wit 4] (condOfS treeLeibniz)),
        lenc t =eq numeralM 5, lineWF t]
        (substFormula 0 t (guardedCond [.witF 2, .wit 3, .wit 4] (condOfS treeLeibniz))) :=
      PrfH.hyp _ _ (List.Mem.head _)
    -- ⚠️ los tipos van INLINE: un `have : PrfH _ (…)` no puede inferir el contexto
    exact ⟨⟨trivial, trivial⟩,
      ⟨⟨by simpa only [guardedCond, substF_wit_slot, STree.objAt] using
            PrfH_and_elim_left (PrfH_and_elim_right hh),
        by simpa only [guardedCond, substF_witF_slot, STree.objAt] using
            PrfH_and_elim_left hh⟩, trivial, trivial⟩,
      ⟨⟨by simpa only [guardedCond, substF_wit_slot, STree.objAt] using
            PrfH_and_elim_left (PrfH_and_elim_right (PrfH_and_elim_right hh)),
        by simpa only [guardedCond, substF_witF_slot, STree.objAt] using
            PrfH_and_elim_left hh⟩, trivial, trivial⟩⟩

/-- ⭐⭐⭐ **EL REFLECTOR DEL TAG 13 (`leibniz`), PROBADO.** Con él, **tres de los siete**. -/
theorem pcc_lineWF_tracked_leibniz_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 13)
      ⇒ provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_stree (k := 13) (n := 5) treeLeibniz t [.witF 2, .wit 3, .wit 4]
    Nat.le.refl (by omega)
    (prf_ax (show ax_lineWF_leibniz ∈ axioms by simp [axioms]))
    (hcond_absorbe_3 t 5 (.witF 2) (.wit 3) (.wit 4) (condOfS treeLeibniz)
      (pcc_hGuardF 2 5 t (by omega)) (pcc_hGuardT 3 5 t (by omega))
      (pcc_hGuardT 4 5 t (by omega)) (pcc_core_leibniz t))


/-! ## §10 · 🏁 q3 (tag 11) y qconf (tag 19), CERRADOS — **CINCO de los SIETE**

Lo único que faltaba era `pcc_eval_liftfc`, que el nodo `lift` de §1 consume en `PrfH_tc_objAt`.
El resto es el mismo gesto de §8–§9: declarar el árbol y desempaquetar su cascada — que aquí
tiene **una sola** guarda, así que el absorbedor es `hcond_absorbe_1`. -/

theorem pcc_core_q3 (t : Term) :
    HcondCore 4 t (guardedCond [.witF 3] (condOfS treeQ3)) (condOfS treeQ3) := by
  refine pcc_condDS_of_stree treeQ3 t (n := 4) Nat.le.refl _ ?_ ?_
  · refine prf_deduction ?_
    have h := PrfH_and_elim_right
      (prfH_hyp_self (substFormula 0 t (guardedCond [.witF 3] (condOfS treeQ3))))
    simpa only [guardedCond, substFormula_condOfS_at] using h
  · have hh : PrfH [substFormula 0 t (guardedCond [.witF 3] (condOfS treeQ3)),
        lenc t =eq numeralM 4, lineWF t]
        (substFormula 0 t (guardedCond [.witF 3] (condOfS treeQ3))) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hwF3 : PrfH [substFormula 0 t (guardedCond [.witF 3] (condOfS treeQ3)),
        lenc t =eq numeralM 4, lineWF t] (hasWitF (nthc t (numeralM 3))) := by
      have h := PrfH_and_elim_left hh
      simpa only [guardedCond, substF_witF_slot] using h
    exact ⟨⟨trivial, hwF3, trivial⟩, trivial, trivial⟩

/-- ⭐⭐⭐ **EL REFLECTOR DEL TAG 11 (`q3`), PROBADO.** El primero que consume `pcc_eval_liftfc`. -/
theorem pcc_lineWF_tracked_q3_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 11)
      ⇒ provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_stree (k := 11) (n := 4) treeQ3 t [.witF 3]
    Nat.le.refl (by omega)
    (prf_ax (show ax_lineWF_q3 ∈ axioms by simp [axioms]))
    (hcond_absorbe_1 t 4 (.witF 3) (condOfS treeQ3)
      (pcc_hGuardF 3 4 t (by omega)) (pcc_core_q3 t))

theorem pcc_core_qconf (t : Term) :
    HcondCore 4 t (guardedCond [.witF 2] (condOfS treeQconf)) (condOfS treeQconf) := by
  refine pcc_condDS_of_stree treeQconf t (n := 4) Nat.le.refl _ ?_ ?_
  · refine prf_deduction ?_
    have h := PrfH_and_elim_right
      (prfH_hyp_self (substFormula 0 t (guardedCond [.witF 2] (condOfS treeQconf))))
    simpa only [guardedCond, substFormula_condOfS_at] using h
  · have hh : PrfH [substFormula 0 t (guardedCond [.witF 2] (condOfS treeQconf)),
        lenc t =eq numeralM 4, lineWF t]
        (substFormula 0 t (guardedCond [.witF 2] (condOfS treeQconf))) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hwF2 : PrfH [substFormula 0 t (guardedCond [.witF 2] (condOfS treeQconf)),
        lenc t =eq numeralM 4, lineWF t] (hasWitF (nthc t (numeralM 2))) := by
      have h := PrfH_and_elim_left hh
      simpa only [guardedCond, substF_witF_slot] using h
    exact ⟨⟨⟨hwF2, trivial⟩, trivial⟩, trivial, trivial⟩

/-- ⭐⭐⭐ **EL REFLECTOR DEL TAG 19 (`qconf`), PROBADO.** Con él, **CINCO de los SIETE**.
    ⚠️ Faltan `ind` (18) y `listInd` (20), y lo que les falta está MEDIDO: sus `liftfc` van
    **anidados** (`liftfc 2 (liftfc 1 A)`) y bajo un `substfc`, así que la guarda que el
    evaluador pide es `hasWitF (liftfc 1 A)` — y la cascada sólo da `hasWitF A`. Hace falta la
    **clausura de `hasWitF` bajo `liftfc`**, que no existe en el árbol (sólo está la de
    TÉRMINO a nivel `zero`, `prf_hasWit_liftc`). -/
theorem pcc_lineWF_tracked_qconf_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 19)
      ⇒ provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_stree (k := 19) (n := 4) treeQconf t [.witF 2]
    Nat.le.refl (by omega)
    (prf_ax (show ax_lineWF_qconf ∈ axioms by simp [axioms]))
    (hcond_absorbe_1 t 4 (.witF 2) (condOfS treeQconf)
      (pcc_hGuardF 2 4 t (by omega)) (pcc_core_qconf t))


end ROBINSON_PlusPlus.Meta.SubstTreeReflect

/-! ## `export` — por PROPÓSITO DECLARADO

El consumidor previsto es `pcc_lineWF_tracked_modulo_7` (`Meta/LineWFAssemblePrf.lean`), que
pide un reflector por tag. Este módulo le entrega **tres de los siete**:
`pcc_lineWF_tracked_q1_imp` (tag 9), `_q2_imp` (10) y `_leibniz_imp` (13).

⚠️ **Los otros cuatro** —q3 (11), qconf (19), ind (18), listInd (20)— **esperan a
`pcc_eval_liftfc`**, que no existe en ningún sitio; son exactamente los que llevan `liftfc`
(§3.47.1). Hasta que estén los siete, `pcc_lineWF_tracked` sigue siendo condicional.

Nada lo consume todavía, y se dice en vez de fingir una medición de consumo. -/
export ROBINSON_PlusPlus.Meta.SubstTreeReflect (
  STree substTerm_objAt substTerm_objAt_var0 code_eq_termCode prf_substtc_code
  substtc_inv_dotN substtc_inv_dotV prf_hasWit_dotN prf_hasWit_dotV
  condOfS substFormula_condOfS substFormula_condOfS_at prf_condD_of_stree_eq
  treeQ1 treeQ2 treeLeibniz treeQ3 treeQconf
  SGuards PrfH_tc_objAt PrfH_dotVN pcc_condDS_of_stree
  substFormula_guardedCond_var0 pcc_lineWF_tracked_of_stree
  substF_wit_slot substF_witF_slot
  pcc_core_q1 pcc_core_q2 pcc_core_leibniz pcc_core_q3 pcc_core_qconf
  pcc_lineWF_tracked_q1_imp pcc_lineWF_tracked_q2_imp pcc_lineWF_tracked_leibniz_imp
  pcc_lineWF_tracked_q3_imp pcc_lineWF_tracked_qconf_imp
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.SubstTreeReflect.prf_substtc_code
#print axioms ROBINSON_PlusPlus.Meta.SubstTreeReflect.prf_condD_of_stree_eq
#print axioms ROBINSON_PlusPlus.Meta.SubstTreeReflect.PrfH_tc_objAt
#print axioms ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_q1_imp
#print axioms ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_q2_imp
#print axioms ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_leibniz_imp
#print axioms ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_q3_imp
#print axioms ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_qconf_imp
