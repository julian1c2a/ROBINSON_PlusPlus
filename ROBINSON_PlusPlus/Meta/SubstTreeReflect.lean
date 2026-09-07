import ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf
import ROBINSON_PlusPlus.Meta.EvalSubstfcPrf
import ROBINSON_PlusPlus.Meta.CodeTreeReflect
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
  deriving Repr

namespace STree

/-- La expresión OBJETO del árbol sobre una línea `t`. -/
def objAt (t : Term) : STree → Term
  | leaf i    => nthc t (numeralM i)
  | nul m     => cons (numeralM m) nil
  | un m a    => cons (numeralM m) (cons (a.objAt t) nil)
  | bin m a b => cons (numeralM m) (cons (a.objAt t) (cons (b.objAt t) nil))
  | sub s f   => substfc zero (s.objAt t) (f.objAt t)

/-- El código ESTÁTICO, con el hueco `⌜v₀⌝` en las hojas. -/
def code : STree → Term
  | leaf i    => nthcT (varc (numeral 0)) (termCode (numeralM i))
  | nul m     => nulT m
  | un m a    => unT m a.code
  | bin m a b => binT m a.code b.code
  | sub s f   => substfcT (termCode zero) s.code f.code

/-- Forma **N** (accesores rastreados). -/
def dotN (t : Term) : STree → Term
  | leaf i    => nthcT (tcFn t) (termCode (numeralM i))
  | nul m     => nulT m
  | un m a    => unT m (a.dotN t)
  | bin m a b => binT m (a.dotN t) (b.dotN t)
  | sub s f   => substfcT (termCode zero) (s.dotN t) (f.dotN t)

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

/-- Cota estricta de los índices de hoja. -/
def maxLeaf : STree → Nat
  | leaf i    => i + 1
  | nul _     => 0
  | un _ a    => a.maxLeaf
  | bin _ a b => Nat.max a.maxLeaf b.maxLeaf
  | sub s f   => Nat.max s.maxLeaf f.maxLeaf

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

/-! ### La GUARDA de las dos formas (ADR-020), por la misma inducción -/

theorem prf_hasWit_dotV (t : Term) : ∀ T : STree, Prf (hasWit (T.dotV t))
  | .leaf i    => prf_hasWit_tcFn (nthc t (numeralM i))
  | .nul m     => prf_hasWit_nulT m
  | .un m a    => prf_hasWit_unT m (prf_hasWit_dotV t a)
  | .bin m a b => prf_hasWit_binT m (prf_hasWit_dotV t a) (prf_hasWit_dotV t b)
  | .sub s f   => prf_hasWit_funcc3 _ _ _ _ (prf_hasWit_tc zero)
      (prf_hasWit_dotV t s) (prf_hasWit_dotV t f)

theorem prf_hasWit_dotN (t : Term) : ∀ T : STree, Prf (hasWit (T.dotN t))
  | .leaf i    => prf_hasWit_nthcT (prf_hasWit_tcFn t) (prf_hasWit_tc (numeralM i))
  | .nul m     => prf_hasWit_nulT m
  | .un m a    => prf_hasWit_unT m (prf_hasWit_dotN t a)
  | .bin m a b => prf_hasWit_binT m (prf_hasWit_dotN t a) (prf_hasWit_dotN t b)
  | .sub s f   => prf_hasWit_funcc3 _ _ _ _ (prf_hasWit_tc zero)
      (prf_hasWit_dotN t s) (prf_hasWit_dotN t f)

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

end ROBINSON_PlusPlus.Meta.SubstTreeReflect

/-! ## `export` — por PROPÓSITO DECLARADO

El consumidor previsto es el cierre de los tres reflectores alcanzables (q1, q2, leibniz):
quien pruebe `PrfH_dotVN` para `STree` —cuyo único caso nuevo es el nodo `sub`, y lo paga
`pcc_eval_substfc_wit` con las guardas que `hcond_absorbe_1/2/3` ponen en el contexto— cierra
los tres declarando su árbol. Nada lo consume todavía, y se dice en vez de fingir una medición
de consumo. -/
export ROBINSON_PlusPlus.Meta.SubstTreeReflect (
  STree substTerm_objAt substTerm_objAt_var0 code_eq_termCode prf_substtc_code
  substtc_inv_dotN substtc_inv_dotV prf_hasWit_dotN prf_hasWit_dotV
  condOfS substFormula_condOfS substFormula_condOfS_at prf_condD_of_stree_eq
  treeQ1 treeQ2 treeLeibniz
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.SubstTreeReflect.prf_substtc_code
#print axioms ROBINSON_PlusPlus.Meta.SubstTreeReflect.prf_condD_of_stree_eq
