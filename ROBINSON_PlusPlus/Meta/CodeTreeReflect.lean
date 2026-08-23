/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CodeCtorKit

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
open ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit
open ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.BdAllIntroPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.CodeTreeReflect

/-!
## META — NIVEL D real (B.3c): reflexión de un ÁRBOL DE CÓDIGO por INDUCCIÓN

El piloto `efq` midió el coste por tag con el chasis: ~100 líneas de parte propia. Con 17 tags
pendientes eso son ~1700 líneas casi idénticas — y los árboles de `p2`/`j3` tienen 5–6 nodos, así
que además serían frágiles.

**Observación que lo colapsa todo.** La condición estructural de los 18 tags con RHS ecuacional es
siempre `carc #0 = E(nthc #0 i…)`, con `E` un árbol construido con los constructores del kit
(`nulT`/`unT`/`binT`) sobre hojas que son accesores `nthc #0 i`. Es decir: `E` recorre un **tipo de
datos**, y la reflexión se puede probar **por inducción sobre él, una sola vez**.

Este módulo reifica esos árboles (`CTree`) y prueba genéricamente:

* `prf_substtc_code` — la evaluación del código punteado (distribución de `substtc` sobre el árbol);
* `substtc_inv_dotN` / `substtc_inv_dotV` — las invariancias que consumen los Leibniz internos;
* `prf_tc_objAt` — el «código del código» del árbol;
* **`PrfH_dotVN`** — la pieza cara: `Prov(⌜E(valores) = E(accesores)⌝)`, por inducción, usando
  `pcc_nthcD_bridge` en las hojas y las congruencias internas del kit en los nodos;
* `pcc_condD_of_tree` — el **reflector `hcond` que pide el chasis**, ya genérico.

Resultado: cada uno de los 17 tags restantes se reduce a **declarar su árbol** y comprobar dos
igualdades definicionales.
-/

/-- Árbol de código con hojas‑accesor. Reifica los RHS estructurales de los esquemas `lineWF`:
    `leaf i` = `nthc · i`; `nul`/`un`/`bin` = los constructores de código por aridad y tag
    (`botc` = `nul 2`, `eqc` = `bin 4`, `implc` = `bin 5`, `forallc` = `un 6`, `andc` = `bin 7`,
    `orc` = `bin 8`, `exc` = `un 9`). -/
inductive CTree where
  | leaf : Nat → CTree
  | nul  : Nat → CTree
  | un   : Nat → CTree → CTree
  | bin  : Nat → CTree → CTree → CTree
  deriving Repr

namespace CTree

/-- La expresión OBJETO del árbol sobre una línea `t`. -/
def objAt (t : Term) : CTree → Term
  | leaf i    => nthc t (numeralM i)
  | nul m     => cons (numeralM m) nil
  | un m a    => cons (numeralM m) (cons (a.objAt t) nil)
  | bin m a b => cons (numeralM m) (cons (a.objAt t) (cons (b.objAt t) nil))

/-- El código ESTÁTICO del árbol, con el hueco `⌜v₀⌝` en las hojas. -/
def code : CTree → Term
  | leaf i    => nthcT (varc (numeral 0)) (termCode (numeralM i))
  | nul m     => nulT m
  | un m a    => unT m a.code
  | bin m a b => binT m a.code b.code

/-- Forma **N** (accesores rastreados): las hojas son `nthcT ṫ ı̇`. -/
def dotN (t : Term) : CTree → Term
  | leaf i    => nthcT (tcFn t) (termCode (numeralM i))
  | nul m     => nulT m
  | un m a    => unT m (a.dotN t)
  | bin m a b => binT m (a.dotN t) (b.dotN t)

/-- Forma **V** (valores punteados): las hojas son `(nthc t ı)˙`. -/
def dotV (t : Term) : CTree → Term
  | leaf i    => tcFn (nthc t (numeralM i))
  | nul m     => nulT m
  | un m a    => unT m (a.dotV t)
  | bin m a b => binT m (a.dotV t) (b.dotV t)

/-- Cota estricta de los índices de hoja (`0` si no hay hojas). Es lo que la longitud canónica
    del esquema debe dominar para que todas las cotas de sub‑índice sean derivables. -/
def maxLeaf : CTree → Nat
  | leaf i    => i + 1
  | nul _     => 0
  | un _ a    => a.maxLeaf
  | bin _ a b => Nat.max a.maxLeaf b.maxLeaf

end CTree

open CTree

/-! ### Las tres igualdades estructurales (inducción pura sobre el árbol) -/

/-- La expresión objeto sobre `#0` es invariante al instanciar el `∀` en `#0`: es la obligación
    administrativa `hC` que pide el chasis, resuelta de una vez para todo árbol. -/
theorem substTerm_objAt :
    ∀ (T : CTree) (t : Term), substTerm 0 t (T.objAt (.var 0)) = T.objAt t
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

/-- Caso `t = #0`: es la obligación administrativa `hC` que pide el chasis. -/
theorem substTerm_objAt_var0 (T : CTree) :
    substTerm 0 (.var 0) (T.objAt (.var 0)) = T.objAt (.var 0) := substTerm_objAt T (.var 0)

/-- El código estático del árbol **es** el `termCode` de su expresión objeto sobre `#0`. Es el
    puente que conecta `CTree.code` con lo que `formCode (condOf T)` produce de verdad. -/
theorem code_eq_termCode : ∀ T : CTree, CTree.code T = termCode (T.objAt (.var 0))
  | .leaf _ => rfl
  | .nul _ => rfl
  | .un m a => by
      simp only [CTree.code, CTree.objAt, code_eq_termCode a, unT_termCode]
  | .bin m a b => by
      simp only [CTree.code, CTree.objAt, code_eq_termCode a, code_eq_termCode b, binT_termCode]

/-- **Evaluación del código punteado**: sustituir `ṫ` en el hueco del código estático da la forma
    rastreada `dotN`. Es la distribución de `substtc` sobre el árbol, del kit. -/
theorem prf_substtc_code (t : Term) :
    ∀ T : CTree, Prf (substtc zero (tcFn t) T.code =eq T.dotN t)
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

/-- `dotN` es `substtc`‑invariante. -/
theorem substtc_inv_dotN (t : Term) :
    ∀ (T : CTree) (W : Term), Prf (substtc zero W (T.dotN t) =eq T.dotN t)
  | .leaf i, W => substtc_inv_nthcT_tcFn t i W
  | .nul m, W => prf_substtc_nulT m W
  | .un m a, W =>
      prf_eq_trans (prf_substtc_unT m W (a.dotN t)) (prf_congr_unT (substtc_inv_dotN t a W))
  | .bin m a b, W =>
      prf_eq_trans (prf_substtc_binT m W (a.dotN t) (b.dotN t))
        (prf_congr_binT (substtc_inv_dotN t a W) (substtc_inv_dotN t b W))

/-- `dotV` es `substtc`‑invariante. -/
theorem substtc_inv_dotV (t : Term) :
    ∀ (T : CTree) (W : Term), Prf (substtc zero W (T.dotV t) =eq T.dotV t)
  | .leaf _, W => substtc_inv_tcFn _ W
  | .nul m, W => prf_substtc_nulT m W
  | .un m a, W =>
      prf_eq_trans (prf_substtc_unT m W (a.dotV t)) (prf_congr_unT (substtc_inv_dotV t a W))
  | .bin m a b, W =>
      prf_eq_trans (prf_substtc_binT m W (a.dotV t) (b.dotV t))
        (prf_congr_binT (substtc_inv_dotV t a W) (substtc_inv_dotV t b W))

/-- **El código del código del árbol**: `(E(nthc t i…))˙ = dotV`, ahora **DENTRO de `Prov`**.

    ⚠️ **Éste era el coste real de repatriar el KIT** (medido en `sondeos/KitPayoff.lean`): la
    versión vieja era esta misma recursión produciendo una igualdad **de CÓDIGO**, y las ecuaciones
    `tc` del kit murieron con `ax_tc_cons`. Como sus sustitutos (`pcc_dot_*`) son **internos**, la
    recursión entera se muda dentro de `Prov`.

    La conversión es literal, pieza por pieza — y todas existían ya:
    * `prf_eq_trans` ⟶ **`pcc_eq_trans_code`** (`EvalArithPrf`);
    * `prf_congr_unT`/`prf_congr_binT` ⟶ **`pcc_congr_unT_code`** / `pcc_congr_binT_1_code` /
      `pcc_congr_binT_2_code` (`CodeCtorKit`), que **sobrevivieron intactas** y ya venían en forma
      implicación, que es justo lo que la recursión interna pide;
    * `prf_refl` ⟶ `prf_provFromCode_eqCodeFn_refl`;
    * las ecuaciones `tc` del kit ⟶ `pcc_dot_nul_symm` / `_un_symm` / `_bin_symm`.

    En el caso binario hacen falta **dos** congruencias encadenadas (una por argumento), donde antes
    bastaba una `prf_congr_binT` simultánea: dentro de `Prov` los argumentos se reescriben de uno en
    uno. -/
theorem pcc_tc_objAt (t : Term) :
    ∀ T : CTree, Prf (provFromCode (eqc (tcFn (T.objAt t)) (T.dotV t)))
  | .leaf _ => prf_provFromCode_eqCodeFn_refl _
  | .nul m => pcc_dot_nul_symm m
  | .un m a =>
      pcc_eq_trans_code _ _ _ (substtc_inv_tcFn _)
        (pcc_dot_un_symm m (a.objAt t))
        (prf_mp (pcc_congr_unT_code m (tcFn (a.objAt t)) (a.dotV t) (substtc_inv_tcFn _))
          (pcc_tc_objAt t a))
  | .bin m a b =>
      pcc_eq_trans_code _ _ _ (substtc_inv_tcFn _)
        (pcc_dot_bin_symm m (a.objAt t) (b.objAt t))
        (pcc_eq_trans_code _ _ _
          (substtc_inv_binT (substtc_inv_tcFn _) (substtc_inv_tcFn _))
          (prf_mp (pcc_congr_binT_1_code m (tcFn (b.objAt t)) (tcFn (a.objAt t)) (a.dotV t)
              (substtc_inv_tcFn _) (substtc_inv_tcFn _))
            (pcc_tc_objAt t a))
          (prf_mp (pcc_congr_binT_2_code m (a.dotV t) (tcFn (b.objAt t)) (b.dotV t)
              (substtc_inv_dotV t a) (substtc_inv_tcFn _))
            (pcc_tc_objAt t b)))

/-! ### La pieza cara: `Prov(⌜E(valores) = E(accesores)⌝)`, por inducción

Hojas: el puente `pcc_nthcD_bridge` (con la cota derivada de la longitud canónica), invertido.
Nodos: las congruencias internas del kit, encadenadas por transitividad interna. -/

/-- **`Prov(⌜dotV = dotN⌝)`** para todo árbol cuyas hojas caigan bajo la longitud canónica.

    ⚠️ La cota se escribe `Nat.le … n` y **no** `… ≤ n`: con `Minimal.Axioms` abierto, `≤` resuelve
    al orden OBJETO (sobre `Term`), no al de `Nat`, y el error que produce es opaco. -/
theorem PrfH_dotVN {Γ : List Formula} (t : Term) {n : Nat}
    (hlenc : PrfH Γ (lenc t =eq numeralM n)) (T : CTree) :
    Nat.le (CTree.maxLeaf T) n →
      PrfH Γ (provFromCode (eqc (CTree.dotV t T) (CTree.dotN t T))) := by
  induction T with
  | leaf i =>
      intro hb
      have hbound : PrfH Γ (lt (numeralM i) (lenc t)) :=
        PrfH_lt_of_lenc_eq (i := i) (n := n) hb hlenc
      have hev : PrfH Γ (provFromCode (eqc (nthcT (tcFn t) (termCode (numeralM i)))
          (tcFn (nthc t (numeralM i))))) :=
        PrfH.mp _ _ _ (prf_to_prfH (pcc_nthcD_bridge t i) _) hbound
      exact PrfH_eq_symm_code _ _ (substtc_inv_nthcT_tcFn t i) hev
  | nul m => intro _; exact prf_to_prfH (prf_provFromCode_eqCodeFn_refl (nulT m)) _
  | un m a ih =>
      intro hb
      exact PrfH.mp _ _ _
        (prf_to_prfH (pcc_congr_unT_code m (CTree.dotV t a) (CTree.dotN t a)
          (substtc_inv_dotV t a)) _) (ih hb)
  | bin m a b iha ihb =>
      intro hb
      have hba : Nat.le (CTree.maxLeaf a) n := Nat.le_trans (Nat.le_max_left _ _) hb
      have hbb : Nat.le (CTree.maxLeaf b) n := Nat.le_trans (Nat.le_max_right _ _) hb
      -- primero el argumento izquierdo, luego el derecho; se componen por transitividad interna
      have h1 : PrfH Γ (provFromCode (eqc (binT m (CTree.dotV t a) (CTree.dotV t b))
          (binT m (CTree.dotN t a) (CTree.dotV t b)))) :=
        PrfH.mp _ _ _
          (prf_to_prfH (pcc_congr_binT_1_code m (CTree.dotV t b) (CTree.dotV t a)
            (CTree.dotN t a) (substtc_inv_dotV t b) (substtc_inv_dotV t a)) _)
          (iha hba)
      have h2 : PrfH Γ (provFromCode (eqc (binT m (CTree.dotN t a) (CTree.dotV t b))
          (binT m (CTree.dotN t a) (CTree.dotN t b)))) :=
        PrfH.mp _ _ _
          (prf_to_prfH (pcc_congr_binT_2_code m (CTree.dotN t a) (CTree.dotV t b)
            (CTree.dotN t b) (substtc_inv_dotN t a) (substtc_inv_dotV t b)) _)
          (ihb hbb)
      exact PrfH_eq_trans_code _ _ _
        (substtc_inv_binT (substtc_inv_dotV t a) (substtc_inv_dotV t b)) h1 h2

/-! ### El reflector `hcond` del chasis, ya genérico -/

/-- La condición estructural asociada a un árbol: `carc #0 = E(nthc #0 i…)`. -/
def condOf (T : CTree) : Formula := carc (.var 0) =eq T.objAt (.var 0)

/-- La obligación administrativa del chasis, resuelta para todo árbol. -/
theorem substFormula_condOf (T : CTree) : substFormula 0 (.var 0) (condOf T) = condOf T := by
  simp only [condOf, carc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true,
    substTerm_objAt_var0 T]

/-- La condición instanciada en una línea concreta. -/
theorem substFormula_condOf_at (T : CTree) (t : Term) :
    substFormula 0 t (condOf T) = (carc t =eq T.objAt t) := by
  simp only [condOf, carc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true,
    substTerm_objAt T t]

/-- **`COND_dot` evaluado**, genérico en el árbol. -/
theorem prf_condD_of_tree_eq (T : CTree) (t : Term) :
    Prf (condD (condOf T) t =eq eqCodeFn (carcT (tcFn t)) (T.dotN t)) := by
  unfold condD condOf
  refine prf_eq_trans (prf_substfc_eq zero (tcFn t) _ _) ?_
  refine prf_congr_eqCodeFn ?_ (code_eq_termCode T ▸ prf_substtc_code t T)
  exact prf_eq_trans (prf_substtc_carcT zero (tcFn t) _)
    (prf_congr_carcT (prf_substtc_varc0 (tcFn t)))

/-- **REFLECTOR GENÉRICO** de una condición‑árbol: exactamente la hipótesis `hcond` que pide
    `pcc_lineWF_tracked_of_schema`. Con esto, cada tag estructural se reduce a declarar su árbol. -/
theorem pcc_condD_of_tree (T : CTree) (t : Term) {n : Nat} (hmax : Nat.le (CTree.maxLeaf T) n) :
    Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒
      (substFormula 0 t (condOf T) ⇒ provFromCode (condD (condOf T) t)))) := by
  rw [substFormula_condOf_at]
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (carc t =eq T.objAt t) [lenc t =eq numeralM n, lineWF t] rfl)
    (lenc t =eq numeralM n) [lineWF t] rfl)
  let Γ : List Formula := [carc t =eq T.objAt t, lenc t =eq numeralM n, lineWF t]
  have hlw : PrfH Γ (lineWF t) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hlenc : PrfH Γ (lenc t =eq numeralM n) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hEQ : PrfH Γ (carc t =eq T.objAt t) := PrfH.hyp _ _ (List.Mem.head _)
  -- (1) puente `carc` + (2) la hipótesis reescribe el valor a `dotV`
  have hcarc : PrfH Γ (provFromCode (eqc (carcT (tcFn t)) (tcFn (carc t)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_carcD_bridge t) _) hlw
  -- CÓDIGO: la congruencia de `tcFn` sigue viva y lleva `(carc t)˙` a `(T.objAt t)˙`
  have hcarc1 : PrfH Γ (provFromCode (eqc (carcT (tcFn t)) (tcFn (T.objAt t)))) :=
    PrfH_provCode_congr
      (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) (PrfH_congr_tcFn hEQ)) hcarc
  -- INTERNO: y de ahí a `dotV`, por transitividad dentro de `Prov`
  have hcarc2 : PrfH Γ (provFromCode (eqc (carcT (tcFn t)) (T.dotV t))) :=
    PrfH_eq_trans_code _ _ _ (substtc_inv_carcT_tcFn t) hcarc1
      (prf_to_prfH (pcc_tc_objAt t T) _)
  -- (3) `dotV → dotN` por inducción sobre el árbol
  have hVN : PrfH Γ (provFromCode (eqc (T.dotV t) (T.dotN t))) :=
    PrfH_dotVN t hlenc T hmax
  -- (4) transitividad interna + vuelta a la forma `substfc`
  have hfin : PrfH Γ (provFromCode (eqc (carcT (tcFn t)) (T.dotN t))) :=
    PrfH_eq_trans_code _ _ _ (substtc_inv_carcT_tcFn t) hcarc2 hVN
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_condD_of_tree_eq T t))) _) hfin

/-- **CIERRE DE UN TAG ESTRUCTURAL**, todo junto. Instanciar esto con el árbol del tag es lo único
    que queda por hacer para cada uno de los esquemas con RHS ecuacional. -/
theorem pcc_lineWF_tracked_of_tree {k n : Nat} (T : CTree) (t : Term)
    (hax : Prf (Formula.forall (Formula.impl (tagF k)
      (lwfVar ⇔ Formula.and (lencF n) (condOf T)))))
    (hmax : Nat.le (CTree.maxLeaf T) n) (h1n : 1 < n) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_schema t (substFormula_condOf T) hax (pcc_condD_of_tree T t hmax) h1n

end ROBINSON_PlusPlus.Meta.CodeTreeReflect

export ROBINSON_PlusPlus.Meta.CodeTreeReflect (
  CTree substTerm_objAt substTerm_objAt_var0 code_eq_termCode prf_substtc_code substtc_inv_dotN substtc_inv_dotV
  pcc_tc_objAt PrfH_dotVN condOf substFormula_condOf substFormula_condOf_at
  prf_condD_of_tree_eq pcc_condD_of_tree pcc_lineWF_tracked_of_tree
)
