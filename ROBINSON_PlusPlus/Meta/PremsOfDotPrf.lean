/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.PremsOfTagPrf
import ROBINSON_PlusPlus.Meta.SubstTreeReflect

/-!
# B1 · `premsOf` REFLEJADO **dentro de `Prov`** — las 21 ramas

`Meta/PremsOfTagPrf.lean` evaluó `premsOf` a nivel **OBJETO**. Esto lo cruza a `Prov`:

    ⊢ lineWF t  ⇒  Prov( ⌜ premsOf ṫ = (premsOf t)˙ ⌝ )

que es el eslabón que a la **cota** de `hbody`(b) le faltaba (§13.1/§13.3 de `D3ChainDotPrf`).

## La ruta, que es la de `pcc_eval_carc` (§`EvalListPrf`)

1. **el axioma CODIFICADO** (`pcc_axiom_inst`/`2`/`3`/`4`) instanciado con testigos **dotados**;
2. abrir hacia el gemelo computable (`prf_substfc_arith_open`) y **casar por `rfl`**;
3. los `liftc` de los testigos **colapsan** (`prf_liftc_tcFn`);
4. los `substfc` externos, distribuidos sobre el código explícito;
5. los subtérminos **cerrados** (`k̄`, `nil`, el `5̄` de `implc`), dotados — **a nivel objeto**;
6. y el **transporte en cascada** `consT ẋ ẏ ↦ (cons x y)˙`, que es `pcc_dot_cons` iterado.

⭐ **El paso 6 es el único que hubo que inventar**, y sale genérico: `pcc_rw_dot_consN` recorre una
lista entera. ⚠️ Su contrato sobre el contexto `G` es **más fuerte** que el de `pcc_rw`: no basta
saber qué hace `substfc` sobre `G ⌜v₀⌝`, hace falta que `G` **conmute** con `substfc`, porque la
recursión mete el prefijo `consT ẋ ·` DENTRO del contexto en cada piso.

## ⚠️ Cuatro cosas medidas al escribirlo

* **Con el tag `k` VARIABLE, `substCodeF` no computa** (`numeralM k` lo bloquea) ⇒ el `hcode` sale
  como **parámetro**, descargado con `rfl` en cada instancia. Es la trampa de §3.53, otra vez.
* **`nil` es `zero`**, luego `nil = numeralM 0` y su dotado es `prf_tc_numeralM 0`.
* **`implc a b = ⟨5̄, a, b⟩` es un `cons`**, así que el RHS de `mp` se transporta con la MISMA
  cascada, anidada dos veces. No hizo falta maquinaria nueva para el único tag con premisas reales.
* Los `substfc` externos de aridad ≥ 3 actúan a **nivel > 0** ⇒ hacen falta las versiones a nivel
  arbitrario (`prf_substtc_tcFn_at`, `substtc_inv_tc_closed`, `prf_substtc_varc_eq/_lt`).
  ⚠️ **No hay decrementos de índice**: tras cada paso las variables que quedan son todas `< v`.

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
open ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
open ROBINSON_PlusPlus.Meta.ListEtaPrf
open ROBINSON_PlusPlus.Meta.PremsOfTagPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.LineWFAssemblePrf
open ROBINSON_PlusPlus.Meta.SubstTreeReflect

set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000

namespace ROBINSON_PlusPlus.Meta.PremsOfDotPrf


/-! ## §1 · `premsOfT` y su fontanería -/

/-- Código object del término `premsOf x` desde el código `x`. -/
def premsOfT (x : Term) : Term := funcc (strCode "premsOf") (cons x nil)

theorem premsOfT_termCode (a : Term) : premsOfT (termCode a) = termCode (premsOf a) := rfl

/-- ⭐ **LA MEDICIÓN**: `substCodeT` produce exactamente `premsOfT`. -/
theorem substCodeT_premsOf (v : Nat) (W X : Term) :
    substCodeT v W (premsOf X) = premsOfT (substCodeT v W X) := rfl

theorem prf_hasWit_premsOfT {X : Term} (hX : Prf (hasWit X)) : Prf (hasWit (premsOfT X)) :=
  prf_hasWit_funcc1 (strCode "premsOf") X hX

theorem prf_congr_premsOfT {x y : Term} (h : Prf (x =eq y)) : Prf (premsOfT x =eq premsOfT y) :=
  prf_congr_funcc2 (prf_congr_cons_head h)

theorem prf_substtc_premsOfT (v W x : Term) :
    Prf (substtc v W (premsOfT x) =eq premsOfT (substtc v W x)) :=
  prf_substtc_funcc1 v W (strCode "premsOf") x

/-! ## §2 · Listas objeto y su versión de CÓDIGO DOTADO -/

/-- La lista objeto `⟨x₀,…⟩` como `cons` anidados.

    ⚠️ **Se llama `consL` (por LISTA) y no `consN` a propósito**: `Meta/CodeNumeralPrf.lean` ya
    exporta un `consN : Nat → Nat → Nat` (el emparejamiento de Cantor) y los dos irían a la raíz.
    Es la clase de colisión que ADR‑019 persigue; se cazó el 2026‑09‑10h al escribir un sondeo que
    usaba los dos. -/
def consL : List Term → Term
  | []      => nil
  | x :: xs => cons x (consL xs)

/-- Su versión de código con cada componente **dotado**: `consT ẋ₀ (consT ẋ₁ … ⌜nil⌝˙)`. -/
def consLT : List Term → Term
  | []      => tcFn nil
  | x :: xs => consT (tcFn x) (consLT xs)

theorem prf_hasWit_consNT : ∀ xs : List Term, Prf (hasWit (consLT xs))
  | []      => prf_hasWit_tcFn nil
  | x :: xs => prf_hasWit_consT (prf_hasWit_tcFn x) (prf_hasWit_consNT xs)

theorem substtc_inv_consNT : ∀ (xs : List Term) (W : Term),
    Prf (substtc zero W (consLT xs) =eq consLT xs)
  | [], W      => substtc_inv_tcFn nil W
  | x :: xs, W =>
      prf_eq_trans (prf_substtc_consT zero W (tcFn x) (consLT xs))
        (prf_congr_consT (prf_substtc_tcFn W x) (substtc_inv_consNT xs W))

/-! ## §3 · EL TRANSPORTE EN CASCADA `consT ẋ ẏ ↦ (cons x y)˙`

⚠️ El contrato del contexto `G` es **más fuerte** que el de `pcc_rw`: no basta saber qué hace
`substfc` sobre `G (varc 0̄)`, hace falta que `G` **conmute** con `substfc`, porque la recursión
mete el prefijo `consT ẋ ·` DENTRO del contexto en cada piso. -/

theorem pcc_rw_dot_consN [AnclaEq]
    (G : Term → Term)
    (hGs : ∀ s c : Term, Prf (substfc zero s (G c) =eq G (substtc zero s c)))
    (hGc : ∀ c c' : Term, Prf (c =eq c') → Prf (G c =eq G c'))
    (hwG : ∀ c : Term, Prf (hasWit c) → Prf (hasWitF (G c))) :
    ∀ (xs : List Term), Prf (provFromCode (G (consLT xs))) →
      Prf (provFromCode (G (tcFn (consL xs))))
  | [], hbase => hbase
  | x :: xs, hbase => by
      -- (1) recursión sobre la COLA, con el contexto `G' c := G (consT ẋ c)`
      have h1 : Prf (provFromCode (G (consT (tcFn x) (tcFn (consL xs))))) := by
        refine pcc_rw_dot_consN (fun c => G (consT (tcFn x) c)) ?_ ?_ ?_ xs hbase
        · intro s c
          refine prf_eq_trans (hGs s (consT (tcFn x) c)) (hGc _ _ ?_)
          exact prf_eq_trans (prf_substtc_consT zero s (tcFn x) c)
            (prf_congr_consT (prf_substtc_tcFn s x) (prf_refl _))
        · exact fun c c' h => hGc _ _ (prf_congr_consT (prf_refl _) h)
        · exact fun c hc => hwG _ (prf_hasWit_consT (prf_hasWit_tcFn x) hc)
      -- (2) el piso exterior
      refine pcc_rw G ?_ _ _ (pcc_dot_cons x (consL xs)) h1
        (hwG _ (prf_hasWit_varc (numeral 0)))
        (prf_hasWit_consT (prf_hasWit_tcFn x) (prf_hasWit_tcFn (consL xs)))
        (prf_hasWit_tcFn (cons x (consL xs)))
      intro s
      exact prf_eq_trans (hGs s (varc (numeral 0))) (hGc _ _ (prf_substtc_varc0 s))

/-! ## §4 · PILOTO: tag 15 (`thy`), aridad 1 -/

/-- El contexto de código de la ecuación, con el argumento de `premsOf` abierto. -/
def GT (R : Term) (c : Term) : Term := eqCodeFn (premsOfT c) R

theorem GT_subst (R : Term) (hR : ∀ W, Prf (substtc zero W R =eq R)) (s c : Term) :
    Prf (substfc zero s (GT R c) =eq GT R (substtc zero s c)) := by
  refine prf_eq_trans (prf_substfc_eq zero s (premsOfT c) R) ?_
  exact prf_congr_eqCodeFn (prf_substtc_premsOfT zero s c) (hR s)

theorem GT_congr (R : Term) {c c' : Term} (h : Prf (c =eq c')) :
    Prf (GT R c =eq GT R c') := prf_congr_eqCodeFn (prf_congr_premsOfT h) (prf_refl _)

theorem GT_wit (R : Term) (hR : Prf (hasWit R)) (c : Term) (hc : Prf (hasWit c)) :
    Prf (hasWitF (GT R c)) := prf_hasWitF_eq2 _ _ (prf_hasWit_premsOfT hc) hR

/-- La medición por `rfl` del `substCodeF` del cuerpo de `ax_premsOf_thy`. -/
theorem meas_thy (W : Term) :
    substCodeF 0 W (premsOf (cons (.var 0) (cons (numeralM 15) nil)) =eq nil)
      = GT (termCode nil) (consT W (consT (termCode (numeralM 15)) (termCode nil))) := rfl

/-- ⭐ La lista de código con los cerrados ya DOTADOS. -/
theorem prf_tc_nil : Prf (tcFn nil =eq termCode nil) := prf_tc_numeralM 0

/-- 🏁 **PILOTO**: la reflexión punteada de `premsOf` para el tag 15 (`thy`). -/
theorem pcc_premsOf_dot_thy [AnclaEq] (a : Term) :
    Prf (provFromCode (eqCodeFn
      (premsOfT (tcFn (cons a (cons (numeralM 15) nil)))) (tcFn nil))) := by
  let φ : Formula := premsOf (cons (.var 0) (cons (numeralM 15) nil)) =eq nil
  -- (1) el axioma CODIFICADO, instanciado con el testigo dotado
  have hax : Prf (provFromCode (substfc zero (tcFn a) (formCode φ))) :=
    pcc_axiom_inst φ (show ax_premsOf_thy ∈ axioms by simp [axioms]) (tcFn a)
      (prf_hasWit_tcFn (liftTerm 0 a))
  -- (2) abrir hacia el gemelo computable y casar por `rfl` (§meas_thy)
  have hopen : Prf (substfc zero (tcFn a) (formCode φ)
      =eq GT (termCode nil) (consT (tcFn a) (consT (termCode (numeralM 15)) (termCode nil)))) :=
    prf_substfc_arith_open 0 (tcFn a) φ
  -- (3) los CERRADOS, dotados — a nivel OBJETO
  have hdot : Prf (GT (termCode nil)
        (consT (tcFn a) (consT (termCode (numeralM 15)) (termCode nil)))
      =eq GT (tcFn nil) (consLT [a, numeralM 15])) := by
    refine prf_congr_eqCodeFn (prf_congr_premsOfT ?_) (prf_eq_symm prf_tc_nil)
    exact prf_congr_consT (prf_refl _)
      (prf_congr_consT (prf_eq_symm (prf_tc_numeralM 15)) (prf_eq_symm prf_tc_nil))
  have hbase : Prf (provFromCode (GT (tcFn nil) (consLT [a, numeralM 15]))) :=
    prf_mp (prf_provCode_congr (prf_eq_trans hopen hdot)) hax
  -- (4) el transporte en cascada
  exact pcc_rw_dot_consN (GT (tcFn nil))
    (GT_subst (tcFn nil) (substtc_inv_tcFn nil))
    (fun _ _ h => GT_congr (tcFn nil) h)
    (fun c hc => GT_wit (tcFn nil) (prf_hasWit_tcFn nil) c hc)
    [a, numeralM 15] hbase

/-! ## §5 · PLANTILLA aridad 2, RHS `nil` (efq, eqrefl, p3, ind, listInd) -/

theorem pcc_premsOf_dot_2nil [AnclaEq] (k : Nat) (a₀ a₁ : Term)
    (hmem : forall_2 (premsOf (cons (.var 1) (cons (numeralM k) (cons (.var 0) nil)))
      =eq nil) ∈ axioms)
    (hcode : ∀ W : Term,
      substCodeF 1 W (premsOf (cons (.var 1) (cons (numeralM k) (cons (.var 0) nil))) =eq nil)
        = GT (termCode nil) (consT W (consT (termCode (numeralM k))
            (consT (varc (numeral 0)) (termCode nil))))) :
    Prf (provFromCode (eqCodeFn
      (premsOfT (tcFn (cons a₀ (cons (numeralM k) (cons a₁ nil))))) (tcFn nil))) := by
  let φ : Formula := premsOf (cons (.var 1) (cons (numeralM k) (cons (.var 0) nil))) =eq nil
  let W₁ : Term := liftc zero (tcFn a₀)
  let W₂ : Term := tcFn a₁
  -- (1) el axioma CODIFICADO
  have hax : Prf (provFromCode (substfc zero W₂ (substfc (succ zero) W₁ (formCode φ)))) :=
    pcc_axiom_inst2 φ hmem (tcFn a₀) (tcFn a₁)
      (prf_hasWit_tcFn (liftTerm 0 a₀)) (prf_hasWit_tcFn (liftTerm 0 a₁))
  -- (2) el `substfc` INTERNO, abierto hacia el gemelo computable (casa por `rfl`)
  have hin : Prf (substfc (succ zero) W₁ (formCode φ)
      =eq GT (termCode nil) (consT W₁ (consT (termCode (numeralM k))
        (consT (varc (numeral 0)) (termCode nil))))) :=
    (hcode W₁) ▸ prf_substfc_arith_open 1 W₁ φ
  -- (3) el `liftc` del testigo COLAPSA
  have hA : Prf (W₁ =eq tcFn a₀) := prf_liftc_tcFn a₀
  have hnorm : Prf (GT (termCode nil) (consT W₁ (consT (termCode (numeralM k))
        (consT (varc (numeral 0)) (termCode nil))))
      =eq GT (termCode nil) (consT (tcFn a₀) (consT (termCode (numeralM k))
        (consT (varc (numeral 0)) (termCode nil))))) :=
    GT_congr _ (prf_congr_consT hA (prf_refl _))
  -- (4) el `substfc` EXTERNO, distribuido a mano sobre el código explícito
  have hout : Prf (substfc zero W₂ (GT (termCode nil) (consT (tcFn a₀)
        (consT (termCode (numeralM k)) (consT (varc (numeral 0)) (termCode nil)))))
      =eq GT (termCode nil) (consT (tcFn a₀) (consT (termCode (numeralM k))
        (consT W₂ (termCode nil))))) := by
    refine prf_eq_trans (GT_subst (termCode nil)
      (substtc_inv_termCode_numeralM 0) W₂ _) (GT_congr _ ?_)
    refine prf_eq_trans (prf_substtc_consT zero W₂ (tcFn a₀) _) ?_
    refine prf_congr_consT (prf_substtc_tcFn W₂ a₀) ?_
    refine prf_eq_trans (prf_substtc_consT zero W₂ (termCode (numeralM k)) _) ?_
    refine prf_congr_consT (substtc_inv_termCode_numeralM k W₂) ?_
    refine prf_eq_trans (prf_substtc_consT zero W₂ (varc (numeral 0)) (termCode nil)) ?_
    exact prf_congr_consT (prf_substtc_varc0 W₂) (substtc_inv_termCode_numeralM 0 W₂)
  -- (5) los CERRADOS, dotados
  have hdot : Prf (GT (termCode nil) (consT (tcFn a₀) (consT (termCode (numeralM k))
        (consT W₂ (termCode nil))))
      =eq GT (tcFn nil) (consLT [a₀, numeralM k, a₁])) := by
    refine prf_congr_eqCodeFn (prf_congr_premsOfT ?_) (prf_eq_symm prf_tc_nil)
    exact prf_congr_consT (prf_refl _)
      (prf_congr_consT (prf_eq_symm (prf_tc_numeralM k))
        (prf_congr_consT (prf_refl _) (prf_eq_symm prf_tc_nil)))
  have hbase : Prf (provFromCode (GT (tcFn nil) (consLT [a₀, numeralM k, a₁]))) :=
    prf_mp (prf_provCode_congr (prf_eq_trans
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout) hdot)) hax
  -- (6) el transporte en cascada
  exact pcc_rw_dot_consN (GT (tcFn nil))
    (GT_subst (tcFn nil) (substtc_inv_tcFn nil))
    (fun _ _ h => GT_congr (tcFn nil) h)
    (fun c hc => GT_wit (tcFn nil) (prf_hasWit_tcFn nil) c hc)
    [a₀, numeralM k, a₁] hbase

/-- Instancia: tag 8 (`efq`). -/
theorem pcc_premsOf_dot_efq [AnclaEq] (a₀ a₁ : Term) :
    Prf (provFromCode (eqCodeFn
      (premsOfT (tcFn (cons a₀ (cons (numeralM 8) (cons a₁ nil))))) (tcFn nil))) :=
  pcc_premsOf_dot_2nil 8 a₀ a₁ (show ax_premsOf_efq ∈ axioms by simp [axioms]) (fun _ => rfl)

/-! ## §6 · LEMAS A NIVEL ARBITRARIO (los externos de aridad ≥ 3) -/

/-- `substtc` no toca el código de un término CERRADO, a **cualquier** nivel. -/
theorem substtc_inv_tc_closed (v : Nat) (W t : Term) (h : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) := by
  have hh := prf_substtc_arith_open v W t
  rwa [substCodeT_closed v W t h] at hh

theorem liftTerm_numeralM (c : Nat) : ∀ k : Nat, liftTerm c (numeralM k) = numeralM k
  | 0     => rfl
  | k + 1 => by simp only [numeralM, succ, liftTerm, liftTerms, liftTerm_numeralM c k]

theorem substtc_inv_tc_numeralM (v k : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode (numeralM k)) =eq termCode (numeralM k)) :=
  substtc_inv_tc_closed v W (numeralM k) (fun c => liftTerm_numeralM c k)

/-- `GT` conmuta con `substfc` a **cualquier** nivel. -/
theorem GT_subst_at (v : Nat) (R : Term)
    (hR : ∀ W, Prf (substtc (numeral v) W R =eq R)) (s c : Term) :
    Prf (substfc (numeral v) s (GT R c) =eq GT R (substtc (numeral v) s c)) := by
  refine prf_eq_trans (prf_substfc_eq (numeral v) s (premsOfT c) R) ?_
  exact prf_congr_eqCodeFn (prf_substtc_premsOfT (numeral v) s c) (hR s)

/-- `varc j̄ ↦ testigo` cuando `j` es el nivel actuante. -/
theorem prf_substtc_varc_eq (v : Nat) (s : Term) :
    Prf (substtc (numeral v) s (varc (numeral v)) =eq s) :=
  prf_mp (prf_substtc_var_eq (numeral v) s (numeral v)) (prf_refl _)

/-- `varc j̄` sobrevive cuando `j < v`. -/
theorem prf_substtc_varc_lt {j v : Nat} (h : j < v) (s : Term) :
    Prf (substtc (numeral v) s (varc (numeral j)) =eq varc (numeral j)) :=
  prf_mp (prf_substtc_var_lt (numeral v) s (numeral j)) (prf_gnum_lt h)

/-! ## §7 · PLANTILLA aridad 3, RHS `nil` -/

theorem pcc_premsOf_dot_3nil [AnclaEq] (k : Nat) (a₀ a₁ a₂ : Term)
    (hmem : forall_3 (premsOf (cons (.var 2) (cons (numeralM k)
      (cons (.var 1) (cons (.var 0) nil)))) =eq nil) ∈ axioms)
    (hcode : ∀ W : Term,
      substCodeF 2 W (premsOf (cons (.var 2) (cons (numeralM k)
        (cons (.var 1) (cons (.var 0) nil)))) =eq nil)
        = GT (termCode nil) (consT W (consT (termCode (numeralM k))
            (consT (varc (numeral 1)) (consT (varc (numeral 0)) (termCode nil)))))) :
    Prf (provFromCode (eqCodeFn
      (premsOfT (tcFn (cons a₀ (cons (numeralM k) (cons a₁ (cons a₂ nil)))))) (tcFn nil))) := by
  let φ : Formula := premsOf (cons (.var 2) (cons (numeralM k)
    (cons (.var 1) (cons (.var 0) nil)))) =eq nil
  have hax : Prf (provFromCode (substfc zero (tcFn a₂)
      (substfc (succ zero) (liftc zero (tcFn a₁))
        (substfc (succ (succ zero)) (liftc zero (liftc zero (tcFn a₀))) (formCode φ))))) :=
    pcc_axiom_inst3 φ hmem (tcFn a₀) (tcFn a₁) (tcFn a₂)
      (prf_hasWit_tcFn (liftTerm 0 a₀)) (prf_hasWit_tcFn (liftTerm 0 a₁))
      (prf_hasWit_tcFn (liftTerm 0 a₂))
  -- (1) los `liftc` de los testigos COLAPSAN
  have hc1 : Prf (liftc zero (liftc zero (tcFn a₀)) =eq tcFn a₀) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn a₀)) (prf_liftc_tcFn a₀)
  have hc2 : Prf (liftc zero (tcFn a₁) =eq tcFn a₁) := prf_liftc_tcFn a₁
  -- (2) nivel 2: el gemelo computable
  have h2 : Prf (substfc (succ (succ zero)) (liftc zero (liftc zero (tcFn a₀))) (formCode φ)
      =eq GT (termCode nil) (consT (tcFn a₀) (consT (termCode (numeralM k))
        (consT (varc (numeral 1)) (consT (varc (numeral 0)) (termCode nil)))))) :=
    prf_eq_trans (prf_congr_substfc_arg2 hc1) ((hcode (tcFn a₀)) ▸
      prf_substfc_arith_open 2 (tcFn a₀) φ)
  -- (3) nivel 1
  have h1 : Prf (substfc (succ zero) (liftc zero (tcFn a₁))
        (GT (termCode nil) (consT (tcFn a₀) (consT (termCode (numeralM k))
          (consT (varc (numeral 1)) (consT (varc (numeral 0)) (termCode nil))))))
      =eq GT (termCode nil) (consT (tcFn a₀) (consT (termCode (numeralM k))
        (consT (tcFn a₁) (consT (varc (numeral 0)) (termCode nil)))))) := by
    refine prf_eq_trans (prf_congr_substfc_arg2 hc2) ?_
    refine prf_eq_trans (GT_subst_at 1 (termCode nil) (substtc_inv_tc_numeralM 1 0) _ _)
      (GT_congr _ ?_)
    refine prf_eq_trans (prf_substtc_consT (numeral 1) (tcFn a₁) _ _) ?_
    refine prf_congr_consT (prf_substtc_tcFn_at 1 (tcFn a₁) a₀) ?_
    refine prf_eq_trans (prf_substtc_consT (numeral 1) (tcFn a₁) _ _) ?_
    refine prf_congr_consT (substtc_inv_tc_numeralM 1 k (tcFn a₁)) ?_
    refine prf_eq_trans (prf_substtc_consT (numeral 1) (tcFn a₁) _ _) ?_
    refine prf_congr_consT (prf_substtc_varc_eq 1 (tcFn a₁)) ?_
    refine prf_eq_trans (prf_substtc_consT (numeral 1) (tcFn a₁) _ _) ?_
    exact prf_congr_consT (prf_substtc_varc_lt (by omega : 0 < 1) (tcFn a₁))
      (substtc_inv_tc_numeralM 1 0 (tcFn a₁))
  -- (4) nivel 0
  have h0 : Prf (substfc zero (tcFn a₂)
        (GT (termCode nil) (consT (tcFn a₀) (consT (termCode (numeralM k))
          (consT (tcFn a₁) (consT (varc (numeral 0)) (termCode nil))))))
      =eq GT (termCode nil) (consT (tcFn a₀) (consT (termCode (numeralM k))
        (consT (tcFn a₁) (consT (tcFn a₂) (termCode nil)))))) := by
    refine prf_eq_trans (GT_subst_at 0 (termCode nil) (substtc_inv_tc_numeralM 0 0) _ _)
      (GT_congr _ ?_)
    refine prf_eq_trans (prf_substtc_consT zero (tcFn a₂) _ _) ?_
    refine prf_congr_consT (prf_substtc_tcFn (tcFn a₂) a₀) ?_
    refine prf_eq_trans (prf_substtc_consT zero (tcFn a₂) _ _) ?_
    refine prf_congr_consT (substtc_inv_termCode_numeralM k (tcFn a₂)) ?_
    refine prf_eq_trans (prf_substtc_consT zero (tcFn a₂) _ _) ?_
    refine prf_congr_consT (prf_substtc_tcFn (tcFn a₂) a₁) ?_
    refine prf_eq_trans (prf_substtc_consT zero (tcFn a₂) _ _) ?_
    exact prf_congr_consT (prf_substtc_varc0 (tcFn a₂))
      (substtc_inv_termCode_numeralM 0 (tcFn a₂))
  -- (5) los CERRADOS, dotados
  have hdot : Prf (GT (termCode nil) (consT (tcFn a₀) (consT (termCode (numeralM k))
        (consT (tcFn a₁) (consT (tcFn a₂) (termCode nil)))))
      =eq GT (tcFn nil) (consLT [a₀, numeralM k, a₁, a₂])) := by
    refine prf_congr_eqCodeFn (prf_congr_premsOfT ?_) (prf_eq_symm prf_tc_nil)
    exact prf_congr_consT (prf_refl _)
      (prf_congr_consT (prf_eq_symm (prf_tc_numeralM k))
        (prf_congr_consT (prf_refl _)
          (prf_congr_consT (prf_refl _) (prf_eq_symm prf_tc_nil))))
  have hbase : Prf (provFromCode (GT (tcFn nil) (consLT [a₀, numeralM k, a₁, a₂]))) :=
    prf_mp (prf_provCode_congr (prf_eq_trans (prf_eq_trans (prf_eq_trans
      (prf_congr_substfc_arg3 (prf_congr_substfc_arg3 h2)) (prf_congr_substfc_arg3 h1)) h0)
      hdot)) hax
  exact pcc_rw_dot_consN (GT (tcFn nil))
    (GT_subst (tcFn nil) (substtc_inv_tcFn nil))
    (fun _ _ h => GT_congr (tcFn nil) h)
    (fun c hc => GT_wit (tcFn nil) (prf_hasWit_tcFn nil) c hc)
    [a₀, numeralM k, a₁, a₂] hbase

/-- Instancia: tag 0 (`p1`). -/
theorem pcc_premsOf_dot_p1 [AnclaEq] (a₀ a₁ a₂ : Term) :
    Prf (provFromCode (eqCodeFn
      (premsOfT (tcFn (cons a₀ (cons (numeralM 0) (cons a₁ (cons a₂ nil)))))) (tcFn nil))) :=
  pcc_premsOf_dot_3nil 0 a₀ a₁ a₂ (show ax_premsOf_p1 ∈ axioms by simp [axioms]) (fun _ => rfl)

/-! ## §8 · PLANTILLA aridad 4, RHS `nil` -/

theorem pcc_premsOf_dot_4nil [AnclaEq] (k : Nat) (a0 a1 a2 a3 : Term)
    (hmem : forall_4 (premsOf (cons (.var 3) (cons (numeralM k)
      (cons (.var 2) (cons (.var 1) (cons (.var 0) nil))))) =eq nil) ∈ axioms)
    (hcode : ∀ W : Term,
      substCodeF 3 W (premsOf (cons (.var 3) (cons (numeralM k)
        (cons (.var 2) (cons (.var 1) (cons (.var 0) nil))))) =eq nil)
        = GT (termCode nil) (consT W (consT (termCode (numeralM k))
            (consT (varc (numeral 2)) (consT (varc (numeral 1))
              (consT (varc (numeral 0)) (termCode nil))))))) :
    Prf (provFromCode (eqCodeFn (premsOfT (tcFn (cons a0 (cons (numeralM k)
      (cons a1 (cons a2 (cons a3 nil))))))) (tcFn nil))) := by
  let phi : Formula := premsOf (cons (.var 3) (cons (numeralM k)
    (cons (.var 2) (cons (.var 1) (cons (.var 0) nil))))) =eq nil
  have hax : Prf (provFromCode (substfc zero (tcFn a3)
      (substfc (numeral 1) (liftc zero (tcFn a2))
        (substfc (numeral 2) (liftc zero (liftc zero (tcFn a1)))
          (substfc (numeral 3) (liftc zero (liftc zero (liftc zero (tcFn a0))))
            (formCode phi)))))) :=
    pcc_axiom_inst4 phi hmem (tcFn a0) (tcFn a1) (tcFn a2) (tcFn a3)
      (prf_hasWit_tcFn (liftTerm 0 a0)) (prf_hasWit_tcFn (liftTerm 0 a1))
      (prf_hasWit_tcFn (liftTerm 0 a2)) (prf_hasWit_tcFn (liftTerm 0 a3))
  have hc1 : Prf (liftc zero (liftc zero (liftc zero (tcFn a0))) =eq tcFn a0) :=
    prf_eq_trans (prf_congr_liftc (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn a0))
      (prf_liftc_tcFn a0))) (prf_liftc_tcFn a0)
  have hc2 : Prf (liftc zero (liftc zero (tcFn a1)) =eq tcFn a1) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn a1)) (prf_liftc_tcFn a1)
  have hc3 : Prf (liftc zero (tcFn a2) =eq tcFn a2) := prf_liftc_tcFn a2
  -- nivel 3
  have h3 : Prf (substfc (numeral 3) (liftc zero (liftc zero (liftc zero (tcFn a0))))
        (formCode phi)
      =eq GT (termCode nil) (consT (tcFn a0) (consT (termCode (numeralM k))
        (consT (varc (numeral 2)) (consT (varc (numeral 1))
          (consT (varc (numeral 0)) (termCode nil))))))) :=
    prf_eq_trans (prf_congr_substfc_arg2 hc1)
      ((hcode (tcFn a0)) ▸ prf_substfc_arith_open 3 (tcFn a0) phi)
  -- nivel 2
  have h2 : Prf (substfc (numeral 2) (liftc zero (liftc zero (tcFn a1)))
        (GT (termCode nil) (consT (tcFn a0) (consT (termCode (numeralM k))
          (consT (varc (numeral 2)) (consT (varc (numeral 1))
            (consT (varc (numeral 0)) (termCode nil)))))))
      =eq GT (termCode nil) (consT (tcFn a0) (consT (termCode (numeralM k))
        (consT (tcFn a1) (consT (varc (numeral 1))
          (consT (varc (numeral 0)) (termCode nil))))))) := by
    refine prf_eq_trans (prf_congr_substfc_arg2 hc2) ?_
    refine prf_eq_trans (GT_subst_at 2 (termCode nil) (substtc_inv_tc_numeralM 2 0) _ _)
      (GT_congr _ ?_)
    refine prf_eq_trans (prf_substtc_consT (numeral 2) (tcFn a1) _ _) ?_
    refine prf_congr_consT (prf_substtc_tcFn_at 2 (tcFn a1) a0) ?_
    refine prf_eq_trans (prf_substtc_consT (numeral 2) (tcFn a1) _ _) ?_
    refine prf_congr_consT (substtc_inv_tc_numeralM 2 k (tcFn a1)) ?_
    refine prf_eq_trans (prf_substtc_consT (numeral 2) (tcFn a1) _ _) ?_
    refine prf_congr_consT (prf_substtc_varc_eq 2 (tcFn a1)) ?_
    refine prf_eq_trans (prf_substtc_consT (numeral 2) (tcFn a1) _ _) ?_
    refine prf_congr_consT (prf_substtc_varc_lt (by omega : 1 < 2) (tcFn a1)) ?_
    refine prf_eq_trans (prf_substtc_consT (numeral 2) (tcFn a1) _ _) ?_
    exact prf_congr_consT (prf_substtc_varc_lt (by omega : 0 < 2) (tcFn a1))
      (substtc_inv_tc_numeralM 2 0 (tcFn a1))
  -- nivel 1
  have h1 : Prf (substfc (numeral 1) (liftc zero (tcFn a2))
        (GT (termCode nil) (consT (tcFn a0) (consT (termCode (numeralM k))
          (consT (tcFn a1) (consT (varc (numeral 1))
            (consT (varc (numeral 0)) (termCode nil)))))))
      =eq GT (termCode nil) (consT (tcFn a0) (consT (termCode (numeralM k))
        (consT (tcFn a1) (consT (tcFn a2)
          (consT (varc (numeral 0)) (termCode nil))))))) := by
    refine prf_eq_trans (prf_congr_substfc_arg2 hc3) ?_
    refine prf_eq_trans (GT_subst_at 1 (termCode nil) (substtc_inv_tc_numeralM 1 0) _ _)
      (GT_congr _ ?_)
    refine prf_eq_trans (prf_substtc_consT (numeral 1) (tcFn a2) _ _) ?_
    refine prf_congr_consT (prf_substtc_tcFn_at 1 (tcFn a2) a0) ?_
    refine prf_eq_trans (prf_substtc_consT (numeral 1) (tcFn a2) _ _) ?_
    refine prf_congr_consT (substtc_inv_tc_numeralM 1 k (tcFn a2)) ?_
    refine prf_eq_trans (prf_substtc_consT (numeral 1) (tcFn a2) _ _) ?_
    refine prf_congr_consT (prf_substtc_tcFn_at 1 (tcFn a2) a1) ?_
    refine prf_eq_trans (prf_substtc_consT (numeral 1) (tcFn a2) _ _) ?_
    refine prf_congr_consT (prf_substtc_varc_eq 1 (tcFn a2)) ?_
    refine prf_eq_trans (prf_substtc_consT (numeral 1) (tcFn a2) _ _) ?_
    exact prf_congr_consT (prf_substtc_varc_lt (by omega : 0 < 1) (tcFn a2))
      (substtc_inv_tc_numeralM 1 0 (tcFn a2))
  -- nivel 0
  have h0 : Prf (substfc zero (tcFn a3)
        (GT (termCode nil) (consT (tcFn a0) (consT (termCode (numeralM k))
          (consT (tcFn a1) (consT (tcFn a2)
            (consT (varc (numeral 0)) (termCode nil)))))))
      =eq GT (termCode nil) (consT (tcFn a0) (consT (termCode (numeralM k))
        (consT (tcFn a1) (consT (tcFn a2) (consT (tcFn a3) (termCode nil))))))) := by
    refine prf_eq_trans (GT_subst_at 0 (termCode nil) (substtc_inv_tc_numeralM 0 0) _ _)
      (GT_congr _ ?_)
    refine prf_eq_trans (prf_substtc_consT zero (tcFn a3) _ _) ?_
    refine prf_congr_consT (prf_substtc_tcFn (tcFn a3) a0) ?_
    refine prf_eq_trans (prf_substtc_consT zero (tcFn a3) _ _) ?_
    refine prf_congr_consT (substtc_inv_termCode_numeralM k (tcFn a3)) ?_
    refine prf_eq_trans (prf_substtc_consT zero (tcFn a3) _ _) ?_
    refine prf_congr_consT (prf_substtc_tcFn (tcFn a3) a1) ?_
    refine prf_eq_trans (prf_substtc_consT zero (tcFn a3) _ _) ?_
    refine prf_congr_consT (prf_substtc_tcFn (tcFn a3) a2) ?_
    refine prf_eq_trans (prf_substtc_consT zero (tcFn a3) _ _) ?_
    exact prf_congr_consT (prf_substtc_varc0 (tcFn a3))
      (substtc_inv_termCode_numeralM 0 (tcFn a3))
  have hdot : Prf (GT (termCode nil) (consT (tcFn a0) (consT (termCode (numeralM k))
        (consT (tcFn a1) (consT (tcFn a2) (consT (tcFn a3) (termCode nil))))))
      =eq GT (tcFn nil) (consLT [a0, numeralM k, a1, a2, a3])) := by
    refine prf_congr_eqCodeFn (prf_congr_premsOfT ?_) (prf_eq_symm prf_tc_nil)
    exact prf_congr_consT (prf_refl _)
      (prf_congr_consT (prf_eq_symm (prf_tc_numeralM k))
        (prf_congr_consT (prf_refl _) (prf_congr_consT (prf_refl _)
          (prf_congr_consT (prf_refl _) (prf_eq_symm prf_tc_nil)))))
  have hbase : Prf (provFromCode (GT (tcFn nil) (consLT [a0, numeralM k, a1, a2, a3]))) :=
    prf_mp (prf_provCode_congr (prf_eq_trans (prf_eq_trans (prf_eq_trans (prf_eq_trans
      (prf_congr_substfc_arg3 (prf_congr_substfc_arg3 (prf_congr_substfc_arg3 h3)))
      (prf_congr_substfc_arg3 (prf_congr_substfc_arg3 h2)))
      (prf_congr_substfc_arg3 h1)) h0) hdot)) hax
  exact pcc_rw_dot_consN (GT (tcFn nil))
    (GT_subst (tcFn nil) (substtc_inv_tcFn nil))
    (fun _ _ h => GT_congr (tcFn nil) h)
    (fun c hc => GT_wit (tcFn nil) (prf_hasWit_tcFn nil) c hc)
    [a0, numeralM k, a1, a2, a3] hbase

/-- Instancia: tag 1 (`p2`). -/
theorem pcc_premsOf_dot_p2 [AnclaEq] (a0 a1 a2 a3 : Term) :
    Prf (provFromCode (eqCodeFn (premsOfT (tcFn (cons a0 (cons (numeralM 1)
      (cons a1 (cons a2 (cons a3 nil))))))) (tcFn nil))) :=
  pcc_premsOf_dot_4nil 1 a0 a1 a2 a3 (show ax_premsOf_p2 ∈ axioms by simp [axioms]) (fun _ => rfl)

/-! ## §9 · LOS DOS TAGS CON PREMISAS REALES: `gen` (17) y `mp` (16)

⚠️ Aquí el transporte en cascada hay que darlo **también en el lado derecho**, y en `mp`
**anidado**: su RHS es `⟨implc a₁ a₀, a₁⟩` y `implc X Y = ⟨5̄, X, Y⟩` es a su vez un `cons`. -/

theorem substtc_inv_premsOfT {X : Term} (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    ∀ W, Prf (substtc zero W (premsOfT X) =eq premsOfT X) :=
  fun W => prf_eq_trans (prf_substtc_premsOfT zero W X) (prf_congr_premsOfT (hX W))

/-- Contexto con el hueco en el lado DERECHO de la ecuación. -/
def GR (L : Term) (c : Term) : Term := eqCodeFn L c

theorem GR_subst (L : Term) (hL : ∀ W, Prf (substtc zero W L =eq L)) (s c : Term) :
    Prf (substfc zero s (GR L c) =eq GR L (substtc zero s c)) :=
  prf_eq_trans (prf_substfc_eq zero s L c) (prf_congr_eqCodeFn (hL s) (prf_refl _))

theorem GR_congr (L : Term) {c c' : Term} (h : Prf (c =eq c')) :
    Prf (GR L c =eq GR L c') := prf_congr_eqCodeFn (prf_refl _) h

theorem GR_wit (L : Term) (hL : Prf (hasWit L)) (c : Term) (hc : Prf (hasWit c)) :
    Prf (hasWitF (GR L c)) := prf_hasWitF_eq2 _ _ hL hc

/-- Contexto con el hueco en la CABEZA del lado derecho. -/
def GRH (L R : Term) (c : Term) : Term := eqCodeFn L (consT c R)

theorem GRH_subst (L R : Term) (hL : ∀ W, Prf (substtc zero W L =eq L))
    (hR : ∀ W, Prf (substtc zero W R =eq R)) (s c : Term) :
    Prf (substfc zero s (GRH L R c) =eq GRH L R (substtc zero s c)) := by
  refine prf_eq_trans (prf_substfc_eq zero s L (consT c R)) ?_
  refine prf_congr_eqCodeFn (hL s) ?_
  exact prf_eq_trans (prf_substtc_consT zero s c R) (prf_congr_consT (prf_refl _) (hR s))

theorem GRH_congr (L R : Term) {c c' : Term} (h : Prf (c =eq c')) :
    Prf (GRH L R c =eq GRH L R c') :=
  prf_congr_eqCodeFn (prf_refl _) (prf_congr_consT h (prf_refl _))

theorem GRH_wit (L R : Term) (hL : Prf (hasWit L)) (hR : Prf (hasWit R))
    (c : Term) (hc : Prf (hasWit c)) : Prf (hasWitF (GRH L R c)) :=
  prf_hasWitF_eq2 _ _ hL (prf_hasWit_consT hc hR)

/-! ### `gen` (17): `premsOf ⟨c, 17̄, b⟩ ≐ ⟨b⟩` -/

theorem pcc_premsOf_dot_gen [AnclaEq] (a0 a1 : Term) :
    Prf (provFromCode (eqCodeFn
      (premsOfT (tcFn (cons a0 (cons (numeralM 17) (cons a1 nil)))))
      (tcFn (cons a1 nil)))) := by
  let phi : Formula := premsOf (cons (.var 1) (cons (numeralM 17) (cons (.var 0) nil)))
    =eq cons (.var 0) nil
  let W1 : Term := liftc zero (tcFn a0)
  let W2 : Term := tcFn a1
  have hax : Prf (provFromCode (substfc zero W2 (substfc (succ zero) W1 (formCode phi)))) :=
    pcc_axiom_inst2 phi (show ax_premsOf_gen ∈ axioms by simp [axioms]) (tcFn a0) (tcFn a1)
      (prf_hasWit_tcFn (liftTerm 0 a0)) (prf_hasWit_tcFn (liftTerm 0 a1))
  have hin : Prf (substfc (succ zero) W1 (formCode phi)
      =eq eqCodeFn (premsOfT (consT W1 (consT (termCode (numeralM 17))
            (consT (varc (numeral 0)) (termCode nil)))))
          (consT (varc (numeral 0)) (termCode nil))) :=
    prf_substfc_arith_open 1 W1 phi
  have hnorm : Prf (eqCodeFn (premsOfT (consT W1 (consT (termCode (numeralM 17))
            (consT (varc (numeral 0)) (termCode nil)))))
          (consT (varc (numeral 0)) (termCode nil))
      =eq eqCodeFn (premsOfT (consT (tcFn a0) (consT (termCode (numeralM 17))
            (consT (varc (numeral 0)) (termCode nil)))))
          (consT (varc (numeral 0)) (termCode nil))) :=
    prf_congr_eqCodeFn (prf_congr_premsOfT
      (prf_congr_consT (prf_liftc_tcFn a0) (prf_refl _))) (prf_refl _)
  have hout : Prf (substfc zero W2
        (eqCodeFn (premsOfT (consT (tcFn a0) (consT (termCode (numeralM 17))
            (consT (varc (numeral 0)) (termCode nil)))))
          (consT (varc (numeral 0)) (termCode nil)))
      =eq eqCodeFn (premsOfT (consLT [a0, numeralM 17, a1])) (consLT [a1])) := by
    refine prf_eq_trans (prf_substfc_eq zero W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_premsOfT zero W2 _) (prf_congr_premsOfT ?_)
      refine prf_eq_trans (prf_substtc_consT zero W2 _ _) ?_
      refine prf_congr_consT (prf_substtc_tcFn W2 a0) ?_
      refine prf_eq_trans (prf_substtc_consT zero W2 _ _) ?_
      refine prf_congr_consT (prf_eq_trans (substtc_inv_termCode_numeralM 17 W2)
        (prf_eq_symm (prf_tc_numeralM 17))) ?_
      refine prf_eq_trans (prf_substtc_consT zero W2 _ _) ?_
      exact prf_congr_consT (prf_substtc_varc0 W2)
        (prf_eq_trans (substtc_inv_termCode_numeralM 0 W2) (prf_eq_symm prf_tc_nil))
    · refine prf_eq_trans (prf_substtc_consT zero W2 _ _) ?_
      exact prf_congr_consT (prf_substtc_varc0 W2)
        (prf_eq_trans (substtc_inv_termCode_numeralM 0 W2) (prf_eq_symm prf_tc_nil))
  have hbase : Prf (provFromCode
      (eqCodeFn (premsOfT (consLT [a0, numeralM 17, a1])) (consLT [a1]))) :=
    prf_mp (prf_provCode_congr (prf_eq_trans
      (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout)) hax
  -- transporte del LHS
  have hL : Prf (provFromCode
      (eqCodeFn (premsOfT (tcFn (consL [a0, numeralM 17, a1]))) (consLT [a1]))) :=
    pcc_rw_dot_consN (GT (consLT [a1]))
      (GT_subst (consLT [a1]) (substtc_inv_consNT [a1]))
      (fun _ _ h => GT_congr (consLT [a1]) h)
      (fun c hc => GT_wit (consLT [a1]) (prf_hasWit_consNT [a1]) c hc)
      [a0, numeralM 17, a1] hbase
  -- transporte del RHS
  exact pcc_rw_dot_consN (GR (premsOfT (tcFn (consL [a0, numeralM 17, a1]))))
    (GR_subst _ (substtc_inv_premsOfT (substtc_inv_tcFn _)))
    (fun _ _ h => GR_congr _ h)
    (fun c hc => GR_wit _ (prf_hasWit_premsOfT (prf_hasWit_tcFn _)) c hc)
    [a1] hL

/-! ### `mp` (16): `premsOf ⟨c, 16̄, a⟩ ≐ ⟨implc a c, a⟩` — el RHS ANIDADO -/

theorem pcc_premsOf_dot_mp [AnclaEq] (a0 a1 : Term) :
    Prf (provFromCode (eqCodeFn
      (premsOfT (tcFn (cons a0 (cons (numeralM 16) (cons a1 nil)))))
      (tcFn (cons (implc a1 a0) (cons a1 nil))))) := by
  let phi : Formula := premsOf (cons (.var 1) (cons (numeralM 16) (cons (.var 0) nil)))
    =eq cons (implc (.var 0) (.var 1)) (cons (.var 0) nil)
  let W1 : Term := liftc zero (tcFn a0)
  let W2 : Term := tcFn a1
  have hax : Prf (provFromCode (substfc zero W2 (substfc (succ zero) W1 (formCode phi)))) :=
    pcc_axiom_inst2 phi (show ax_premsOf_mp ∈ axioms by simp [axioms]) (tcFn a0) (tcFn a1)
      (prf_hasWit_tcFn (liftTerm 0 a0)) (prf_hasWit_tcFn (liftTerm 0 a1))
  have hin : Prf (substfc (succ zero) W1 (formCode phi)
      =eq eqCodeFn (premsOfT (consT W1 (consT (termCode (numeralM 16))
            (consT (varc (numeral 0)) (termCode nil)))))
          (consT (consT (termCode (numeralM 5)) (consT (varc (numeral 0))
            (consT W1 (termCode nil))))
           (consT (varc (numeral 0)) (termCode nil)))) :=
    prf_substfc_arith_open 1 W1 phi
  have hnorm : Prf (eqCodeFn (premsOfT (consT W1 (consT (termCode (numeralM 16))
            (consT (varc (numeral 0)) (termCode nil)))))
          (consT (consT (termCode (numeralM 5)) (consT (varc (numeral 0))
            (consT W1 (termCode nil))))
           (consT (varc (numeral 0)) (termCode nil)))
      =eq eqCodeFn (premsOfT (consT (tcFn a0) (consT (termCode (numeralM 16))
            (consT (varc (numeral 0)) (termCode nil)))))
          (consT (consT (termCode (numeralM 5)) (consT (varc (numeral 0))
            (consT (tcFn a0) (termCode nil))))
           (consT (varc (numeral 0)) (termCode nil)))) :=
    prf_congr_eqCodeFn
      (prf_congr_premsOfT (prf_congr_consT (prf_liftc_tcFn a0) (prf_refl _)))
      (prf_congr_consT (prf_congr_consT (prf_refl _)
        (prf_congr_consT (prf_refl _)
          (prf_congr_consT (prf_liftc_tcFn a0) (prf_refl _)))) (prf_refl _))
  have hout : Prf (substfc zero W2
        (eqCodeFn (premsOfT (consT (tcFn a0) (consT (termCode (numeralM 16))
            (consT (varc (numeral 0)) (termCode nil)))))
          (consT (consT (termCode (numeralM 5)) (consT (varc (numeral 0))
            (consT (tcFn a0) (termCode nil))))
           (consT (varc (numeral 0)) (termCode nil))))
      =eq eqCodeFn (premsOfT (consLT [a0, numeralM 16, a1]))
          (consT (consLT [numeralM 5, a1, a0]) (consLT [a1]))) := by
    refine prf_eq_trans (prf_substfc_eq zero W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_premsOfT zero W2 _) (prf_congr_premsOfT ?_)
      refine prf_eq_trans (prf_substtc_consT zero W2 _ _) ?_
      refine prf_congr_consT (prf_substtc_tcFn W2 a0) ?_
      refine prf_eq_trans (prf_substtc_consT zero W2 _ _) ?_
      refine prf_congr_consT (prf_eq_trans (substtc_inv_termCode_numeralM 16 W2)
        (prf_eq_symm (prf_tc_numeralM 16))) ?_
      refine prf_eq_trans (prf_substtc_consT zero W2 _ _) ?_
      exact prf_congr_consT (prf_substtc_varc0 W2)
        (prf_eq_trans (substtc_inv_termCode_numeralM 0 W2) (prf_eq_symm prf_tc_nil))
    · refine prf_eq_trans (prf_substtc_consT zero W2 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · refine prf_eq_trans (prf_substtc_consT zero W2 _ _) ?_
        refine prf_congr_consT (prf_eq_trans (substtc_inv_termCode_numeralM 5 W2)
          (prf_eq_symm (prf_tc_numeralM 5))) ?_
        refine prf_eq_trans (prf_substtc_consT zero W2 _ _) ?_
        refine prf_congr_consT (prf_substtc_varc0 W2) ?_
        refine prf_eq_trans (prf_substtc_consT zero W2 _ _) ?_
        exact prf_congr_consT (prf_substtc_tcFn W2 a0)
          (prf_eq_trans (substtc_inv_termCode_numeralM 0 W2) (prf_eq_symm prf_tc_nil))
      · refine prf_eq_trans (prf_substtc_consT zero W2 _ _) ?_
        exact prf_congr_consT (prf_substtc_varc0 W2)
          (prf_eq_trans (substtc_inv_termCode_numeralM 0 W2) (prf_eq_symm prf_tc_nil))
  have hbase : Prf (provFromCode (eqCodeFn (premsOfT (consLT [a0, numeralM 16, a1]))
      (consT (consLT [numeralM 5, a1, a0]) (consLT [a1])))) :=
    prf_mp (prf_provCode_congr (prf_eq_trans
      (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout)) hax
  -- (1) transporte del LHS
  have hL : Prf (provFromCode (eqCodeFn (premsOfT (tcFn (consL [a0, numeralM 16, a1])))
      (consT (consLT [numeralM 5, a1, a0]) (consLT [a1])))) :=
    pcc_rw_dot_consN (GT (consT (consLT [numeralM 5, a1, a0]) (consLT [a1])))
      (GT_subst _ (fun W => prf_eq_trans (prf_substtc_consT zero W _ _)
        (prf_congr_consT (substtc_inv_consNT [numeralM 5, a1, a0] W)
          (substtc_inv_consNT [a1] W))))
      (fun _ _ h => GT_congr _ h)
      (fun c hc => GT_wit _ (prf_hasWit_consT (prf_hasWit_consNT [numeralM 5, a1, a0])
        (prf_hasWit_consNT [a1])) c hc)
      [a0, numeralM 16, a1] hbase
  -- (2) transporte del `implc` (la CABEZA del RHS)
  have hH : Prf (provFromCode (eqCodeFn (premsOfT (tcFn (consL [a0, numeralM 16, a1])))
      (consT (tcFn (consL [numeralM 5, a1, a0])) (consLT [a1])))) :=
    pcc_rw_dot_consN (GRH (premsOfT (tcFn (consL [a0, numeralM 16, a1]))) (consLT [a1]))
      (GRH_subst _ _ (substtc_inv_premsOfT (substtc_inv_tcFn _)) (substtc_inv_consNT [a1]))
      (fun _ _ h => GRH_congr _ _ h)
      (fun c hc => GRH_wit _ _ (prf_hasWit_premsOfT (prf_hasWit_tcFn _))
        (prf_hasWit_consNT [a1]) c hc)
      [numeralM 5, a1, a0] hL
  -- (3) transporte del RHS entero
  exact pcc_rw_dot_consN (GR (premsOfT (tcFn (consL [a0, numeralM 16, a1]))))
    (GR_subst _ (substtc_inv_premsOfT (substtc_inv_tcFn _)))
    (fun _ _ h => GR_congr _ h)
    (fun c hc => GR_wit _ (prf_hasWit_premsOfT (prf_hasWit_tcFn _)) c hc)
    [implc a1 a0, a1] hH


/-! ## §10 · EL ENSAMBLAJE POR TAG

Tres piezas se juntan aquí, y **sólo la tercera vive dentro de `Prov`**:

* la **η** (`prf_eta_of_tag`, nivel objeto) — `t ≐ etaTag t m k`;
* el **valor** (`prf_premsOf_*`, nivel objeto) — `premsOf t ≐ R`;
* la **reflexión punteada de la forma explícita** (§4–§9) — `Prov(premsOfT (etaTag …)˙ ≐ Ṙ)`.

⭐ El puente entre las dos primeras y la tercera es **congruencia OBJETO pura**: `ṫ ≐ (etaTag …)˙`
y `(premsOf t)˙ ≐ Ṙ` salen de `PrfH_congr_tcFn`. No hay ningún salto de moneda aquí — el salto ya
lo pagó §4–§9. -/

theorem PrfH_congr_premsOfT {Γ : List Formula} {x y : Term} (h : PrfH Γ (x =eq y)) :
    PrfH Γ (premsOfT x =eq premsOfT y) :=
  PrfH_congr_funcc2 (PrfH_congr_cons_head h)

/-- ⭐⭐ **EL ENSAMBLAJE, genérico en el tag.** -/
theorem pcc_eval_premsOf_of_tag {k m : Nat} {D : Formula} (t R : Term)
    (hax : Prf (Formula.forall (Formula.impl (tagF k) (lwfVar ⇔ D))))
    (hD : Prf (substFormula 0 t D ⇒ (lenc t =eq numeralM (m + 2))))
    (hobj : Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k) ⇒ (premsOf t =eq R))))
    (hdot : Prf (provFromCode (eqCodeFn (premsOfT (tcFn (etaTag t m k))) (tcFn R)))) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) := by
  refine prf_deduction (deduction_aux ?_ (nthc t (succ zero) =eq numeralM k) [lineWF t] rfl)
  have hlw : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t] (lineWF t) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have htagH : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t]
      (nthc t (succ zero) =eq numeralM k) := PrfH.hyp _ _ (List.Mem.head _)
  have ht : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t] (t =eq etaTag t m k) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_eta_of_tag t hax hD) _) hlw) htagH
  have hR : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t] (premsOf t =eq R) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hobj _) hlw) htagH
  have hbr : PrfH [nthc t (succ zero) =eq numeralM k, lineWF t]
      (eqCodeFn (premsOfT (tcFn (etaTag t m k))) (tcFn R)
        =eq eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))) :=
    PrfH_congr_eqCodeFn (PrfH_congr_premsOfT (PrfH_congr_tcFn (PrfH_eq_symm ht)))
      (PrfH_congr_tcFn (PrfH_eq_symm hR))
  exact PrfH_provCode_congr hbr (prf_to_prfH hdot _)

/-- Envoltorio para los **veinte** tags cuyo bicondicional lleva condición estructural. -/
theorem pcc_eval_premsOf_tag_and {k m : Nat} {C : Formula} (t R : Term)
    (hax : Prf (Formula.forall (Formula.impl (tagF k)
      (lwfVar ⇔ Formula.and (lencF (m + 2)) C))))
    (hobj : Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k) ⇒ (premsOf t =eq R))))
    (hdot : Prf (provFromCode (eqCodeFn (premsOfT (tcFn (etaTag t m k))) (tcFn R)))) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_of_tag t R hax
    (by
      have hsub : substFormula 0 t (Formula.and (lencF (m + 2)) C)
          = Formula.and (lenc t =eq numeralM (m + 2)) (substFormula 0 t C) := by
        simp only [substFormula, substFormula_lencF]
      rw [hsub]
      exact prf_deduction (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) (prfH_hyp_self _)))
    hobj hdot

/-- Envoltorio para `mp` (16), el **único** sin condición estructural. -/
theorem pcc_eval_premsOf_tag_plain {k m : Nat} (t R : Term)
    (hax : Prf (Formula.forall (Formula.impl (tagF k) (lwfVar ⇔ lencF (m + 2)))))
    (hobj : Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k) ⇒ (premsOf t =eq R))))
    (hdot : Prf (provFromCode (eqCodeFn (premsOfT (tcFn (etaTag t m k))) (tcFn R)))) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM k) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_of_tag t R hax
    (by rw [substFormula_lencF]; exact prf_deduction (prfH_hyp_self _)) hobj hdot

/-! ## §11 · LAS 21 RAMAS -/

/-- Tag 0 (`p1`). -/
theorem pcc_eval_premsOf_p1 [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 0) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 0) (m := 2) t (nil)
    (prf_ax (show ax_lineWF_p1 ∈ axioms by simp [axioms]))
    (prf_premsOf_p1 t)
    (pcc_premsOf_dot_3nil 0 (carc t) (carc (cdrc (cdrc t))) (carc (cdrc (cdrc (cdrc t))))
      (show ax_premsOf_p1 ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 1 (`p2`). -/
theorem pcc_eval_premsOf_p2 [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 1) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 1) (m := 3) t (nil)
    (prf_ax (show ax_lineWF_p2 ∈ axioms by simp [axioms]))
    (prf_premsOf_p2 t)
    (pcc_premsOf_dot_4nil 1 (carc t) (carc (cdrc (cdrc t))) (carc (cdrc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc (cdrc t)))))
      (show ax_premsOf_p2 ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 2 (`c1`). -/
theorem pcc_eval_premsOf_c1 [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 2) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 2) (m := 2) t (nil)
    (prf_ax (show ax_lineWF_c1 ∈ axioms by simp [axioms]))
    (prf_premsOf_c1 t)
    (pcc_premsOf_dot_3nil 2 (carc t) (carc (cdrc (cdrc t))) (carc (cdrc (cdrc (cdrc t))))
      (show ax_premsOf_c1 ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 3 (`c2`). -/
theorem pcc_eval_premsOf_c2 [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 3) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 3) (m := 2) t (nil)
    (prf_ax (show ax_lineWF_c2 ∈ axioms by simp [axioms]))
    (prf_premsOf_c2 t)
    (pcc_premsOf_dot_3nil 3 (carc t) (carc (cdrc (cdrc t))) (carc (cdrc (cdrc (cdrc t))))
      (show ax_premsOf_c2 ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 4 (`c3`). -/
theorem pcc_eval_premsOf_c3 [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 4) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 4) (m := 2) t (nil)
    (prf_ax (show ax_lineWF_c3 ∈ axioms by simp [axioms]))
    (prf_premsOf_c3 t)
    (pcc_premsOf_dot_3nil 4 (carc t) (carc (cdrc (cdrc t))) (carc (cdrc (cdrc (cdrc t))))
      (show ax_premsOf_c3 ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 5 (`j1`). -/
theorem pcc_eval_premsOf_j1 [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 5) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 5) (m := 2) t (nil)
    (prf_ax (show ax_lineWF_j1 ∈ axioms by simp [axioms]))
    (prf_premsOf_j1 t)
    (pcc_premsOf_dot_3nil 5 (carc t) (carc (cdrc (cdrc t))) (carc (cdrc (cdrc (cdrc t))))
      (show ax_premsOf_j1 ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 6 (`j2`). -/
theorem pcc_eval_premsOf_j2 [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 6) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 6) (m := 2) t (nil)
    (prf_ax (show ax_lineWF_j2 ∈ axioms by simp [axioms]))
    (prf_premsOf_j2 t)
    (pcc_premsOf_dot_3nil 6 (carc t) (carc (cdrc (cdrc t))) (carc (cdrc (cdrc (cdrc t))))
      (show ax_premsOf_j2 ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 7 (`j3`). -/
theorem pcc_eval_premsOf_j3 [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 7) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 7) (m := 3) t (nil)
    (prf_ax (show ax_lineWF_j3 ∈ axioms by simp [axioms]))
    (prf_premsOf_j3 t)
    (pcc_premsOf_dot_4nil 7 (carc t) (carc (cdrc (cdrc t))) (carc (cdrc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc (cdrc t)))))
      (show ax_premsOf_j3 ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 8 (`efq`). -/
theorem pcc_eval_premsOf_efq [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 8) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 8) (m := 1) t (nil)
    (prf_ax (show ax_lineWF_efq ∈ axioms by simp [axioms]))
    (prf_premsOf_efq t)
    (pcc_premsOf_dot_2nil 8 (carc t) (carc (cdrc (cdrc t)))
      (show ax_premsOf_efq ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 9 (`q1`). -/
theorem pcc_eval_premsOf_q1 [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 9) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 9) (m := 2) t (nil)
    (prf_ax (show ax_lineWF_q1 ∈ axioms by simp [axioms]))
    (prf_premsOf_q1 t)
    (pcc_premsOf_dot_3nil 9 (carc t) (carc (cdrc (cdrc t))) (carc (cdrc (cdrc (cdrc t))))
      (show ax_premsOf_q1 ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 10 (`q2`). -/
theorem pcc_eval_premsOf_q2 [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 10) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 10) (m := 2) t (nil)
    (prf_ax (show ax_lineWF_q2 ∈ axioms by simp [axioms]))
    (prf_premsOf_q2 t)
    (pcc_premsOf_dot_3nil 10 (carc t) (carc (cdrc (cdrc t))) (carc (cdrc (cdrc (cdrc t))))
      (show ax_premsOf_q2 ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 11 (`q3`). -/
theorem pcc_eval_premsOf_q3 [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 11) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 11) (m := 2) t (nil)
    (prf_ax (show ax_lineWF_q3 ∈ axioms by simp [axioms]))
    (prf_premsOf_q3 t)
    (pcc_premsOf_dot_3nil 11 (carc t) (carc (cdrc (cdrc t))) (carc (cdrc (cdrc (cdrc t))))
      (show ax_premsOf_q3 ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 12 (`eqrefl`). -/
theorem pcc_eval_premsOf_eqrefl [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 12) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 12) (m := 1) t (nil)
    (prf_ax (show ax_lineWF_eqrefl ∈ axioms by simp [axioms]))
    (prf_premsOf_eqrefl t)
    (pcc_premsOf_dot_2nil 12 (carc t) (carc (cdrc (cdrc t)))
      (show ax_premsOf_eqrefl ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 13 (`leibniz`). -/
theorem pcc_eval_premsOf_leibniz [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 13) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 13) (m := 3) t (nil)
    (prf_ax (show ax_lineWF_leibniz ∈ axioms by simp [axioms]))
    (prf_premsOf_leibniz t)
    (pcc_premsOf_dot_4nil 13 (carc t) (carc (cdrc (cdrc t))) (carc (cdrc (cdrc (cdrc t)))) (carc (cdrc (cdrc (cdrc (cdrc t)))))
      (show ax_premsOf_leibniz ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 14 (`p3`). -/
theorem pcc_eval_premsOf_p3 [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 14) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 14) (m := 1) t (nil)
    (prf_ax (show ax_lineWF_p3 ∈ axioms by simp [axioms]))
    (prf_premsOf_p3 t)
    (pcc_premsOf_dot_2nil 14 (carc t) (carc (cdrc (cdrc t)))
      (show ax_premsOf_p3 ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 15 (`thy`). -/
theorem pcc_eval_premsOf_thy [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 15) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 15) (m := 0) t (nil)
    (prf_ax (show ax_lineWF_thy ∈ axioms by simp [axioms]))
    (prf_premsOf_thy t)
    (pcc_premsOf_dot_thy (carc t))

/-- Tag 16 (`mp`). -/
theorem pcc_eval_premsOf_mp [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 16) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_plain (k := 16) (m := 1) t (cons (implc (carc (cdrc (cdrc t))) (carc t)) (cons (carc (cdrc (cdrc t))) nil))
    (prf_ax (show ax_lineWF_mp ∈ axioms by simp [axioms]))
    (prf_premsOf_mp t)
    (pcc_premsOf_dot_mp (carc t) (carc (cdrc (cdrc t))))

/-- Tag 17 (`gen`). -/
theorem pcc_eval_premsOf_gen [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 17) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 17) (m := 1) t (cons (carc (cdrc (cdrc t))) nil)
    (prf_ax (show ax_lineWF_gen ∈ axioms by simp [axioms]))
    (prf_premsOf_gen t)
    (pcc_premsOf_dot_gen (carc t) (carc (cdrc (cdrc t))))

/-- Tag 18 (`ind`). -/
theorem pcc_eval_premsOf_ind [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 18) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 18) (m := 1) t (nil)
    (prf_ax (show ax_lineWF_ind ∈ axioms by simp [axioms]))
    (prf_premsOf_ind t)
    (pcc_premsOf_dot_2nil 18 (carc t) (carc (cdrc (cdrc t)))
      (show ax_premsOf_ind ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 19 (`qconf`). -/
theorem pcc_eval_premsOf_qconf [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 19) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 19) (m := 2) t (nil)
    (prf_ax (show ax_lineWF_qconf ∈ axioms by simp [axioms]))
    (prf_premsOf_qconf t)
    (pcc_premsOf_dot_3nil 19 (carc t) (carc (cdrc (cdrc t))) (carc (cdrc (cdrc (cdrc t))))
      (show ax_premsOf_qconf ∈ axioms by simp [axioms]) (fun _ => rfl))

/-- Tag 20 (`listInd`). -/
theorem pcc_eval_premsOf_listInd [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 20) ⇒
      provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t))))) :=
  pcc_eval_premsOf_tag_and (k := 20) (m := 1) t (nil)
    (prf_ax (show ax_lineWF_listInd ∈ axioms by simp [axioms]))
    (prf_premsOf_listInd t)
    (pcc_premsOf_dot_2nil 20 (carc t) (carc (cdrc (cdrc t)))
      (show ax_premsOf_listInd ∈ axioms by simp [axioms]) (fun _ => rfl))

/-! ## §12 · 🏁 `pcc_eval_premsOf` — SIN CONOCER EL TAG

La inversión (`prf_lineWF_inv`) entrega el tag y `pcc_tag_vacuous` (§11ter de `SubstTreeReflect`)
cierra la cola `k ≥ 21`. ⭐ El enunciado **no menciona ni el tag ni el valor**: `tcFn (premsOf t)`
es uniforme, y por eso el ensamblador por ramas se le puede aplicar tal cual. -/

/-- 🏁🏁 **B1 · `premsOf`, REFLEJADO DENTRO DE `Prov`**, con `t` abstracto y sólo `lineWF t` de
    guarda. Es el eslabón que le faltaba a la cota de `hbody`(b). -/
theorem pcc_eval_premsOf [AnclaEq] (t : Term) :
    Prf (lineWF t ⇒ provFromCode (eqCodeFn (premsOfT (tcFn t)) (tcFn (premsOf t)))) := by
  refine prf_of_premsOf_branches t _ (fun k => ?_)
  match k with
  | 0  => exact pcc_eval_premsOf_p1 t
  | 1  => exact pcc_eval_premsOf_p2 t
  | 2  => exact pcc_eval_premsOf_c1 t
  | 3  => exact pcc_eval_premsOf_c2 t
  | 4  => exact pcc_eval_premsOf_c3 t
  | 5  => exact pcc_eval_premsOf_j1 t
  | 6  => exact pcc_eval_premsOf_j2 t
  | 7  => exact pcc_eval_premsOf_j3 t
  | 8  => exact pcc_eval_premsOf_efq t
  | 9  => exact pcc_eval_premsOf_q1 t
  | 10 => exact pcc_eval_premsOf_q2 t
  | 11 => exact pcc_eval_premsOf_q3 t
  | 12 => exact pcc_eval_premsOf_eqrefl t
  | 13 => exact pcc_eval_premsOf_leibniz t
  | 14 => exact pcc_eval_premsOf_p3 t
  | 15 => exact pcc_eval_premsOf_thy t
  | 16 => exact pcc_eval_premsOf_mp t
  | 17 => exact pcc_eval_premsOf_gen t
  | 18 => exact pcc_eval_premsOf_ind t
  | 19 => exact pcc_eval_premsOf_qconf t
  | 20 => exact pcc_eval_premsOf_listInd t
  | n + 21 => exact pcc_tag_vacuous t _ (by omega)

end ROBINSON_PlusPlus.Meta.PremsOfDotPrf

/-! ## `export` — por CONSUMO

Consumidor previsto: **B2**, el puente de la cota de `hbody`(b) dentro de `Prov`, que encadena
`pcc_eval_nthc` → `pcc_eval_premsOf` → `pcc_eval_lenc`. -/
export ROBINSON_PlusPlus.Meta.PremsOfDotPrf (
  premsOfT premsOfT_termCode substCodeT_premsOf
  prf_hasWit_premsOfT prf_congr_premsOfT prf_substtc_premsOfT substtc_inv_premsOfT
  consL consLT prf_hasWit_consNT substtc_inv_consNT pcc_rw_dot_consN
  GT GT_subst GT_subst_at GT_congr GT_wit GR GR_subst GR_congr GR_wit
  GRH GRH_subst GRH_congr GRH_wit
  substtc_inv_tc_closed liftTerm_numeralM substtc_inv_tc_numeralM
  prf_substtc_varc_eq prf_substtc_varc_lt prf_tc_nil
  pcc_premsOf_dot_thy pcc_premsOf_dot_2nil pcc_premsOf_dot_3nil pcc_premsOf_dot_4nil
  pcc_premsOf_dot_gen pcc_premsOf_dot_mp
  PrfH_congr_premsOfT pcc_eval_premsOf_of_tag
  pcc_eval_premsOf_tag_and pcc_eval_premsOf_tag_plain
  pcc_eval_premsOf
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.PremsOfDotPrf.pcc_rw_dot_consN
#print axioms ROBINSON_PlusPlus.Meta.PremsOfDotPrf.pcc_premsOf_dot_mp
#print axioms ROBINSON_PlusPlus.Meta.PremsOfDotPrf.pcc_eval_premsOf
