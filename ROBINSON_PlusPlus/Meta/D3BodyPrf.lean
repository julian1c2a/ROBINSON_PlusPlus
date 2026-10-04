/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.D3ChainDotPrf
import ROBINSON_PlusPlus.Meta.SubstTreeReflect
import ROBINSON_PlusPlus.Meta.PremsOfDotPrf

/-!
# D3 · el CUERPO del chasis, mitad (a) — la reflexión de `lineWF`

`Meta/D3ChainDotPrf.lean` §13 partió el `hbody` de `pcc_bdAll_intro` en sus dos mitades. Ésta es
la **(a)**: la reflexión del átomo `lineWF`, que quedó desbloqueada el 2026‑09‑10 al cerrarse los
**siete** reflectores de sustitución (`Meta/SubstTreeReflect.lean` §10bis, con
`prf_hasWitF_liftfc`).

⚠️ **Módulo aparte, y a propósito**: junta `D3ChainDotPrf` (que fija el destino) con
`SubstTreeReflect` (que prueba el reflector), y ninguno de los dos importa al otro. Meterlo en
cualquiera de ellos crearía una dependencia que hoy no existe.

## Las tres cosas que pasan aquí

1. **`chainOk → chainOkB`** y `∀`‑elim en `i`: de la cadena válida sale `lineWF (nthc q i)`.
2. **El reflector**, `pcc_lineWF_tracked_modulo_other`, que da `Prov(⌜lineWF (nthc q i)⌝)` con el
   código en forma de **reflexión pura** `(nthc q i)˙`.
3. ⚠️ **La MONEDA** (§3.55.2 otra vez): el destino pide el **ACCESOR dotado** `nthcT q̇ i̇`, no la
   reflexión pura. El salto lo paga `pcc_eval_nthc` **dentro de `Prov`**, con el Leibniz
   codificado; y el `liftc` que el binder impone **colapsa** (`prf_liftc_tcFn`).

**Footprint**: la base sancionada.
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.LineWFSchemaPrf ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
open ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
open ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.SubstTreeReflect
open ROBINSON_PlusPlus.Meta.D3ChainDotPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.PremsOfTagPrf
open ROBINSON_PlusPlus.Meta.PremsOfDotPrf

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

namespace ROBINSON_PlusPlus.Meta.D3BodyPrf


/-- El hueco de `lineWFCodeFn`, como pide `pcc_rw_imp`. -/
theorem hG_lineWF (s : Term) :
    Prf (substfc zero s (lineWFCodeFn (varc (numeral 0))) =eq lineWFCodeFn s) := by
  unfold lineWFCodeFn atom1CodeFn
  refine prf_eq_trans (prf_substfc_atom zero s (strCode "lineWF")
    (cons (varc (numeral 0)) nil)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  exact prf_eq_trans (prf_substtsc_cons zero s (varc (numeral 0)) nil)
    (prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0 s))
      (prf_congr_cons_tail (prf_substtsc_nil zero s)))

theorem hwG_lineWF : Prf (hasWitF (lineWFCodeFn (varc (numeral 0)))) :=
  prf_hasWitF_atom1 (strCode "lineWF") (varc (numeral 0)) (prf_hasWit_varc (numeral 0))

/-- ⭐ **De la cadena sale la buena-formación de la línea `i`-ésima.** Es el `∀`-elim en `i`
    del `chainOkB`, y lo consumen **las dos** mitades de `hbody`: (a) para reflejar `lineWF`, y (b)
    porque `premsOf` **sólo se evalúa sabiendo el tag**, y el tag lo da `lineWF`. -/
theorem prf_lineWF_of_chainOk (q i : Term) :
    Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒ lineWF (nthc q i))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [chainOk nil q] rfl)
  have hch : PrfH [lt i (lenc q), chainOk nil q] (chainOk nil q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [lt i (lenc q), chainOk nil q] (lt i (lenc q)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  -- (1) `chainOk → chainOkB`, y la línea `i` es buena
  have hB : PrfH [lt i (lenc q), chainOk nil q] (chainOkB nil q) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_chainOk_iff_chainOkB nil q)) _) hch
  have hB' : PrfH [lt i (lenc q), chainOk nil q]
      (Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
        (lineOkB (liftTerm 0 nil) (liftTerm 0 q) (.var 0)))) := hB
  have hspec := PrfH_spec hB' i
  have heq : substFormula 0 i (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
      (lineOkB (liftTerm 0 nil) (liftTerm 0 q) (.var 0)))
      = Formula.impl (lt i (lenc q)) (lineOkB nil q i) := by
    simp only [substFormula, substFormula_lineOkB, lt, lenc, nil, zero, substTerm, substTerms,
      FOL.substTerm_liftTerm, if_true]
  rw [heq] at hspec
  exact PrfH_and_elim_left (PrfH.mp _ _ _ hspec hlt)

/-- ⭐ **`hbody`(a) de D3**: la reflexión del átomo `lineWF`, ya instanciada en el cuerpo. -/
theorem hA_lineWFDotAt (q i : Term) :
    Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒ provFromCode (lineWFDotAt q i))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [chainOk nil q] rfl)
  have hch : PrfH [lt i (lenc q), chainOk nil q] (chainOk nil q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [lt i (lenc q), chainOk nil q] (lt i (lenc q)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  -- (1) la línea `i` es buena — el `∀`-elim, factorizado arriba
  have hline : PrfH [lt i (lenc q), chainOk nil q] (lineWF (nthc q i)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_lineWF_of_chainOk q i) _) hch) hlt
  -- (2) el reflector de `lineWF`, ya cerrado para los SIETE tags
  have hprov : PrfH [lt i (lenc q), chainOk nil q]
      (provFromCode (lineWFCodeFn (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH
      (pcc_lineWF_tracked (nthc q i)) _) hline
  -- (3) la MONEDA: el destino pide el ACCESOR dotado, no la reflexión pura
  have hev : PrfH [lt i (lenc q), chainOk nil q]
      (provFromCode (eqc (nthcT (tcFn q) (tcFn i)) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc q i) _) hlt
  have hsym : PrfH [lt i (lenc q), chainOk nil q]
      (provFromCode (eqc (tcFn (nthc q i)) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_eq_symm_code_internal
      (nthcT (tcFn q) (tcFn i)) (tcFn (nthc q i))
      (substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i))
      (prf_hasWit_nthcT (prf_hasWit_tcFn q) (prf_hasWit_tcFn i))
      (prf_hasWit_tcFn (nthc q i))) _) hev
  -- el Leibniz codificado, aplicado DENTRO del contexto `PrfH`
  have hleib : Prf (provFromCode (implc
      (eqc (tcFn (nthc q i)) (nthcT (tcFn q) (tcFn i)))
      (implc (substfc zero (tcFn (nthc q i)) (lineWFCodeFn (varc (numeral 0))))
             (substfc zero (nthcT (tcFn q) (tcFn i)) (lineWFCodeFn (varc (numeral 0))))))) :=
    pcc_leibniz_code (lineWFCodeFn (varc (numeral 0)))
      (tcFn (nthc q i)) (nthcT (tcFn q) (tcFn i)) hwG_lineWF
      (prf_hasWit_tcFn (nthc q i))
      (prf_hasWit_nthcT (prf_hasWit_tcFn q) (prf_hasWit_tcFn i))
  have h2 := PrfH_mp_code_apply (prf_to_prfH hleib _) hsym
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_implc
    (hG_lineWF (tcFn (nthc q i))) (hG_lineWF (nthcT (tcFn q) (tcFn i))))) _) h2
  have hrw : PrfH [lt i (lenc q), chainOk nil q]
      (provFromCode (lineWFCodeFn (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_mp_code_apply h3 hprov
  -- (4) y el `liftc` del binder COLAPSA
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_atom1CodeFn
    (prf_congr_nthcT (prf_eq_symm (prf_liftc_tcFn q)) (prf_refl _)))) _) hrw



/-! ## §2 · **B2 · EL PUENTE DE LA COTA** de `hbody`(b), dentro de `Prov` (2026-09-10f)

§13.1 de `D3ChainDotPrf` midió que la cota de la mitad **(b)** lleva `premsOf` **DOTADO**, y que
`pcc_bdAll_intro` entrega la cota como **reflexión pura**. Ésta es la cadena que las cruza, con
`pcc_eval_premsOf` (B1, `Meta/PremsOfDotPrf.lean`) en el eslabón que faltaba:

    nthcT q̇ i̇   ↦ (nthc q i)˙    `pcc_eval_nthc`     (bajo `i < lenc q`)
    premsOfT Ẋ   ↦ (premsOf X)˙   `pcc_eval_premsOf`  (bajo `lineWF X`)
    lencT L̇      ↦ (lenc L)˙      `pcc_eval_lenc`     (incondicional)

⚠️ **Los dos primeros eslabones son CONDICIONALES**, y eso obliga a reescribir a nivel **`PrfH`**:
`pcc_rw` (`DotConsPrf`) pide la igualdad interna como `Prf`, y aquí sólo se tiene bajo hipótesis.
De ahí `PrfH_pcc_rw`, que es la misma prueba con el Leibniz interno en su versión de contexto
(`PrfH_leibniz_apply`).

⭐ Y nótese **quién paga qué**: la guarda `lineWF X` del eslabón de en medio la produce
`prf_lineWF_of_chainOk` — la misma pieza que usa la mitad (a). Es la dependencia que §13.1 midió
(«(b) consume el análisis por tags de (a)») **materializada en una sola hipótesis**. -/

/-- ⭐ `pcc_rw` a nivel `PrfH`: reescribe dentro de `Prov` con la igualdad interna **en el contexto
    de hipótesis**. -/
theorem PrfH_pcc_rw {Γ : List Formula} (G : Term → Term)
    (hG : ∀ s : Term, Prf (substfc zero s (G (varc (numeral 0))) =eq G s))
    (X Y : Term) (heq : PrfH Γ (provFromCode (eqc X Y)))
    (hbase : PrfH Γ (provFromCode (G X)))
    (hwG : Prf (hasWitF (G (varc (numeral 0)))))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) :
    PrfH Γ (provFromCode (G Y)) := by
  have h1 : PrfH Γ (provFromCode (substfc zero X (G (varc (numeral 0))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hG X))) _) hbase
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hG Y)) _)
    (PrfH_leibniz_apply (G (varc (numeral 0))) X Y heq h1 hwG hwX hwY)

/-- Contexto de reescritura: el hueco, en el argumento de `premsOfT`. -/
theorem hG_premsOfT (L : Term) (s : Term) :
    Prf (substfc zero s (eqCodeFn (premsOfT (varc (numeral 0))) (tcFn L))
      =eq eqCodeFn (premsOfT s) (tcFn L)) := by
  refine prf_eq_trans (prf_substfc_eq zero s (premsOfT (varc (numeral 0))) (tcFn L)) ?_
  exact prf_congr_eqCodeFn
    (prf_eq_trans (prf_substtc_premsOfT zero s (varc (numeral 0)))
      (prf_congr_premsOfT (prf_substtc_varc0 s)))
    (prf_substtc_tcFn s L)

/-- Contexto de reescritura: el hueco, en el argumento de `lencT`. -/
theorem hG_lencT (L : Term) (s : Term) :
    Prf (substfc zero s (eqCodeFn (lencT (varc (numeral 0))) (tcFn (lenc L)))
      =eq eqCodeFn (lencT s) (tcFn (lenc L))) := by
  refine prf_eq_trans (prf_substfc_eq zero s (lencT (varc (numeral 0))) (tcFn (lenc L))) ?_
  exact prf_congr_eqCodeFn
    (prf_eq_trans (prf_substtc_lencT zero s (varc (numeral 0)))
      (prf_congr_lencT (prf_substtc_varc0 s)))
    (prf_substtc_tcFn s (lenc L))

/-- 🏁🏁 **B2 · LA COTA DE `hbody`(b), CRUZADA DENTRO DE `Prov`.** -/
theorem pcc_bnd_bridge (q i : Term) :
    Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (eqCodeFn (lencT (premsOfT (nthcT (tcFn q) (tcFn i))))
        (tcFn (lenc (premsOf (nthc q i))))))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [chainOk nil q] rfl)
  let Gm : List Formula := [lt i (lenc q), chainOk nil q]
  let X : Term := nthc q i
  let L : Term := premsOf X
  have hch : PrfH Gm (chainOk nil q) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH Gm (lt i (lenc q)) := PrfH.hyp _ _ (List.Mem.head _)
  have hline : PrfH Gm (lineWF X) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_lineWF_of_chainOk q i) _) hch) hlt
  -- (1) `nthcT q̇ i̇ ↦ Ẋ`
  have e1 : PrfH Gm (provFromCode (eqc (nthcT (tcFn q) (tcFn i)) (tcFn X))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc q i) _) hlt
  have e1s : PrfH Gm (provFromCode (eqc (tcFn X) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_eq_symm_code_internal
      (nthcT (tcFn q) (tcFn i)) (tcFn X)
      (substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i))
      (prf_hasWit_nthcT (prf_hasWit_tcFn q) (prf_hasWit_tcFn i))
      (prf_hasWit_tcFn X)) _) e1
  -- (2) `premsOfT Ẋ ↦ L̇` — **B1**, y lo que la habilita es `hline`
  have e2 : PrfH Gm (provFromCode (eqc (premsOfT (tcFn X)) (tcFn L))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_premsOf X) _) hline
  -- (3) el argumento de `premsOfT`, reescrito dentro de `Prov`
  have e2p : PrfH Gm (provFromCode (eqc (premsOfT (nthcT (tcFn q) (tcFn i))) (tcFn L))) :=
    PrfH_pcc_rw (fun c => eqCodeFn (premsOfT c) (tcFn L)) (hG_premsOfT L) _ _ e1s e2
      (prf_hasWitF_eq2 _ _ (prf_hasWit_premsOfT (prf_hasWit_varc (numeral 0)))
        (prf_hasWit_tcFn L))
      (prf_hasWit_tcFn X)
      (prf_hasWit_nthcT (prf_hasWit_tcFn q) (prf_hasWit_tcFn i))
  have e2s : PrfH Gm (provFromCode (eqc (tcFn L) (premsOfT (nthcT (tcFn q) (tcFn i))))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_eq_symm_code_internal
      (premsOfT (nthcT (tcFn q) (tcFn i))) (tcFn L)
      (substtc_inv_premsOfT (substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i)))
      (prf_hasWit_premsOfT (prf_hasWit_nthcT (prf_hasWit_tcFn q) (prf_hasWit_tcFn i)))
      (prf_hasWit_tcFn L)) _) e2p
  -- (4) `lencT L̇ ↦ (lenc L)˙`, con el argumento ya reescrito
  have e3 : PrfH Gm (provFromCode (eqc (lencT (tcFn L)) (tcFn (lenc L)))) :=
    prf_to_prfH (pcc_eval_lenc L) _
  exact PrfH_pcc_rw (fun c => eqCodeFn (lencT c) (tcFn (lenc L))) (hG_lencT L) _ _ e2s e3
    (prf_hasWitF_eq2 _ _ (prf_hasWit_lencT (prf_hasWit_varc (numeral 0)))
      (prf_hasWit_tcFn (lenc L)))
    (prf_hasWit_tcFn L)
    (prf_hasWit_premsOfT (prf_hasWit_nthcT (prf_hasWit_tcFn q) (prf_hasWit_tcFn i)))

/-! ## §3 · EL DESTINO DE `hbody`(b), MEDIDO POR `rfl`

Regla de §3.44: el destino se despliega y se casa por `rfl` **antes** de escribir nada. -/

/-- El cuerpo del `∀` acotado de `boundedPremsIn`, ya bajo el binder y con las capas de `liftc`
    que le impone su posición dentro del `PsiF` exterior. -/
noncomputable def premsPsi (q i : Term) : Term :=
  substCodeF2 1 (liftc zero (tcFn i)) (liftc zero (liftc zero (tcFn q)))
    (lor (In (nthc (liftTerm 0 (premsOf (nthc (.var 1) (.var 0)))) (.var 0)) (liftTerm 0 nil))
         (boundedCarcLt (nthc (liftTerm 0 (premsOf (nthc (.var 1) (.var 0)))) (.var 0))
           (liftTerm 0 (.var 1)) (liftTerm 0 (.var 0))))

/-- ⭐ **EL DESTINO, DESCOMPUESTO**: `premsDotAt` **es** un `bdAllCode`, y su cota lleva `premsOf`
    dotado con **dos** capas de `liftc` — una por cada binder que lo cubre. -/
theorem premsDotAt_split (q i : Term) :
    premsDotAt q i
      = bdAllCode (lencT (premsOfT (nthcT (liftc zero (liftc zero (tcFn q)))
          (liftc zero (tcFn i))))) (premsPsi q i) := rfl

/-- Y las dos capas de `liftc` **COLAPSAN** a nivel objeto (`prf_liftc_tcFn`), con lo que la cota
    del destino es exactamente la que `pcc_bnd_bridge` cruza. -/
theorem prf_bnd_collapse (q i : Term) :
    Prf (lencT (premsOfT (nthcT (liftc zero (liftc zero (tcFn q))) (liftc zero (tcFn i))))
      =eq lencT (premsOfT (nthcT (tcFn q) (tcFn i)))) :=
  prf_congr_lencT (prf_congr_premsOfT (prf_congr_nthcT
    (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn q)) (prf_liftc_tcFn q))
    (prf_liftc_tcFn i)))

/-- 🏁 **La cota del DESTINO, cruzada**: `pcc_bnd_bridge` con el colapso ya aplicado. Es la forma
    que `PrfH_bdAllCode_congr_bnd` consumirá para transportar el `bdAllCode` que produzca B3. -/
theorem pcc_bnd_bridge_at (q i : Term) :
    Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (eqCodeFn (tcFn (lenc (premsOf (nthc q i))))
        (lencT (premsOfT (nthcT (liftc zero (liftc zero (tcFn q))) (liftc zero (tcFn i)))))))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [chainOk nil q] rfl)
  have hch : PrfH [lt i (lenc q), chainOk nil q] (chainOk nil q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [lt i (lenc q), chainOk nil q] (lt i (lenc q)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have h : PrfH [lt i (lenc q), chainOk nil q]
      (provFromCode (eqCodeFn (lencT (premsOfT (nthcT (tcFn q) (tcFn i))))
        (tcFn (lenc (premsOf (nthc q i)))))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_bnd_bridge q i) _) hch) hlt
  have hs : PrfH [lt i (lenc q), chainOk nil q]
      (provFromCode (eqCodeFn (tcFn (lenc (premsOf (nthc q i))))
        (lencT (premsOfT (nthcT (tcFn q) (tcFn i)))))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_eq_symm_code_internal
      (lencT (premsOfT (nthcT (tcFn q) (tcFn i)))) (tcFn (lenc (premsOf (nthc q i))))
      (substtc_inv_lencT (substtc_inv_premsOfT
        (substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i))))
      (prf_hasWit_lencT (prf_hasWit_premsOfT
        (prf_hasWit_nthcT (prf_hasWit_tcFn q) (prf_hasWit_tcFn i))))
      (prf_hasWit_tcFn (lenc (premsOf (nthc q i))))) _) h
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_eq_symm (prf_bnd_collapse q i)))) _) hs


end ROBINSON_PlusPlus.Meta.D3BodyPrf


/-! ## `export` — por CONSUMO

El consumidor previsto es el ensamblaje de D3: `d3_prf_of_halves` (`D3ChainDotPrf` §13) pide
exactamente `hA` y `hB`, y ésta es `hA`. -/
export ROBINSON_PlusPlus.Meta.D3BodyPrf (
  hG_lineWF hwG_lineWF prf_lineWF_of_chainOk hA_lineWFDotAt
  PrfH_pcc_rw hG_premsOfT hG_lencT pcc_bnd_bridge
  premsPsi premsDotAt_split prf_bnd_collapse pcc_bnd_bridge_at
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.D3BodyPrf.hA_lineWFDotAt
#print axioms ROBINSON_PlusPlus.Meta.D3BodyPrf.pcc_bnd_bridge_at
