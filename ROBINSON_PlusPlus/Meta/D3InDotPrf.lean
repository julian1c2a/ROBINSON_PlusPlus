/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.D3DottedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.RunFnBoundedPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf
open ROBINSON_PlusPlus.Meta.D3DottedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.ExIntroCodePrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.ChainPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace ROBINSON_PlusPlus.Meta.D3InDotPrf

/-!
## META — NIVEL D real (§38): reflexión PUNTEADA del átomo `In` (`hI_dot`, ruta B)

Segundo de los dos átomos punteados del cuerpo Δ₀ de `provCodeC' φ` (tras `chainOk`): dado
`chainOk nil p` e `In ⌜φ⌝ (runFn nil p)` (con `p = #0` **libre**), producir
`provFromCode (inDot φ)` — el código del átomo `In ⌜φ⌝ (runFn nil ṗ)` con `p` dotado (`ṗ = tcFn #0`).

Estrategia (análoga a `pcc_lt_tracked`, pero con la implicación objeto **codificada**):

1. `In ⌜φ⌝ (runFn nil p) ⇒ boundedCarcIn ⌜φ⌝ p` (`prf_boundedCarcIn_of_In_runFn`): pasar al `∃`
   acotado `∃i<lenc p. carc(nthc p i) = ⌜φ⌝`.
2. Reflejar ese `∃` acotado DOTADO (`pcc_bdEx_intro_open`, testigo `tcFn i`), con la cota vía
   `pcc_lt_tracked`+`pcc_eval_lenc` y el cuerpo vía `pcc_eq_tracked`+`pcc_eval_carc_nthc`+`prf_tc_form`
   (aquí entra `chainOk`, que `pcc_eval_carc_nthc` necesita).
3. Codificar la implicación objeto `boundedCarcIn ⌜φ⌝ p ⇒ In ⌜φ⌝ (runFn nil p)` (`pcc_thm_inst` del
   teorema generalizado) y MP interno (`pcc_mp_code_open`) para llegar a `provFromCode (inDot φ)`.
-/

/-- **`∃i<B`-intro a nivel de código, versión OPEN** (sin clausura de `B`/`Phic`): admite cotas y
    cuerpos con variables objeto **libres** (necesario para `p` dotado, `B = lencT (liftc 0 ṗ)`).
    Sólo pide `hBinv` (`substtc`-invariancia de `B`); la `∃`-intro interna es la abierta
    (`pcc_exIntro_code_open`), que no requiere `liftTerm`-invariancia. -/
theorem pcc_bdEx_intro_open (B Phic K : Term)
    (hBinv : ∀ W, Prf (substtc zero W B =eq B))
    (hlt : Prf (provFromCode (ltCodeFn K B)))
    (hphi : Prf (provFromCode (substfc zero K Phic)))
    (hwB : Prf (hasWit (liftTerm 0 B))) (hwP : Prf (hasWitF (liftTerm 0 Phic)))
    (hwK : Prf (hasWit (liftTerm 0 K))) :
    Prf (provFromCode (bdExCode B Phic)) := by
  have hand : Prf (provFromCode (andc (ltCodeFn K B) (substfc zero K Phic))) :=
    pcc_and_intro_code hlt hphi
  have hsub : Prf (substfc zero K (andc (ltCodeFn (varc (numeral 0)) B) Phic)
      =eq andc (ltCodeFn K B) (substfc zero K Phic)) :=
    prf_eq_trans (prf_substfc_and zero K _ _)
      (prf_congr_andc (prf_substfc_ltCodeFn_varc0 B K hBinv) (prf_refl _))
  have hant : Prf (provFromCode (substfc zero K (andc (ltCodeFn (varc (numeral 0)) B) Phic))) :=
    prf_mp (prf_provCode_congr (prf_eq_symm hsub)) hand
  exact prf_mp (pcc_exIntro_code_open (andc (ltCodeFn (varc (numeral 0)) B) Phic) K
    (prf_hasWitF_andc (ltCodeFn (varc (numeral 0)) (liftTerm 0 B)) (liftTerm 0 Phic)
      (prf_hasWitF_atom2 (strCode lt_sym) (varc (numeral 0)) (liftTerm 0 B)
        (prf_hasWit_varc (numeral 0)) hwB) hwP)
    hwK) hant

/-! ### Combinadores internos bajo CONTEXTO (`PrfH`)

El núcleo de Step B extrae el testigo con `PrfH_ex_elim`, así que todas las reflexiones viven bajo
contexto: hacen falta las versiones `PrfH` del `∧`-intro y del `∃i<B`-intro internos, más la
**simetría interna de `=`** (que no existía: `pcc_eq_trans_code`/`pcc_congr_succ_code` sí, symm no).
La simetría es imprescindible para la COTA — `tcFn (lenc p)` y `lencT ṗ` sólo son iguales *dentro* de
`Prov` (es la evaluación provable), y Leibniz transporta en la dirección contraria a la que hace falta. -/

/-- **Simetría interna de `=` a nivel de código**, en `PrfH`: `Prov(⌜X=Y⌝) → Prov(⌜Y=X⌝)`.
    Leibniz con el contexto `Ac := (v₀ = X)`; la base `Ac[X]` es la reflexividad codificada. -/
theorem PrfH_eq_symm_code {Γ : List Formula} (X Y : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (heq : PrfH Γ (provFromCode (eqc X Y)))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) :
    PrfH Γ (provFromCode (eqc Y X)) := by
  let Ac : Term := eqc (varc (numeral 0)) X
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc t X) := fun t =>
    prf_eq_trans (prf_substfc_eq zero t (varc (numeral 0)) X)
      (prf_congr_eqCodeFn (prf_substtc_varc0 t) (hX t))
  have hrefl : Prf (provFromCode (eqc X X)) := prf_provFromCode_eqCodeFn_refl X
  have hAX : PrfH Γ (provFromCode (substfc zero X Ac)) :=
    prf_to_prfH (prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X))) hrefl) _
  have hAY : PrfH Γ (provFromCode (substfc zero Y Ac)) :=
    PrfH_leibniz_apply Ac X Y heq hAX
      (prf_hasWitF_eq2 (varc (numeral 0)) X (prf_hasWit_varc (numeral 0)) hwX) hwX hwY
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _) hAY

/-- `∧`-intro interno a nivel de código, en `PrfH` (patrón de `hbody_of_atoms`: `pcc_c1_code` + dos MP). -/
theorem PrfH_and_intro_code {Γ : List Formula} (Ac Bc : Term)
    (ha : PrfH Γ (provFromCode Ac)) (hb : PrfH Γ (provFromCode Bc)) :
    PrfH Γ (provFromCode (andc Ac Bc)) := by
  have step1 : Prf (provFromCode Ac ⇒ provFromCode (implc Bc (andc Ac Bc))) :=
    prf_mp (pcc_mp_code_open Ac (implc Bc (andc Ac Bc))) (pcc_c1_code Ac Bc)
  exact PrfH_mp_code_apply (PrfH.mp _ _ _ (prf_to_prfH step1 _) ha) hb

/-- **`∃i<B`-intro OPEN, versión `PrfH`** (la que usa el núcleo de Step B: cota y cuerpo se reflejan
    bajo el contexto del `∃`-elim). -/
theorem PrfH_bdEx_intro_open {Γ : List Formula} (B Phic K : Term)
    (hBinv : ∀ W, Prf (substtc zero W B =eq B))
    (hlt : PrfH Γ (provFromCode (ltCodeFn K B)))
    (hphi : PrfH Γ (provFromCode (substfc zero K Phic)))
    (hwB : Prf (hasWit (liftTerm 0 B))) (hwP : Prf (hasWitF (liftTerm 0 Phic)))
    (hwK : Prf (hasWit (liftTerm 0 K))) :
    PrfH Γ (provFromCode (bdExCode B Phic)) := by
  have hand : PrfH Γ (provFromCode (andc (ltCodeFn K B) (substfc zero K Phic))) :=
    PrfH_and_intro_code _ _ hlt hphi
  have hsub : Prf (substfc zero K (andc (ltCodeFn (varc (numeral 0)) B) Phic)
      =eq andc (ltCodeFn K B) (substfc zero K Phic)) :=
    prf_eq_trans (prf_substfc_and zero K _ _)
      (prf_congr_andc (prf_substfc_ltCodeFn_varc0 B K hBinv) (prf_refl _))
  have hant : PrfH Γ (provFromCode (substfc zero K (andc (ltCodeFn (varc (numeral 0)) B) Phic))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm hsub)) _) hand
  exact PrfH.mp _ _ _
    (prf_to_prfH (pcc_exIntro_code_open (andc (ltCodeFn (varc (numeral 0)) B) Phic) K
      (prf_hasWitF_andc (ltCodeFn (varc (numeral 0)) (liftTerm 0 B)) (liftTerm 0 Phic)
      (prf_hasWitF_atom2 (strCode lt_sym) (varc (numeral 0)) (liftTerm 0 B)
        (prf_hasWit_varc (numeral 0)) hwB) hwP)
    hwK) _) hant

/-! ### Toolkit De Bruijn / `substtc` para el testigo dotado

El `∃`-elim **liftea** `p` (de `#0` a `#1`), así que los lemas fijados en `#0` no aplicarían después:
todo lo dotado se generaliza sobre un testigo `p` **arbitrario** (igual que `pcc_lt_tracked` hace con
`s`,`t`), y estos lemas garantizan que el lift atraviesa `tcFn`/`inDot`/`bddCarcDot` moviendo `p`. -/

/-- El lift atraviesa `tcFn` (es `Term.func "tcFn" [·]`). -/
theorem liftTerm_tcFn (c : Nat) (t : Term) : liftTerm c (tcFn t) = tcFn (liftTerm c t) := by
  simp only [tcFn, liftTerm, liftTerms]

/-- `liftc 0 (tcFn a)` es `substtc`-invariante (vía `prf_liftc_tcFn` + `prf_substtc_tcFn`). -/
theorem substtc_inv_liftc_tcFn (a : Term) :
    ∀ W, Prf (substtc zero W (liftc zero (tcFn a)) =eq liftc zero (tcFn a)) := fun W =>
  prf_eq_trans (prf_congr_substtc3 (prf_liftc_tcFn a))
    (prf_eq_trans (prf_substtc_tcFn W a) (prf_eq_symm (prf_liftc_tcFn a)))

/-! ### El sustituto de `prf_tc_form` (2026-08-23)

`prf_tc_form (φ) : Prf (tcFn (formCode φ) =eq termCode (formCode φ))` murió con `ax_tc_cons`: bajo
la lectura numeral su enunciado es **falso**, porque `tcFn (formCode φ)` es el código del NUMERAL y
`termCode (formCode φ)` el del árbol `cons`. Dos códigos distintos de dos términos que **denotan el
mismo número**.

⚠️ **El lado derecho NO se puede cambiar.** `inDot φ` está fijado por `Meta/D3DottedPrf.lean` —que
sale de la definición de `provCodeC'`— y lleva `termCode (formCode φ)`. Ese código **es el objetivo
de D3**: cambiarlo sería cambiar el teorema, no refundar un enunciado.

**La salida:** probar por dentro en forma NUMERAL, y convertir en la **frontera**, dentro de `Prov`,
usando que D1 dota `prf_formCode_numeral`. Los enunciados públicos de este módulo quedan intactos.
Medición completa en `sondeos/TcFormPayoff.lean`. -/

/-- El sustituto directo, **net‑0**: la vía numeral sobre la estructura CONCRETA de `φ`.
    ⚠️ Nótese el código estático cambiado a la derecha. -/
theorem prf_tc_form_numeral (φ : Formula) :
    Prf (tcFn (formCode φ) =eq termCode (numeral (codeNat φ))) :=
  prf_eq_trans (prf_congr_tcFn (prf_formCode_numeral φ)) (prf_tc_numeral (codeNat φ))

/-- **EL CONVERTIDOR DE FRONTERA**, en forma implicación (para entrar en `PrfH`).
    De la forma numeral a la forma `formCode`, **dentro de `Prov`**, en cualquier hueco.

    Es `pcc_rw_imp` con el puente de **D1**: `formCode φ` y `numeral (codeNat φ)` son términos objeto
    provablemente iguales (`prf_formCode_numeral`), y `repr_pos'_prf` dota esa igualdad. -/
theorem pcc_to_formCode_imp (φ : Formula) (G : Term → Term)
    (hG : ∀ s : Term, Prf (substfc zero s (G (varc (numeral 0))) =eq G s))
    (hwG : Prf (hasWitF (G (varc (numeral 0))))) :
    Prf (provFromCode (G (termCode (numeral (codeNat φ))))
       ⇒ provFromCode (G (termCode (formCode φ)))) :=
  pcc_rw_imp G hG _ _ (repr_pos'_prf (prf_eq_symm (prf_formCode_numeral φ)))
    hwG (prf_hasWit_tc (numeral (codeNat φ))) (prf_hasWit_tc (formCode φ))

/-- Ídem, en forma directa. -/
theorem pcc_to_formCode (φ : Formula) (G : Term → Term)
    (hG : ∀ s : Term, Prf (substfc zero s (G (varc (numeral 0))) =eq G s))
    (h : Prf (provFromCode (G (termCode (numeral (codeNat φ))))))
    (hwG : Prf (hasWitF (G (varc (numeral 0))))) :
    Prf (provFromCode (G (termCode (formCode φ)))) :=
  prf_mp (pcc_to_formCode_imp φ G hG hwG) h

/-- `termCode (formCode φ)` es `substtc`-invariante. **Mismo enunciado que antes**; la prueba ya no
    pasa por `tcFn`, sino directamente por que `formCode φ` es un término **CERRADO**. -/
theorem substtc_inv_termCode_formCode (φ : Formula) :
    ∀ W, Prf (substtc zero W (termCode (formCode φ)) =eq termCode (formCode φ)) := fun W => by
  have h := prf_substtc_arith_open 0 W (formCode φ)
  rw [substCodeT_closed 0 W (formCode φ) (fun c => liftTerm_formCode c φ)] at h
  exact h

/-- Espejo de `prf_substfc_ltCodeFn_varc0`: el hueco `⌜v₀⌝` en la **segunda** posición
    (`substfc 0 K (A < ⌜v₀⌝) =eq (A < K)`). Lo necesita el Leibniz de la cota. -/
theorem prf_substfc_ltCodeFn_snd (A K : Term)
    (hAinv : ∀ W, Prf (substtc zero W A =eq A)) :
    Prf (substfc zero K (ltCodeFn A (varc (numeral 0))) =eq ltCodeFn A K) := by
  have hts : Prf (substtsc zero K (cons A (cons (varc (numeral 0)) nil))
      =eq cons A (cons K nil)) :=
    prf_eq_trans (prf_substtsc_cons zero K A (cons (varc (numeral 0)) nil))
      (prf_eq_trans (prf_congr_cons_head (hAinv K))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_substtsc_cons zero K (varc (numeral 0)) nil)
            (prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0 K))
              (prf_congr_cons_tail (prf_substtsc_nil zero K))))))
  refine prf_eq_trans (prf_substfc_atom zero K (strCode lt_sym)
    (cons A (cons (varc (numeral 0)) nil))) ?_
  show Prf (atomc (strCode lt_sym) (substtsc zero K (cons A (cons (varc (numeral 0)) nil)))
    =eq atomc (strCode lt_sym) (cons A (cons K nil)))
  unfold atomc
  exact prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head hts))

/-! ### Step A — la implicación ⇐ CODIFICADA (`boundedCarcIn ⌜φ⌝ ṗ ⇒ In ⌜φ⌝ (runFn nil ṗ)`)

El teorema objeto `prf_In_runFn_of_boundedCarcIn ⌜φ⌝ #0` se generaliza (`Prf.gen`) y se instancia
DOTADO (`pcc_thm_inst`, testigo `tcFn #0`). Distribuyendo `substfc` sobre el `implc`
(`prf_substfc_impl`), el consecuente es **exactamente `inDot φ`** (por definición de `inDot`) y el
antecedente es `bddCarcDot φ` (código dotado de `boundedCarcIn`). -/

/-- Cuerpo objeto de la implicación ⇐ (con `p = #0`): `boundedCarcIn ⌜φ⌝ #0 ⇒ In ⌜φ⌝ (runFn nil #0)`. -/
noncomputable def inBwdBody (φ : Formula) : Formula :=
  Formula.impl (boundedCarcIn (formCode φ) (.var 0)) (In (formCode φ) (runFn nil (.var 0)))

/-- Código DOTADO del átomo `In`, con testigo `p` **arbitrario**. `inDot φ = inDotAt φ #0` (rfl).
    Nota: el `formCode` codifica siempre el **esquema** (con `#0` en el hueco de `p`); lo único que
    varía es el testigo dotado `tcFn p`. -/
noncomputable def inDotAt (φ : Formula) (p : Term) : Term :=
  substfc zero (tcFn p) (formCode (In (formCode φ) (runFn nil (.var 0))))

/-- Código DOTADO del antecedente `boundedCarcIn`, con testigo `p` **arbitrario**. -/
noncomputable def bddCarcDotAt (φ : Formula) (p : Term) : Term :=
  substfc zero (tcFn p) (formCode (boundedCarcIn (formCode φ) (.var 0)))

/-- Código dotado del antecedente en `p = #0` (el que consume `hbody_of_atoms`). -/
noncomputable def bddCarcDot (φ : Formula) : Term := bddCarcDotAt φ (.var 0)

theorem inDot_eq_inDotAt (φ : Formula) : inDot φ = inDotAt φ (.var 0) := rfl

/-- El lift atraviesa `inDotAt` moviendo el testigo (`formCode` es cerrado, `liftTerm_substfc_open`). -/
theorem liftTerm_inDotAt (c : Nat) (φ : Formula) (p : Term) :
    liftTerm c (inDotAt φ p) = inDotAt φ (liftTerm c p) := by
  unfold inDotAt
  rw [liftTerm_substfc_open _ (fun k => liftTerm_formCode k _) (tcFn p) c, liftTerm_tcFn]

/-- El lift atraviesa `bddCarcDotAt` moviendo el testigo. -/
theorem liftTerm_bddCarcDotAt (c : Nat) (φ : Formula) (p : Term) :
    liftTerm c (bddCarcDotAt φ p) = bddCarcDotAt φ (liftTerm c p) := by
  unfold bddCarcDotAt
  rw [liftTerm_substfc_open _ (fun k => liftTerm_formCode k _) (tcFn p) c, liftTerm_tcFn]

/-- **Step A** (testigo arbitrario): `⊢ Prov(⌜ bddCarcDotAt φ p ⇒ inDotAt φ p ⌝)`. Instancia dotada
    del teorema ⇐ (`Prf.gen` + `pcc_thm_inst` con testigo `tcFn p`), con `substfc` distribuido sobre
    el `implc`; el consecuente coincide con `inDotAt φ p` por definición. -/
theorem pcc_bddDot_imp_inDot_at (φ : Formula) (p : Term) :
    Prf (provFromCode (implc (bddCarcDotAt φ p) (inDotAt φ p))) := by
  have hthm : Prf (provFromCode (substfc zero (tcFn p) (formCode (inBwdBody φ)))) :=
    pcc_thm_inst (inBwdBody φ) (Prf.gen _ (prf_In_runFn_of_boundedCarcIn (formCode φ) (.var 0)))
      (tcFn p) (prf_hasWit_tcFn (liftTerm 0 p))
  have hbridge : Prf (substfc zero (tcFn p) (formCode (inBwdBody φ))
      =eq implc (bddCarcDotAt φ p) (inDotAt φ p)) :=
    prf_substfc_impl zero (tcFn p) (formCode (boundedCarcIn (formCode φ) (.var 0)))
      (formCode (In (formCode φ) (runFn nil (.var 0))))
  exact prf_mp (prf_provCode_congr hbridge) hthm

/-- Step A en `p = #0`. -/
theorem pcc_bddDot_imp_inDot (φ : Formula) :
    Prf (provFromCode (implc (bddCarcDot φ) (inDot φ))) := pcc_bddDot_imp_inDot_at φ (.var 0)

/-! ### Step B (puente) — `bddCarcDot φ` como `bdExCode` con argumentos DOTADOS

El código dotado del antecedente `boundedCarcIn` es un `∃` acotado codificado (`bdExCode`) con:
* cota `bdCarcB = lencT (liftc 0 ṗ)` (el `liftc 0` viene del binder de `substfc`);
* cuerpo `bdCarcPhic φ = eqCodeFn (carcT (nthcT (liftc 0 ṗ) ⌜v₀⌝)) ⌜φ⌝` (con `⌜φ⌝ = termCode (formCode φ)`,
  reducido vía `substCodeT_closed`).

Establece `bddCarcDot φ =eq bdExCode bdCarcB (bdCarcPhic φ)`: `prf_substfc_arith_open` lleva la forma
`substfc` a `substCodeF`, y `substCodeF_boundedCarcIn` (ecuación META, rfl salvo la reducción del
`formCode φ` cerrado) la identifica con `bdExCode`. -/

/-- Cota (dotada, bajo el binder) del `∃` acotado de `boundedCarcIn`: `lencT (liftc 0 ṗ)`. -/
noncomputable def bdCarcBAt (p : Term) : Term := lencT (liftc zero (tcFn p))

/-- Cuerpo (dotado) del `∃` acotado: `carcT (nthcT (liftc 0 ṗ) ⌜v₀⌝) = ⌜φ⌝`. -/
noncomputable def bdCarcPhicAt (φ : Formula) (p : Term) : Term :=
  eqCodeFn (carcT (nthcT (liftc zero (tcFn p)) (varc (numeral 0)))) (termCode (formCode φ))

/-- La cota dotada tiene testigo (descarga la guarda de ADR-020): es `lencT` de un `liftc` de un
    `tcFn`, o sea escalera de aridad pura. -/
theorem prf_hasWit_bdCarcBAt (p : Term) : Prf (hasWit (bdCarcBAt p)) :=
  prf_hasWit_lencT (prf_hasWit_liftc (prf_hasWit_tcFn p))

/-- El cuerpo dotado tiene testigo: es un nodo `eqc` con `carcT`/`nthcT` a la izquierda y un
    `termCode` CERRADO a la derecha. -/
theorem prf_hasWitF_bdCarcPhicAt (φ : Formula) (p : Term) :
    Prf (hasWitF (bdCarcPhicAt φ p)) :=
  prf_hasWitF_eq2 _ _
    (prf_hasWit_carcT (prf_hasWit_nthcT (prf_hasWit_liftc (prf_hasWit_tcFn p))
      (prf_hasWit_varc (numeral 0))))
    (prf_hasWit_tc (formCode φ))

/-- `liftTerm` atraviesa el cuerpo dotado. ⚠️ NO es `rfl`: el `termCode (formCode φ)` de la
    derecha necesita `liftTerm_termCode`, que es un TEOREMA (la clausura de `formCode` no es
    definicional). -/
theorem liftTerm_bdCarcPhicAt (c : Nat) (φ : Formula) (p : Term) :
    liftTerm c (bdCarcPhicAt φ p) = bdCarcPhicAt φ (liftTerm c p) := by
  simp only [bdCarcPhicAt, eqCodeFn, carcT, nthcT, liftc, tcFn, varc, funcc, cons, nil, zero,
    succ, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode, liftTerm_termCode]

/-- La guarda del cuerpo dotado, en la forma LIFTEADA que pide `PrfH_bdEx_intro_open`. -/
theorem prf_hasWitF_bdCarcPhicAt_lift (φ : Formula) (p : Term) :
    Prf (hasWitF (liftTerm 0 (bdCarcPhicAt φ p))) := by
  rw [liftTerm_bdCarcPhicAt]
  exact prf_hasWitF_bdCarcPhicAt φ (liftTerm 0 p)

/-- La cota dotada es `substtc`-invariante (descarga el `hBinv` de `pcc_bdEx_intro_open`). -/
theorem substtc_inv_bdCarcBAt (p : Term) :
    ∀ W, Prf (substtc zero W (bdCarcBAt p) =eq bdCarcBAt p) :=
  substtc_inv_lencT (substtc_inv_liftc_tcFn p)

/-- **Forma META del código dotado de `boundedCarcIn`** (rfl salvo `substCodeT_closed` sobre el
    `formCode φ` cerrado). El testigo `tcFn p` es **arbitrario**: la fórmula codificada es siempre el
    esquema con `#0`, así que la computación de `substCodeF` no depende de `p`. -/
theorem substCodeF_boundedCarcIn_at (φ : Formula) (p : Term) :
    substCodeF 0 (tcFn p) (boundedCarcIn (formCode φ) (.var 0))
      = bdExCode (bdCarcBAt p) (bdCarcPhicAt φ p) := by
  have key : substCodeT 1 (liftc zero (tcFn p)) (liftTerm 0 (formCode φ))
      = termCode (formCode φ) := by
    rw [liftTerm_formCode]
    exact substCodeT_closed 1 (liftc zero (tcFn p)) (formCode φ)
      (fun c => liftTerm_formCode c φ)
  simp only [boundedCarcIn, land, lt, lenc, carc, nthc, liftTerm, liftTerms, Nat.lt_irrefl,
    reduceIte, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, substCodeF, substCodeT,
    substCodeTs, bdExCode, bdCarcBAt, bdCarcPhicAt, exc, andc, numeral, ltCodeFn, atom2CodeFn,
    eqCodeFn, lencT, carcT, nthcT, funcc, varc, key]

/-- **`bddCarcDotAt φ p` es `bdExCode` con argumentos dotados** (versión `Prf`): compone
    `prf_substfc_arith_open` (forma `substfc` → `substCodeF`) con `substCodeF_boundedCarcIn_at`. -/
theorem prf_bddCarcDot_eq_at (φ : Formula) (p : Term) :
    Prf (bddCarcDotAt φ p =eq bdExCode (bdCarcBAt p) (bdCarcPhicAt φ p)) := by
  have h := prf_substfc_arith_open 0 (tcFn p) (boundedCarcIn (formCode φ) (.var 0))
  rwa [substCodeF_boundedCarcIn_at φ p] at h

/-! ### NÚCLEO de Step B — reflexión punteada del `∃` acotado

`chainOk nil p ⇒ boundedCarcIn ⌜φ⌝ p ⇒ Prov(⌜ bddCarcDotAt φ p ⌝)`. Espejo de `pcc_lt_tracked`:

1. **`PrfH_ex_elim`** del `∃` acotado extrae el testigo `i = #0` y **liftea `p`** (de ahí que todo lo
   dotado esté generalizado sobre `p`); la meta lifteada es `provFromCode (bddCarcDotAt φ ↑p)` gracias
   a `liftFormula_provFromCode_open` + `liftTerm_bddCarcDotAt`.
2. **COTA** `i < lenc ↑p` ⟶ `Prov(⌜ ı̇ < lencT (liftc 0 ↑ṗ) ⌝)`: `pcc_lt_tracked` da la cota con
   `tcFn (lenc ↑p)`, que hay que transportar a `lencT` — y eso **sólo vale dentro de `Prov`** (es la
   evaluación provable `pcc_eval_lenc`), en la dirección contraria a Leibniz ⟹ **simetría interna**
   (`PrfH_eq_symm_code`) + Leibniz con `Ac := (ı̇ < ⌜v₀⌝)` (`prf_substfc_ltCodeFn_snd`).
3. **CUERPO** `carc (nthc ↑p i) = ⌜φ⌝` ⟶ `Prov(⌜ carcT (nthcT (liftc 0 ↑ṗ) ı̇) = ⌜φ⌝ ⌝)`: aquí NO hace
   falta simetría — `pcc_eval_carc_nthc` (que consume `chainOk`) da la evaluación, y la hipótesis del
   `∃` es una igualdad **objeto**, así que basta congruencia objeto (`PrfH_congr_tcFn` + `prf_tc_form`
   + cancelación del `liftc` con `prf_liftc_tcFn`) y `PrfH_provCode_congr`.
4. **`PrfH_bdEx_intro_open`** (testigo `K = ı̇`) ensambla, y `prf_bddCarcDot_eq_at` transporta a la
   forma `substfc` del código dotado. -/

/-- **NÚCLEO de Step B**: la reflexión punteada del `∃` acotado `boundedCarcIn`. -/
theorem pcc_bddCarcDot_reflect (φ : Formula) (p : Term) :
    Prf (chainOk nil p ⇒ (boundedCarcIn (formCode φ) p ⇒ provFromCode (bddCarcDotAt φ p))) := by
  refine prf_deduction (deduction_aux ?_ (boundedCarcIn (formCode φ) p) [chainOk nil p] rfl)
  have hex : PrfH [boundedCarcIn (formCode φ) p, chainOk nil p]
      (boundedCarcIn (formCode φ) p) := PrfH.hyp _ _ (List.Mem.head _)
  refine PrfH_ex_elim hex ?_
  rw [liftFormula_provFromCode_open, liftTerm_bddCarcDotAt]
  -- el `∃`-elim lifteó `p` a `↑p := liftTerm 0 p`; el testigo del `∃` es `i = #0`
  let exBody : Formula := land (lt (.var 0) (liftTerm 0 (lenc p)))
    (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 (formCode φ)))
  let Γ' : List Formula :=
    [exBody, liftFormula 0 (boundedCarcIn (formCode φ) p), liftFormula 0 (chainOk nil p)]
  show PrfH Γ' (provFromCode (bddCarcDotAt φ (liftTerm 0 p)))
  have hC : PrfH Γ' exBody := PrfH.hyp _ _ (List.Mem.head _)
  have hlt : PrfH Γ' (lt (.var 0) (lenc (liftTerm 0 p))) := PrfH_and_elim_left hC
  have hbody : PrfH Γ'
      (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 (formCode φ))) :=
    PrfH_and_elim_right hC
  have hchain : PrfH Γ' (chainOk nil (liftTerm 0 p)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  -- COTA: `pcc_lt_tracked` + evaluación de `lenc` transportada (simetría interna + Leibniz)
  have hlt1 : PrfH Γ' (provFromCode (ltCodeFn (tcFn (.var 0)) (tcFn (lenc (liftTerm 0 p))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked (.var 0) (lenc (liftTerm 0 p))) _) hlt
  have hBeq : Prf (provFromCode (eqc (bdCarcBAt (liftTerm 0 p)) (tcFn (lenc (liftTerm 0 p))))) :=
    prf_mp (prf_provCode_congr
      (prf_congr_eqCodeFn (prf_congr_lencT (prf_eq_symm (prf_liftc_tcFn (liftTerm 0 p))))
        (prf_refl _)))
      (pcc_eval_lenc (liftTerm 0 p))
  have hBsym : PrfH Γ'
      (provFromCode (eqc (tcFn (lenc (liftTerm 0 p))) (bdCarcBAt (liftTerm 0 p)))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_bdCarcBAt (liftTerm 0 p)) (prf_to_prfH hBeq _)
      (prf_hasWit_bdCarcBAt (liftTerm 0 p)) (prf_hasWit_tcFn (lenc (liftTerm 0 p)))
  have hcompLt : ∀ t : Term, Prf (substfc zero t (ltCodeFn (tcFn (.var 0)) (varc (numeral 0)))
      =eq ltCodeFn (tcFn (.var 0)) t) := fun t =>
    prf_substfc_ltCodeFn_snd (tcFn (.var 0)) t (substtc_inv_tcFn (.var 0))
  have hA1 : PrfH Γ' (provFromCode (substfc zero (tcFn (lenc (liftTerm 0 p)))
      (ltCodeFn (tcFn (.var 0)) (varc (numeral 0))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcompLt _))) _) hlt1
  have hA2 : PrfH Γ' (provFromCode (substfc zero (bdCarcBAt (liftTerm 0 p))
      (ltCodeFn (tcFn (.var 0)) (varc (numeral 0))))) :=
    PrfH_leibniz_apply _ _ _ hBsym hA1
      (prf_hasWitF_atom2 (strCode lt_sym) (tcFn (.var 0)) (varc (numeral 0))
        (prf_hasWit_tcFn (.var 0)) (prf_hasWit_varc (numeral 0)))
      (prf_hasWit_tcFn (lenc (liftTerm 0 p)))
      (prf_hasWit_lencT (prf_hasWit_liftc (prf_hasWit_tcFn (liftTerm 0 p))))
  have hltB : PrfH Γ' (provFromCode (ltCodeFn (tcFn (.var 0)) (bdCarcBAt (liftTerm 0 p)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcompLt _)) _) hA2
  -- CUERPO: `pcc_eval_carc_nthc` (consume `chainOk`) + congruencia OBJETO (sin simetría interna)
  have hev : PrfH Γ' (provFromCode (eqCodeFn
      (carcT (nthcT (tcFn (liftTerm 0 p)) (tcFn (.var 0))))
      (tcFn (carc (nthc (liftTerm 0 p) (.var 0)))))) :=
    PrfH.mp _ _ _
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_carc_nthc (liftTerm 0 p) (.var 0)) _) hchain) hlt
  -- ⚠️ Aquí estaba `prf_tc_form`. Ahora el transporte de código sólo llega a la forma NUMERAL...
  have hTC : Prf (tcFn (liftTerm 0 (formCode φ)) =eq termCode (numeral (codeNat φ))) := by
    rw [liftTerm_formCode]; exact prf_tc_form_numeral φ
  have htc : PrfH Γ' (tcFn (carc (nthc (liftTerm 0 p) (.var 0)))
      =eq termCode (numeral (codeNat φ))) :=
    PrfH_eq_trans (PrfH_congr_tcFn hbody) (prf_to_prfH hTC _)
  have hlc : Prf (carcT (nthcT (liftc zero (tcFn (liftTerm 0 p))) (tcFn (.var 0)))
      =eq carcT (nthcT (tcFn (liftTerm 0 p)) (tcFn (.var 0)))) :=
    prf_congr_carcT (prf_congr_nthcT (prf_liftc_tcFn (liftTerm 0 p)) (prf_refl _))
  have hcodeq : PrfH Γ' (eqCodeFn (carcT (nthcT (tcFn (liftTerm 0 p)) (tcFn (.var 0))))
        (tcFn (carc (nthc (liftTerm 0 p) (.var 0))))
      =eq eqCodeFn (carcT (nthcT (liftc zero (tcFn (liftTerm 0 p))) (tcFn (.var 0))))
        (termCode (numeral (codeNat φ)))) :=
    PrfH_congr_eqCodeFn (prf_to_prfH (prf_eq_symm hlc) _) htc
  have hphi0n : PrfH Γ' (provFromCode (eqCodeFn
      (carcT (nthcT (liftc zero (tcFn (liftTerm 0 p))) (tcFn (.var 0))))
      (termCode (numeral (codeNat φ))))) :=
    PrfH_provCode_congr hcodeq hev
  -- ...y la FRONTERA se cruza aquí, DENTRO de `Prov`, con el puente de D1.
  -- El hueco va en el lado derecho; el izquierdo es `substtc`-invariante y no se toca.
  have hphi0 : PrfH Γ' (provFromCode (eqCodeFn
      (carcT (nthcT (liftc zero (tcFn (liftTerm 0 p))) (tcFn (.var 0))))
      (termCode (formCode φ)))) := by
    refine PrfH.mp _ _ _ (prf_to_prfH (pcc_to_formCode_imp φ
      (fun s => eqCodeFn (carcT (nthcT (liftc zero (tcFn (liftTerm 0 p))) (tcFn (.var 0)))) s)
      ?_
      (prf_hasWitF_eq2 _ _
        (prf_hasWit_carcT (prf_hasWit_nthcT
          (prf_hasWit_liftc (prf_hasWit_tcFn (liftTerm 0 p))) (prf_hasWit_tcFn (.var 0))))
        (prf_hasWit_varc (numeral 0)))) _) hphi0n
    intro s
    refine prf_eq_trans (prf_substfc_eq zero s _ (varc (numeral 0))) ?_
    exact prf_congr_eqCodeFn
      (substtc_inv_carcT (substtc_inv_nthcT (substtc_inv_liftc_tcFn (liftTerm 0 p))
        (substtc_inv_tcFn (.var 0))) s)
      (prf_substtc_varc0 s)
  have hcompPhi : Prf (substfc zero (tcFn (.var 0)) (bdCarcPhicAt φ (liftTerm 0 p))
      =eq eqCodeFn (carcT (nthcT (liftc zero (tcFn (liftTerm 0 p))) (tcFn (.var 0))))
        (termCode (formCode φ))) := by
    unfold bdCarcPhicAt
    refine prf_eq_trans (prf_substfc_eq zero (tcFn (.var 0)) _ _) ?_
    refine prf_congr_eqCodeFn ?_ (substtc_inv_termCode_formCode φ (tcFn (.var 0)))
    refine prf_eq_trans (prf_substtc_carcT zero (tcFn (.var 0)) _) ?_
    refine prf_congr_carcT ?_
    refine prf_eq_trans (prf_substtc_nthcT zero (tcFn (.var 0)) _ _) ?_
    exact prf_congr_nthcT (substtc_inv_liftc_tcFn (liftTerm 0 p) (tcFn (.var 0)))
      (prf_substtc_varc0 (tcFn (.var 0)))
  have hphi : PrfH Γ' (provFromCode (substfc zero (tcFn (.var 0))
      (bdCarcPhicAt φ (liftTerm 0 p)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm hcompPhi)) _) hphi0
  -- ENSAMBLAJE
  have hbd : PrfH Γ' (provFromCode
      (bdExCode (bdCarcBAt (liftTerm 0 p)) (bdCarcPhicAt φ (liftTerm 0 p)))) :=
    PrfH_bdEx_intro_open (bdCarcBAt (liftTerm 0 p)) (bdCarcPhicAt φ (liftTerm 0 p))
      (tcFn (.var 0)) (substtc_inv_bdCarcBAt (liftTerm 0 p)) hltB hphi
      (prf_hasWit_bdCarcBAt (liftTerm 0 (liftTerm 0 p)))
      (prf_hasWitF_bdCarcPhicAt_lift φ (liftTerm 0 p))
      (prf_hasWit_tcFn (liftTerm 0 (.var 0)))
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_bddCarcDot_eq_at φ (liftTerm 0 p)))) _) hbd

/-! ### `hI_dot` — la reflexión punteada del átomo `In`

Composición final: `In ⌜φ⌝ (runFn nil p)` ⟹ (`prf_boundedCarcIn_of_In_runFn`) `boundedCarcIn ⌜φ⌝ p`
⟹ (núcleo) `Prov(⌜bddCarcDotAt φ p⌝)` ⟹ (**MP interno** con Step A) `Prov(⌜inDotAt φ p⌝)`. -/

/-- **`hI_dot` (testigo arbitrario)**: `chainOk nil p ⇒ In ⌜φ⌝ (runFn nil p) ⇒ Prov(⌜In ⌜φ⌝ (runFn nil ṗ)⌝)`. -/
theorem hI_dot_at (φ : Formula) (p : Term) :
    Prf (chainOk nil p ⇒ (In (formCode φ) (runFn nil p) ⇒ provFromCode (inDotAt φ p))) := by
  refine prf_deduction (deduction_aux ?_ (In (formCode φ) (runFn nil p)) [chainOk nil p] rfl)
  have hIn : PrfH [In (formCode φ) (runFn nil p), chainOk nil p]
      (In (formCode φ) (runFn nil p)) := PrfH.hyp _ _ (List.Mem.head _)
  have hchain : PrfH [In (formCode φ) (runFn nil p), chainOk nil p] (chainOk nil p) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hbc : PrfH [In (formCode φ) (runFn nil p), chainOk nil p]
      (boundedCarcIn (formCode φ) p) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_boundedCarcIn_of_In_runFn (formCode φ) p) _) hIn
  have hant : PrfH [In (formCode φ) (runFn nil p), chainOk nil p]
      (provFromCode (bddCarcDotAt φ p)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_bddCarcDot_reflect φ p) _) hchain) hbc
  exact PrfH_mp_code_apply (prf_to_prfH (pcc_bddDot_imp_inDot_at φ p) _) hant

/-- **`hI_dot`** (en `p = #0`): el segundo de los dos átomos punteados que pide `d3_prf_of_dotted_atoms`. -/
theorem hI_dot (φ : Formula) :
    Prf (chainOk nil (.var 0) ⇒
      (In (formCode φ) (runFn nil (.var 0)) ⇒ provFromCode (inDot φ))) :=
  hI_dot_at φ (.var 0)

/-- **PAYOFF (§38): D3 queda reducida a `hC_dot` SOLO** — la reflexión punteada de `chainOk`.
    El átomo `In` ya está cerrado (`hI_dot`). -/
theorem d3_prf_of_chainOkDot (φ : Formula)
    (hC : Prf (chainOk nil (.var 0) ⇒ provFromCode chainOkDot)) :
    Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_dotted_atoms φ hC (hI_dot φ)

end ROBINSON_PlusPlus.Meta.D3InDotPrf

export ROBINSON_PlusPlus.Meta.D3InDotPrf (
  pcc_bdEx_intro_open PrfH_eq_symm_code PrfH_and_intro_code PrfH_bdEx_intro_open
  liftTerm_tcFn substtc_inv_liftc_tcFn substtc_inv_termCode_formCode prf_substfc_ltCodeFn_snd
  prf_tc_form_numeral pcc_to_formCode pcc_to_formCode_imp
  inBwdBody inDotAt bddCarcDotAt bddCarcDot inDot_eq_inDotAt
  liftTerm_inDotAt liftTerm_bddCarcDotAt
  pcc_bddDot_imp_inDot_at pcc_bddDot_imp_inDot
  bdCarcBAt bdCarcPhicAt substtc_inv_bdCarcBAt substCodeF_boundedCarcIn_at prf_bddCarcDot_eq_at
  pcc_bddCarcDot_reflect hI_dot_at hI_dot d3_prf_of_chainOkDot
)
