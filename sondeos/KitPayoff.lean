/-
MEDICIÓN del KIT (2026-08-23) — la última familia sin medir.

`prf_tc_nul`/`_un`/`_bin` eran **composición pura de `prf_tc_cons'`** sobre argumentos ABSTRACTOS,
luego sus enunciados son **falsos** bajo la lectura numeral, igual que el original. No se recuperan
como igualdades `Prf`.

## RESULTADO: ✅ NO es un muro. La hipótesis era correcta.

Los tres sustitutos salen **por composición de `pcc_dot_cons`, sin inducción nueva** — que es justo
lo que se conjeturaba porque `nulT`/`unT`/`binT` son todos `cons`-árboles:

| | cómo sale |
|---|---|
| `pcc_dot_nul` | **sólo reescrituras de CÓDIGO** sobre `pcc_dot_cons` (las hojas `prf_tc_numeral` y `prf_tc_zero` **nunca murieron**) |
| `pcc_dot_un`  | código → **1 paso interno** (`pcc_rw`) → código |
| `pcc_dot_bin` | código → **2 pasos internos anidados** → código |

Los tres con el footprint sancionado `[propext, choice, Quot.sound, prf_axiomsCodeT_eq]`.

🔑 **Hizo falta `pcc_dot_cons_symm`** (la dirección simétrica), que sale de
`pcc_eq_symm_code_internal` — y ésa **volvió con `BdAllIntroPrf` en el paso 3**. Los pasos componen:
hacerlos en orden de cascada fue lo que dejó la herramienta a mano.

## ⚠️ DÓNDE ESTÁ EL COSTE REAL (medido, no ejecutado)

**No en el KIT, sino en `CodeTreeReflect`.** Allí vive

    prf_tc_objAt (t) : ∀ T : CTree, Prf (tcFn (T.objAt t) =eq T.dotV t)

que es **recursión estructural sobre `CTree`** produciendo una igualdad **de CÓDIGO**. Con
sustitutos internos, esa recursión entera tiene que **moverse dentro de `Prov`**:

    pcc_tc_objAt (t) : ∀ T : CTree, Prf (provFromCode (eqc (T.dotV t) (tcFn (T.objAt t))))

**Buena noticia: todas las piezas existen y están activas.**
* transitividad interna — `pcc_eq_trans_code` (`EvalArithPrf`) ✅
* congruencias internas del KIT — `pcc_congr_unT_code`, `pcc_congr_binT_1_code`,
  `pcc_congr_binT_2_code` (`CodeCtorKit`): **SOBREVIVEN intactas**, no citan ningún símbolo muerto,
  y ya están en forma implicación, que es exactamente lo que la recursión interna pide ✅
* los tres `pcc_dot_*` de este sondeo ✅

⇒ La conversión es **mecánica pero voluminosa**: cambiar `prf_eq_trans` por `pcc_eq_trans_code` y
`prf_congr_unT`/`prf_congr_binT` por sus versiones `_code` en cada rama de la recursión.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ArithPrf ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.BdAllIntroPrf ROBINSON_PlusPlus.Meta.DerivCondPrf

namespace KitDev

def nulT (m : Nat) : Term := consT (termCode (numeralM m)) (termCode nil)
def unT (m : Nat) (a : Term) : Term := consT (termCode (numeralM m)) (consT a (termCode nil))
def binT (m : Nat) (a b : Term) : Term :=
  consT (termCode (numeralM m)) (consT a (consT b (termCode nil)))

/-- Las dos hojas SIGUEN VIVAS: `prf_tc_numeral` y `prf_tc_zero`. -/
theorem prf_tc_numeralM' (m : Nat) : Prf (tcFn (numeralM m) =eq termCode (numeralM m)) := by
  rw [numeralM_eq]; exact prf_tc_numeral m
theorem prf_tc_nil' : Prf (tcFn nil =eq termCode nil) := prf_tc_zero

/-- `pcc_dot_cons` en la dirección SIMÉTRICA, vía la simetría interna. -/
theorem pcc_dot_cons_symm (h t : Term) :
    Prf (provFromCode (eqc (tcFn (cons h t)) (consT (tcFn h) (tcFn t)))) :=
  pcc_mp_code_apply
    (pcc_eq_symm_code_internal (consT (tcFn h) (tcFn t)) (tcFn (cons h t))
      (substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t)))
    (pcc_dot_cons h t)

/-- **NULARIO** — sólo reescrituras de CÓDIGO sobre `pcc_dot_cons`. -/
theorem pcc_dot_nul (m : Nat) :
    Prf (provFromCode (eqc (nulT m) (tcFn (cons (numeralM m) nil)))) := by
  unfold nulT
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_consT (prf_tc_numeralM' m) prf_tc_nil') (prf_refl _)))
    (pcc_dot_cons (numeralM m) nil)

/-- `⌜m̄⌝` es `substtc`-invariante: `numeralM m` es CERRADO (mismo truco que el sitio 1 del paso 3). -/
theorem substtc_inv_termCode_numeralM (m : Nat) :
    ∀ W, Prf (substtc zero W (termCode (numeralM m)) =eq termCode (numeralM m)) := fun W => by
  have h := prf_substtc_arith_open 0 W (numeralM m)
  rw [substCodeT_closed 0 W (numeralM m)
    (fun c => by rw [numeralM_eq]; exact liftTerm_numeral c m)] at h
  exact h

/-- **UNARIO** — código, luego INTERNO (`pcc_rw` con la simétrica), luego código. -/
theorem pcc_dot_un (m : Nat) (a : Term) :
    Prf (provFromCode (eqc (unT m (tcFn a)) (tcFn (cons (numeralM m) (cons a nil))))) := by
  unfold unT
  -- (1) código: `(numeralM m)˙ ⟶ ⌜m̄⌝`
  have h1 : Prf (provFromCode (eqc (consT (termCode (numeralM m)) (tcFn (cons a nil)))
      (tcFn (cons (numeralM m) (cons a nil))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
        (prf_congr_consT (prf_tc_numeralM' m) (prf_refl _)) (prf_refl _)))
      (pcc_dot_cons (numeralM m) (cons a nil))
  -- (2) INTERNO: `(cons a nil)˙ ⟶ consT ȧ nil˙`
  have h2 : Prf (provFromCode (eqc
      (consT (termCode (numeralM m)) (consT (tcFn a) (tcFn nil)))
      (tcFn (cons (numeralM m) (cons a nil))))) := by
    refine pcc_rw (fun s => eqc (consT (termCode (numeralM m)) s)
      (tcFn (cons (numeralM m) (cons a nil)))) ?_ _ _ (pcc_dot_cons_symm a nil) h1
    intro s
    refine prf_eq_trans (prf_substfc_eq zero s _ _) ?_
    exact prf_congr_eqCodeFn
      (prf_eq_trans (prf_substtc_consT zero s _ _)
        (prf_congr_consT (substtc_inv_termCode_numeralM m s) (prf_substtc_varc0 s)))
      (substtc_inv_tcFn _ s)
  -- (3) código: `nil˙ ⟶ ⌜nil⌝`
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_consT (prf_refl _) (prf_congr_consT (prf_refl _) prf_tc_nil')) (prf_refl _))) h2

/-- **BINARIO** — igual, con DOS pasos internos anidados. -/
theorem pcc_dot_bin (m : Nat) (a b : Term) :
    Prf (provFromCode (eqc (binT m (tcFn a) (tcFn b))
      (tcFn (cons (numeralM m) (cons a (cons b nil)))))) := by
  unfold binT
  let RHS : Term := tcFn (cons (numeralM m) (cons a (cons b nil)))
  have hR : ∀ W, Prf (substtc zero W RHS =eq RHS) := substtc_inv_tcFn _
  -- (1) código: `(numeralM m)˙ ⟶ ⌜m̄⌝`
  have h1 : Prf (provFromCode (eqc
      (consT (termCode (numeralM m)) (tcFn (cons a (cons b nil)))) RHS)) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
        (prf_congr_consT (prf_tc_numeralM' m) (prf_refl _)) (prf_refl _)))
      (pcc_dot_cons (numeralM m) (cons a (cons b nil)))
  -- (2) INTERNO ×1: `(cons a (cons b nil))˙ ⟶ consT ȧ (cons b nil)˙`
  have h2 : Prf (provFromCode (eqc
      (consT (termCode (numeralM m)) (consT (tcFn a) (tcFn (cons b nil)))) RHS)) := by
    refine pcc_rw (fun s => eqc (consT (termCode (numeralM m)) s) RHS) ?_ _ _
      (pcc_dot_cons_symm a (cons b nil)) h1
    intro s
    refine prf_eq_trans (prf_substfc_eq zero s _ _) ?_
    exact prf_congr_eqCodeFn
      (prf_eq_trans (prf_substtc_consT zero s _ _)
        (prf_congr_consT (substtc_inv_termCode_numeralM m s) (prf_substtc_varc0 s)))
      (hR s)
  -- (3) INTERNO ×2: `(cons b nil)˙ ⟶ consT ḃ nil˙`, ahora ANIDADO
  have h3 : Prf (provFromCode (eqc
      (consT (termCode (numeralM m)) (consT (tcFn a) (consT (tcFn b) (tcFn nil)))) RHS)) := by
    refine pcc_rw (fun s => eqc (consT (termCode (numeralM m)) (consT (tcFn a) s)) RHS) ?_ _ _
      (pcc_dot_cons_symm b nil) h2
    intro s
    refine prf_eq_trans (prf_substfc_eq zero s _ _) ?_
    refine prf_congr_eqCodeFn ?_ (hR s)
    refine prf_eq_trans (prf_substtc_consT zero s _ _) ?_
    refine prf_congr_consT (substtc_inv_termCode_numeralM m s) ?_
    exact prf_eq_trans (prf_substtc_consT zero s _ _)
      (prf_congr_consT (substtc_inv_tcFn a s) (prf_substtc_varc0 s))
  -- (4) código: `nil˙ ⟶ ⌜nil⌝`
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_consT (prf_refl _) (prf_congr_consT (prf_refl _)
      (prf_congr_consT (prf_refl _) prf_tc_nil'))) (prf_refl _))) h3

end KitDev

#print axioms KitDev.pcc_dot_cons_symm
#print axioms KitDev.pcc_dot_nul
#print axioms KitDev.pcc_dot_un
#print axioms KitDev.pcc_dot_bin
