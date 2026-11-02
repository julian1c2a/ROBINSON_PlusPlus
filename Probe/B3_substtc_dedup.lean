/-
# `Probe/B3_substtc_dedup.lean` — AUDITORIA DE DUPLICACION de `sondeos/EvalSubsttc.lean`

**Angulo B de la rama B3.** No promueve nada: MIDE, y deja COMPILADO cada veredicto.

## Metodo (mecanizado, no por lectura)

1. Se copia el sondeo VERBATIM (md5 `7cfc61a8f12477b3dae118a136d5b904`, 1905 lineas), sin su
   bloque final de `#print axioms`/`#check`, para que sus 156 constantes existan en el entorno.
2. Un escaneo en `MetaM` compara CADA constante de `SFsubsttc` contra las 2552 constantes
   `ROBINSON_PlusPlus.*` + `FOL.*` del entorno: los TEOREMAS por `isDefEq` de su TIPO (el
   enunciado), y las DEFINICIONES por `isDefEq` de su VALOR — comparar TIPOS de `def`s no dice
   nada, porque todos los `Term -> Term -> Formula` tienen el mismo tipo.
3. Cada veredicto queda fijado aqui abajo con un PUENTE COMPILADO:
   * duplicado  ==>  `@SFsubsttc.X = @Produccion.Y := rfl`. Elabora SOLO si los dos tipos son
     defeq, y el `rfl` cierra por irrelevancia de pruebas bajo eta: que compile ES la
     afirmacion «MISMO ENUNCIADO», con otro nombre o no.
   * colision de nombre  ==>  `fail_if_success have : @SFsubsttc.X = @Produccion.X := rfl`,
     control negativo de que el homonimo de produccion dice OTRA cosa.

## Resultado en una linea

De las **156** declaraciones del sondeo, **69 son duplicados por ENUNCIADO** y **87 son nuevas**.
El reparto NO coincide con el reparto por NOMBRE: **17 de los 83 «ya estan por nombre» son
COLISIONES** (el homonimo de produccion habla de `liftc`, no de `substtc`), y en cambio **3 de
los 73 «faltan» ya estan, con OTRO nombre**.

Y el hallazgo caro: **el §13 entero del sondeo (8 declaraciones, ~85 lineas) esta MUERTO** —
`Meta/EvalPredPrf.lean` ya prueba `pcc_eval_pred` SIN la guarda `v < n`, o sea algo mas fuerte
que `PredHyp`. Ver §C y §D.
-/

/-
# `pcc_eval_substtc` — la evaluacion PROVABLE de `substtc` / `substtsc`.

Sigue el patron cerrado de `sondeos/DescensoLiftc.lean` (`pcc_eval_liftc`): UNA induccion
fuerte con conclusion CONJUNTIVA sobre los dos sorts (termino / lista de terminos).

Fichero AUTOCONTENIDO: `import ROBINSON_PlusPlus.Meta` y copia literal de lo que hace falta.

    lake env lean Probe/SF_substtc.lean
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf ROBINSON_PlusPlus.Meta.InAxiomsCodePrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf ROBINSON_PlusPlus.Meta.PropCodePrf
open ROBINSON_PlusPlus.Meta.NatMulPrf ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace SFsubsttc

/-! ############################################################################
    ## §1 · CONSTRUCTORES DE CODIGO (DEFINICIONES; ninguna ecuacion suya se postula)
    ############################################################################ -/

def substtcT (v s t : Term) : Term :=
  funcc (strCode "substtc") (cons v (cons s (cons t nil)))
def substtscT (v s ts : Term) : Term :=
  funcc (strCode "substtsc") (cons v (cons s (cons ts nil)))
/-- `varc x = cons 0 (cons x nil)` ⇒ su imagen punteada es el `unT 0` del KIT. -/
def varcT (X : Term) : Term := unT 0 X
/-- `funcc a b = cons 1 (cons a (cons b nil))` ⇒ su imagen punteada es `binT 1`. -/
def funccT (X Y : Term) : Term := binT 1 X Y
/-- Imagen punteada de `pred` (identica en forma a `succcT`). -/
def predcT (x : Term) : Term := funcc (strCode pred_sym) (cons x nil)

theorem substtcT_termCode (v s t : Term) :
    substtcT (termCode v) (termCode s) (termCode t) = termCode (substtc v s t) := rfl
theorem substtscT_termCode (v s t : Term) :
    substtscT (termCode v) (termCode s) (termCode t) = termCode (substtsc v s t) := rfl
theorem varcT_termCode (x : Term) : varcT (termCode x) = termCode (varc x) := rfl
theorem funccT_termCode (x y : Term) : funccT (termCode x) (termCode y) = termCode (funcc x y) :=
  rfl
theorem predcT_termCode (x : Term) : predcT (termCode x) = termCode (pred x) := rfl

theorem eqc_eq_eqCodeFn (a b : Term) : eqc a b = eqCodeFn a b := rfl

/-! ## §2 · Fontaneria basica: congruencias e invariancias -/

/-- Congruencia ternaria sobre `funcc` (injerto de `sondeos/Paso2CasoForall.lean:74`). -/
theorem prf_congr_funcc3 {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head hy)
      (prf_congr_cons_tail (prf_congr_cons_head hz)))))

/-- `substtc` sobre un `funcc` de **tres** argumentos. -/
theorem prf_substtc_funcc3 (v W sc x y z : Term) :
    Prf (substtc v W (funcc sc (cons x (cons y (cons z nil))))
      =eq funcc sc (cons (substtc v W x) (cons (substtc v W y) (cons (substtc v W z) nil)))) :=
  prf_eq_trans (prf_substtc_func v W sc (cons x (cons y (cons z nil))))
    (prf_congr_funcc2
      (prf_eq_trans (prf_substtsc_cons v W x (cons y (cons z nil)))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_substtsc_cons v W y (cons z nil))
            (prf_congr_cons_tail
              (prf_eq_trans (prf_substtsc_cons v W z nil)
                (prf_congr_cons_tail (prf_substtsc_nil v W))))))))

theorem prf_congr_substtcT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtcT v s t =eq substtcT v' s' t') := prf_congr_funcc3 hv hs ht
theorem prf_congr_substtscT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtscT v s t =eq substtscT v' s' t') := prf_congr_funcc3 hv hs ht
theorem prf_congr_varcT {X X' : Term} (h : Prf (X =eq X')) : Prf (varcT X =eq varcT X') :=
  prf_congr_unT h
theorem prf_congr_funccT {X X' Y Y' : Term} (hx : Prf (X =eq X')) (hy : Prf (Y =eq Y')) :
    Prf (funccT X Y =eq funccT X' Y') := prf_congr_binT hx hy
theorem prf_congr_predcT {x y : Term} (h : Prf (x =eq y)) : Prf (predcT x =eq predcT y) :=
  prf_congr_funcc2 (prf_congr_cons_head h)

theorem prf_substtc_substtcT (v W x y z : Term) :
    Prf (substtc v W (substtcT x y z)
      =eq substtcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtc") x y z
theorem prf_substtc_substtscT (v W x y z : Term) :
    Prf (substtc v W (substtscT x y z)
      =eq substtscT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtsc") x y z
theorem prf_substtc_predcT (v W x : Term) :
    Prf (substtc v W (predcT x) =eq predcT (substtc v W x)) :=
  prf_substtc_funcc1 v W (strCode pred_sym) x

theorem substtc_inv_substtcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtcT X Y Z) =eq substtcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substtcT zero W X Y Z) (prf_congr_substtcT (hX W) (hY W) (hZ W))
theorem substtc_inv_substtscT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtscT X Y Z) =eq substtscT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substtscT zero W X Y Z) (prf_congr_substtscT (hX W) (hY W) (hZ W))
theorem substtc_inv_predcT {X : Term} (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    ∀ W, Prf (substtc zero W (predcT X) =eq predcT X) := fun W =>
  prf_eq_trans (prf_substtc_predcT zero W X) (prf_congr_predcT (hX W))

/-! ### `substtc` a NIVEL ARBITRARIO sobre los codigos cerrados (copia de Paso2 §2) -/

theorem prf_substtc_termCode_closed (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) := by
  have h := prf_substtc_arith_open v W t
  rwa [substCodeT_closed v W t ht] at h

theorem prf_substtc_termCode_numeralM (v m : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  prf_substtc_termCode_closed v W (numeralM m) (fun c => liftTerm_numeralM c m)

theorem prf_substtc_termCode_zero (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  prf_substtc_termCode_closed v W zero (fun _ => rfl)

theorem prf_substtc_unT_at (m v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (unT m a) =eq unT m (substtc (numeral v) W a)) := by
  unfold unT consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v m W)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v W)))

theorem prf_substtc_binT_at (m v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (binT m a b)
      =eq binT m (substtc (numeral v) W a) (substtc (numeral v) W b)) := by
  unfold binT consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v m W)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v W)))

theorem prf_substtc_varcT_at (v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (varcT a) =eq varcT (substtc (numeral v) W a)) :=
  prf_substtc_unT_at 0 v W a
theorem prf_substtc_funccT_at (v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (funccT a b)
      =eq funccT (substtc (numeral v) W a) (substtc (numeral v) W b)) :=
  prf_substtc_binT_at 1 v W a b

/-! ## §3 · `pcc_axiom_inst4` — la pieza que faltaba (los dos axiomas clave son `forall_4`) -/

theorem pcc_thm_inst4 (φ : Formula) (h : Prf (forall_4 φ)) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (succ zero) (liftc zero w₃)
      (substfc (succ (succ zero)) (liftc zero (liftc zero w₂))
        (substfc (succ (succ (succ zero))) (liftc zero (liftc zero (liftc zero w₁)))
          (formCode φ)))))) := by
  have h3 : Prf (provFromCode (substfc zero w₃ (substfc (succ zero) (liftc zero w₂)
      (substfc (succ (succ zero)) (liftc zero (liftc zero w₁))
        (formCode (Formula.forall φ)))))) :=
    pcc_thm_inst3 (Formula.forall φ) h w₁ w₂ w₃
  -- empuja los tres `substfc` bajo el binder, uno a uno
  have e2 : Prf (substfc (succ (succ zero)) (liftc zero (liftc zero w₁))
        (forallc (formCode φ))
      =eq forallc (substfc (succ (succ (succ zero)))
        (liftc zero (liftc zero (liftc zero w₁))) (formCode φ))) :=
    prf_substfc_forall (succ (succ zero)) (liftc zero (liftc zero w₁)) (formCode φ)
  have h3' := prf_mp (prf_provCode_congr (prf_congr_substfc_arg3
    (prf_congr_substfc_arg3 e2))) h3
  have e1 : Prf (substfc (succ zero) (liftc zero w₂)
        (forallc (substfc (succ (succ (succ zero)))
          (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))
      =eq forallc (substfc (succ (succ zero)) (liftc zero (liftc zero w₂))
        (substfc (succ (succ (succ zero)))
          (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))) :=
    prf_substfc_forall (succ zero) (liftc zero w₂) _
  have h3'' := prf_mp (prf_provCode_congr (prf_congr_substfc_arg3 e1)) h3'
  have e0 : Prf (substfc zero w₃
        (forallc (substfc (succ (succ zero)) (liftc zero (liftc zero w₂))
          (substfc (succ (succ (succ zero)))
            (liftc zero (liftc zero (liftc zero w₁))) (formCode φ))))
      =eq forallc (substfc (succ zero) (liftc zero w₃)
        (substfc (succ (succ zero)) (liftc zero (liftc zero w₂))
          (substfc (succ (succ (succ zero)))
            (liftc zero (liftc zero (liftc zero w₁))) (formCode φ))))) :=
    prf_substfc_forall zero w₃ _
  have h3''' := prf_mp (prf_provCode_congr e0) h3''
  exact prf_mp (pcc_forallElim_code_open _ w₄) h3'''

theorem pcc_axiom_inst4 (φ : Formula) (hmem : forall_4 φ ∈ axioms) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (succ zero) (liftc zero w₃)
      (substfc (succ (succ zero)) (liftc zero (liftc zero w₂))
        (substfc (succ (succ (succ zero))) (liftc zero (liftc zero (liftc zero w₁)))
          (formCode φ)))))) :=
  pcc_thm_inst4 φ (prf_ax hmem) w₁ w₂ w₃ w₄

/-! ############################################################################
    ## §4 · LAS SEIS ECUACIONES DE `substtc`/`substtsc`, DOTADAS
    ############################################################################ -/

/-! ### (a) `ax_substtsc_nil` (`forall_2`) -/

def SUBSTTSC_NIL_BODY : Formula := substtsc (.var 1) (.var 0) nil =eq nil

theorem SUBSTTSC_NIL_BODY_ok : ax_substtsc_nil = forall_2 SUBSTTSC_NIL_BODY := rfl

theorem pcc_substtsc_nil_code (v s : Term) :
    Prf (provFromCode (eqCodeFn
      (substtscT (tcFn v) (tcFn s) (termCode nil)) (termCode nil))) := by
  let W1 : Term := liftc zero (tcFn v)
  let W0 : Term := tcFn s
  have hin : Prf (substfc (succ zero) W1 (formCode SUBSTTSC_NIL_BODY)
      =eq eqCodeFn (substtscT W1 (varc (numeral 0)) (termCode nil)) (termCode nil)) :=
    prf_substfc_arith_open 1 W1 SUBSTTSC_NIL_BODY
  have hA1 : Prf (W1 =eq tcFn v) := prf_liftc_tcFn v
  have hnorm : Prf (eqCodeFn (substtscT W1 (varc (numeral 0)) (termCode nil)) (termCode nil)
      =eq eqCodeFn (substtscT (tcFn v) (varc (numeral 0)) (termCode nil)) (termCode nil)) :=
    prf_congr_eqCodeFn (prf_congr_substtscT hA1 (prf_refl _) (prf_refl _)) (prf_refl _)
  have hout : Prf (substfc zero W0
        (eqCodeFn (substtscT (tcFn v) (varc (numeral 0)) (termCode nil)) (termCode nil))
      =eq eqCodeFn (substtscT (tcFn v) (tcFn s) (termCode nil)) (termCode nil)) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ (prf_substtc_termCode_zero 0 W0)
    exact prf_eq_trans (prf_substtc_substtscT zero W0 _ _ _)
      (prf_congr_substtscT (prf_substtc_tcFn W0 v) (prf_substtc_varc0 W0)
        (prf_substtc_termCode_zero 0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1 (formCode SUBSTTSC_NIL_BODY))
      =eq eqCodeFn (substtscT (tcFn v) (tcFn s) (termCode nil)) (termCode nil)) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst2 SUBSTTSC_NIL_BODY (show ax_substtsc_nil ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s))

/-! ### (b) `ax_substtc_func` (`forall_4`) -/

def SUBSTTC_FUNC_BODY : Formula :=
  substtc (.var 3) (.var 2) (funcc (.var 1) (.var 0))
    =eq funcc (.var 1) (substtsc (.var 3) (.var 2) (.var 0))

theorem SUBSTTC_FUNC_BODY_ok : ax_substtc_func = forall_4 SUBSTTC_FUNC_BODY := rfl

theorem pcc_substtc_func_code (v s p b : Term) :
    Prf (provFromCode (eqCodeFn
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))))) := by
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn p)
  let W0 : Term := tcFn b
  have hin : Prf (substfc (succ (succ (succ zero))) W3 (formCode SUBSTTC_FUNC_BODY)
      =eq eqCodeFn
        (substtcT W3 (varc (numeral 2)) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT W3 (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 3 W3 SUBSTTC_FUNC_BODY
  have hA3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_congr_liftc (prf_liftc_tcFn v)))
      (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v))
  have hnorm : Prf (eqCodeFn
        (substtcT W3 (varc (numeral 2)) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substtcT (tcFn v) (varc (numeral 2)) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_substtcT hA3 (prf_refl _) (prf_refl _))
      (prf_congr_funccT (prf_refl _) (prf_congr_substtscT hA3 (prf_refl _) (prf_refl _)))
  -- nivel 2 : `varc 2̄ ↦ ṡ`
  have hA2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have g2v2 : Prf (substtc (numeral 2) W2 (varc (numeral 2)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 2) W2 (numeral 2)) (prf_refl _)) hA2
  have g2v1 : Prf (substtc (numeral 2) W2 (varc (numeral 1)) =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 1)) (prf_gnum_lt (by omega))
  have g2v0 : Prf (substtc (numeral 2) W2 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 0)) (prf_gnum_lt (by omega))
  have g2tv : Prf (substtc (numeral 2) W2 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 2 W2 v
  have hL2 : Prf (substfc (numeral 2) W2 (eqCodeFn
        (substtcT (tcFn v) (varc (numeral 2)) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtcT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substtcT g2tv g2v2 ?_
      exact prf_eq_trans (prf_substtc_funccT_at 2 W2 _ _) (prf_congr_funccT g2v1 g2v0)
    · refine prf_eq_trans (prf_substtc_funccT_at 2 W2 _ _) ?_
      refine prf_congr_funccT g2v1 ?_
      exact prf_eq_trans (prf_substtc_substtscT (numeral 2) W2 _ _ _)
        (prf_congr_substtscT g2tv g2v2 g2v0)
  -- nivel 1 : `varc 1̄ ↦ ṗ`
  have hA1 : Prf (W1 =eq tcFn p) := prf_liftc_tcFn p
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn p) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have g1ts : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have hL1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (substtscT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (varc (numeral 0))))
        (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substtcT g1tv g1ts ?_
      exact prf_eq_trans (prf_substtc_funccT_at 1 W1 _ _) (prf_congr_funccT g1v1 g1v0)
    · refine prf_eq_trans (prf_substtc_funccT_at 1 W1 _ _) ?_
      refine prf_congr_funccT g1v1 ?_
      exact prf_eq_trans (prf_substtc_substtscT (numeral 1) W1 _ _ _)
        (prf_congr_substtscT g1tv g1ts g1v0)
  -- nivel 0 : `varc 0̄ ↦ ḃ`
  have hL0 : Prf (substfc zero W0 (eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (varc (numeral 0))))
        (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
        (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _) ?_
      refine prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
      exact prf_eq_trans (prf_substtc_funccT_at 0 W0 _ _)
        (prf_congr_funccT (prf_substtc_tcFn W0 p) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_funccT_at 0 W0 _ _) ?_
      refine prf_congr_funccT (prf_substtc_tcFn W0 p) ?_
      exact prf_eq_trans (prf_substtc_substtscT zero W0 _ _ _)
        (prf_congr_substtscT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s)
          (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2
          (substfc (succ (succ (succ zero))) W3 (formCode SUBSTTC_FUNC_BODY))))
      =eq eqCodeFn
        (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
        (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_congr_substfc_arg3
      (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm))))
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_congr_substfc_arg3 hL2))
        (prf_eq_trans (prf_congr_substfc_arg3 hL1) hL0))
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst4 SUBSTTC_FUNC_BODY (show ax_substtc_func ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn p) (tcFn b))

/-! ### (c) `ax_substtsc_cons` (`forall_4`) -/

def SUBSTTSC_CONS_BODY : Formula :=
  substtsc (.var 3) (.var 2) (cons (.var 1) (.var 0))
    =eq cons (substtc (.var 3) (.var 2) (.var 1)) (substtsc (.var 3) (.var 2) (.var 0))

theorem SUBSTTSC_CONS_BODY_ok : ax_substtsc_cons = forall_4 SUBSTTSC_CONS_BODY := rfl

theorem pcc_substtsc_cons_code (v s h t : Term) :
    Prf (provFromCode (eqCodeFn
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t))))) := by
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn h)
  let W0 : Term := tcFn t
  have hin : Prf (substfc (succ (succ (succ zero))) W3 (formCode SUBSTTSC_CONS_BODY)
      =eq eqCodeFn
        (substtscT W3 (varc (numeral 2)) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substtscT W3 (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 3 W3 SUBSTTSC_CONS_BODY
  have hA3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_congr_liftc (prf_liftc_tcFn v)))
      (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v))
  have hnorm : Prf (eqCodeFn
        (substtscT W3 (varc (numeral 2)) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substtscT W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substtscT (tcFn v) (varc (numeral 2)) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substtscT (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_substtscT hA3 (prf_refl _) (prf_refl _))
      (prf_congr_consT (prf_congr_substtcT hA3 (prf_refl _) (prf_refl _))
        (prf_congr_substtscT hA3 (prf_refl _) (prf_refl _)))
  have hA2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have g2v2 : Prf (substtc (numeral 2) W2 (varc (numeral 2)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 2) W2 (numeral 2)) (prf_refl _)) hA2
  have g2v1 : Prf (substtc (numeral 2) W2 (varc (numeral 1)) =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 1)) (prf_gnum_lt (by omega))
  have g2v0 : Prf (substtc (numeral 2) W2 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 0)) (prf_gnum_lt (by omega))
  have g2tv : Prf (substtc (numeral 2) W2 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 2 W2 v
  have hL2 : Prf (substfc (numeral 2) W2 (eqCodeFn
        (substtscT (tcFn v) (varc (numeral 2)) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substtscT (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substtscT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtscT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substtscT g2tv g2v2 ?_
      exact prf_eq_trans (prf_substtc_consT (numeral 2) W2 _ _) (prf_congr_consT g2v1 g2v0)
    · refine prf_eq_trans (prf_substtc_consT (numeral 2) W2 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_substtcT (numeral 2) W2 _ _ _)
          (prf_congr_substtcT g2tv g2v2 g2v1)
      · exact prf_eq_trans (prf_substtc_substtscT (numeral 2) W2 _ _ _)
          (prf_congr_substtscT g2tv g2v2 g2v0)
  have hA1 : Prf (W1 =eq tcFn h) := prf_liftc_tcFn h
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn h) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have g1ts : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have hL1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substtscT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
          (substtscT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtscT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substtscT g1tv g1ts ?_
      exact prf_eq_trans (prf_substtc_consT (numeral 1) W1 _ _) (prf_congr_consT g1v1 g1v0)
    · refine prf_eq_trans (prf_substtc_consT (numeral 1) W1 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _)
          (prf_congr_substtcT g1tv g1ts g1v1)
      · exact prf_eq_trans (prf_substtc_substtscT (numeral 1) W1 _ _ _)
          (prf_congr_substtscT g1tv g1ts g1v0)
  have hL0 : Prf (substfc zero W0 (eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (varc (numeral 0))))
        (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
          (substtscT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
        (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
          (substtscT (tcFn v) (tcFn s) (tcFn t)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substtscT zero W0 _ _ _) ?_
      refine prf_congr_substtscT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
      exact prf_eq_trans (prf_substtc_consT zero W0 _ _)
        (prf_congr_consT (prf_substtc_tcFn W0 h) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_consT zero W0 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _)
          (prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s)
            (prf_substtc_tcFn W0 h))
      · exact prf_eq_trans (prf_substtc_substtscT zero W0 _ _ _)
          (prf_congr_substtscT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s)
            (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2
          (substfc (succ (succ (succ zero))) W3 (formCode SUBSTTSC_CONS_BODY))))
      =eq eqCodeFn
        (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
        (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
          (substtscT (tcFn v) (tcFn s) (tcFn t)))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_congr_substfc_arg3
      (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm))))
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_congr_substfc_arg3 hL2))
        (prf_eq_trans (prf_congr_substfc_arg3 hL1) hL0))
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst4 SUBSTTSC_CONS_BODY (show ax_substtsc_cons ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn h) (tcFn t))

/-! ### (d) las TRES clausulas guardadas de `varc` (`forall_3`) -/

/-- `substfc` atraviesa un atomo binario de codigo (copia de `DescensoLiftc:251`). -/
theorem prf_substfc_atom2CodeFn (v t : Term) (s : String) (a b : Term) :
    Prf (substfc v t (atom2CodeFn s a b)
      =eq atom2CodeFn s (substtc v t a) (substtc v t b)) := by
  unfold atom2CodeFn
  refine prf_eq_trans (prf_substfc_atom v t (strCode s) (cons a (cons b nil))) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons v t a (cons b nil)) ?_
  exact prf_congr_cons_tail
    (prf_eq_trans (prf_substtsc_cons v t b nil) (prf_congr_cons_tail (prf_substtsc_nil v t)))

theorem prf_substfc_ltCodeFn' (v t a b : Term) :
    Prf (substfc v t (ltCodeFn a b) =eq ltCodeFn (substtc v t a) (substtc v t b)) :=
  prf_substfc_atom2CodeFn v t lt_sym a b

def SUBSTTC_VAR_EQ_BODY : Formula :=
  Formula.impl ((.var 2) =eq (.var 0))
    (substtc (.var 2) (.var 1) (varc (.var 0)) =eq (.var 1))
def SUBSTTC_VAR_GT_BODY : Formula :=
  Formula.impl (lt (.var 2) (.var 0))
    (substtc (.var 2) (.var 1) (varc (.var 0)) =eq varc (pred (.var 0)))
def SUBSTTC_VAR_LT_BODY : Formula :=
  Formula.impl (lt (.var 0) (.var 2))
    (substtc (.var 2) (.var 1) (varc (.var 0)) =eq varc (.var 0))

theorem SUBSTTC_VAR_EQ_BODY_ok : ax_substtc_var_eq = forall_3 SUBSTTC_VAR_EQ_BODY := rfl
theorem SUBSTTC_VAR_GT_BODY_ok : ax_substtc_var_gt = forall_3 SUBSTTC_VAR_GT_BODY := rfl
theorem SUBSTTC_VAR_LT_BODY_ok : ax_substtc_var_lt = forall_3 SUBSTTC_VAR_LT_BODY := rfl

theorem pcc_substtc_var_eq_code (v s n : Term) :
    Prf (provFromCode (implc (eqCodeFn (tcFn v) (tcFn n))
      (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn s)))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn v))
  let W1 : Term := liftc zero (tcFn s)
  let W0 : Term := tcFn n
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_EQ_BODY)
      =eq implc (eqCodeFn W2 (varc (numeral 0)))
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varc (numeral 1)))) :=
    prf_substfc_arith_open 2 W2 SUBSTTC_VAR_EQ_BODY
  have hA2 : Prf (W2 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)
  have hnorm : Prf (implc (eqCodeFn W2 (varc (numeral 0)))
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varc (numeral 1)))
      =eq implc (eqCodeFn (tcFn v) (varc (numeral 0)))
            (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varc (numeral 1)))) :=
    prf_congr_implc (prf_congr_eqCodeFn hA2 (prf_refl _))
      (prf_congr_eqCodeFn (prf_congr_substtcT hA2 (prf_refl _) (prf_refl _)) (prf_refl _))
  have hA1 : Prf (W1 =eq tcFn s) := prf_liftc_tcFn s
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have hL1 : Prf (substfc (numeral 1) W1
        (implc (eqCodeFn (tcFn v) (varc (numeral 0)))
          (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
            (varc (numeral 1))))
      =eq implc (eqCodeFn (tcFn v) (varc (numeral 0)))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0)))) (tcFn s))) := by
    refine prf_eq_trans (prf_substfc_impl (numeral 1) W1 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _)
        (prf_congr_eqCodeFn g1tv g1v0)
    · refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
      refine prf_congr_eqCodeFn ?_ g1v1
      refine prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substtcT g1tv g1v1 ?_
      exact prf_eq_trans (prf_substtc_varcT_at 1 W1 _) (prf_congr_varcT g1v0)
  have hL0 : Prf (substfc zero W0
        (implc (eqCodeFn (tcFn v) (varc (numeral 0)))
          (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0)))) (tcFn s)))
      =eq implc (eqCodeFn (tcFn v) (tcFn n))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn s))) := by
    refine prf_eq_trans (prf_substfc_impl zero W0 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_eq zero W0 _ _)
        (prf_congr_eqCodeFn (prf_substtc_tcFn W0 v) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
      refine prf_congr_eqCodeFn ?_ (prf_substtc_tcFn W0 s)
      refine prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _) ?_
      refine prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
      exact prf_eq_trans (prf_substtc_varcT_at 0 W0 _) (prf_congr_varcT (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_EQ_BODY)))
      =eq implc (eqCodeFn (tcFn v) (tcFn n))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn s))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hL1)) hL0
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 SUBSTTC_VAR_EQ_BODY (show ax_substtc_var_eq ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn n))

theorem pcc_substtc_var_gt_code (v s n : Term) :
    Prf (provFromCode (implc (ltCodeFn (tcFn v) (tcFn n))
      (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
        (varcT (predcT (tcFn n)))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn v))
  let W1 : Term := liftc zero (tcFn s)
  let W0 : Term := tcFn n
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_GT_BODY)
      =eq implc (ltCodeFn W2 (varc (numeral 0)))
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (predcT (varc (numeral 0)))))) :=
    prf_substfc_arith_open 2 W2 SUBSTTC_VAR_GT_BODY
  have hA2 : Prf (W2 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)
  have hnorm : Prf (implc (ltCodeFn W2 (varc (numeral 0)))
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (predcT (varc (numeral 0)))))
      =eq implc (ltCodeFn (tcFn v) (varc (numeral 0)))
            (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (predcT (varc (numeral 0)))))) :=
    prf_congr_implc (prf_congr_atom2CodeFn hA2 (prf_refl _))
      (prf_congr_eqCodeFn (prf_congr_substtcT hA2 (prf_refl _) (prf_refl _)) (prf_refl _))
  have hA1 : Prf (W1 =eq tcFn s) := prf_liftc_tcFn s
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have hL1 : Prf (substfc (numeral 1) W1
        (implc (ltCodeFn (tcFn v) (varc (numeral 0)))
          (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
            (varcT (predcT (varc (numeral 0))))))
      =eq implc (ltCodeFn (tcFn v) (varc (numeral 0)))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0))))
              (varcT (predcT (varc (numeral 0)))))) := by
    refine prf_eq_trans (prf_substfc_impl (numeral 1) W1 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_ltCodeFn' (numeral 1) W1 _ _)
        (prf_congr_atom2CodeFn g1tv g1v0)
    · refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _) ?_
        refine prf_congr_substtcT g1tv g1v1 ?_
        exact prf_eq_trans (prf_substtc_varcT_at 1 W1 _) (prf_congr_varcT g1v0)
      · refine prf_eq_trans (prf_substtc_varcT_at 1 W1 _) ?_
        refine prf_congr_varcT ?_
        exact prf_eq_trans (prf_substtc_predcT (numeral 1) W1 _) (prf_congr_predcT g1v0)
  have hL0 : Prf (substfc zero W0
        (implc (ltCodeFn (tcFn v) (varc (numeral 0)))
          (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0))))
            (varcT (predcT (varc (numeral 0))))))
      =eq implc (ltCodeFn (tcFn v) (tcFn n))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
              (varcT (predcT (tcFn n))))) := by
    refine prf_eq_trans (prf_substfc_impl zero W0 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_ltCodeFn' zero W0 _ _)
        (prf_congr_atom2CodeFn (prf_substtc_tcFn W0 v) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _) ?_
        refine prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
        exact prf_eq_trans (prf_substtc_varcT_at 0 W0 _) (prf_congr_varcT (prf_substtc_varc0 W0))
      · refine prf_eq_trans (prf_substtc_varcT_at 0 W0 _) ?_
        refine prf_congr_varcT ?_
        exact prf_eq_trans (prf_substtc_predcT zero W0 _)
          (prf_congr_predcT (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_GT_BODY)))
      =eq implc (ltCodeFn (tcFn v) (tcFn n))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
              (varcT (predcT (tcFn n))))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hL1)) hL0
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 SUBSTTC_VAR_GT_BODY (show ax_substtc_var_gt ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn n))

theorem pcc_substtc_var_lt_code (v s n : Term) :
    Prf (provFromCode (implc (ltCodeFn (tcFn n) (tcFn v))
      (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (tcFn n))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn v))
  let W1 : Term := liftc zero (tcFn s)
  let W0 : Term := tcFn n
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_LT_BODY)
      =eq implc (ltCodeFn (varc (numeral 0)) W2)
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (varc (numeral 0))))) :=
    prf_substfc_arith_open 2 W2 SUBSTTC_VAR_LT_BODY
  have hA2 : Prf (W2 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)
  have hnorm : Prf (implc (ltCodeFn (varc (numeral 0)) W2)
            (eqCodeFn (substtcT W2 (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (varc (numeral 0))))
      =eq implc (ltCodeFn (varc (numeral 0)) (tcFn v))
            (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
              (varcT (varc (numeral 0))))) :=
    prf_congr_implc (prf_congr_atom2CodeFn (prf_refl _) hA2)
      (prf_congr_eqCodeFn (prf_congr_substtcT hA2 (prf_refl _) (prf_refl _)) (prf_refl _))
  have hA1 : Prf (W1 =eq tcFn s) := prf_liftc_tcFn s
  have g1v1 : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) hA1
  have g1v0 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0)) (prf_gnum_lt (by omega))
  have g1tv : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have hL1 : Prf (substfc (numeral 1) W1
        (implc (ltCodeFn (varc (numeral 0)) (tcFn v))
          (eqCodeFn (substtcT (tcFn v) (varc (numeral 1)) (varcT (varc (numeral 0))))
            (varcT (varc (numeral 0)))))
      =eq implc (ltCodeFn (varc (numeral 0)) (tcFn v))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0))))
              (varcT (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_impl (numeral 1) W1 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_ltCodeFn' (numeral 1) W1 _ _)
        (prf_congr_atom2CodeFn g1v0 g1tv)
    · refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_substtcT (numeral 1) W1 _ _ _) ?_
        refine prf_congr_substtcT g1tv g1v1 ?_
        exact prf_eq_trans (prf_substtc_varcT_at 1 W1 _) (prf_congr_varcT g1v0)
      · exact prf_eq_trans (prf_substtc_varcT_at 1 W1 _) (prf_congr_varcT g1v0)
  have hL0 : Prf (substfc zero W0
        (implc (ltCodeFn (varc (numeral 0)) (tcFn v))
          (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (varc (numeral 0))))
            (varcT (varc (numeral 0)))))
      =eq implc (ltCodeFn (tcFn n) (tcFn v))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (tcFn n)))) := by
    refine prf_eq_trans (prf_substfc_impl zero W0 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · exact prf_eq_trans (prf_substfc_ltCodeFn' zero W0 _ _)
        (prf_congr_atom2CodeFn (prf_substtc_varc0 W0) (prf_substtc_tcFn W0 v))
    · refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_substtcT zero W0 _ _ _) ?_
        refine prf_congr_substtcT (prf_substtc_tcFn W0 v) (prf_substtc_tcFn W0 s) ?_
        exact prf_eq_trans (prf_substtc_varcT_at 0 W0 _) (prf_congr_varcT (prf_substtc_varc0 W0))
      · exact prf_eq_trans (prf_substtc_varcT_at 0 W0 _)
          (prf_congr_varcT (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2 (formCode SUBSTTC_VAR_LT_BODY)))
      =eq implc (ltCodeFn (tcFn n) (tcFn v))
            (eqCodeFn (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (tcFn n)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hL1)) hL0
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 SUBSTTC_VAR_LT_BODY (show ax_substtc_var_lt ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn n))

/-! ############################################################################
    ## §5 · EL OBJETIVO y las CONGRUENCIAS INTERNAS
    ############################################################################ -/

/-- El objetivo, con `v`, `s`, `X` **ABSTRACTOS**. -/
def targetSubsttc (v s X : Term) : Formula :=
  provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substtc v s X)))
/-- Su companera sobre LISTAS de codigos de termino. -/
def targetSubsttsc (v s X : Term) : Formula :=
  provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substtsc v s X)))

/-- CONTROL NEGATIVO: no es una reflexividad disfrazada. -/
example (v s X : Term) : True := by
  fail_if_success
    exact (rfl : substtcT (tcFn v) (tcFn s) (tcFn X) = tcFn (substtc v s X))
  trivial

theorem pcc_congr_substtcT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substtcT A B X) (substtcT A B Y))) := by
  let Ac : Term := eqc (substtcT A B X) (substtcT A B (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (substtcT A B X) (substtcT A B w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substtcT A B X)
      (substtcT A B (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substtcT zero w A B X)
        (prf_congr_substtcT (hA w) (hB w) (hX w))
    · exact prf_eq_trans (prf_substtc_substtcT zero w A B (varc (numeral 0)))
        (prf_congr_substtcT (hA w) (hB w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substtcT A B X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

theorem pcc_congr_substtscT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substtscT A B X) (substtscT A B Y))) := by
  let Ac : Term := eqc (substtscT A B X) (substtscT A B (varc (numeral 0)))
  have hcomp : ∀ w : Term,
      Prf (substfc zero w Ac =eq eqc (substtscT A B X) (substtscT A B w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substtscT A B X)
      (substtscT A B (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substtscT zero w A B X)
        (prf_congr_substtscT (hA w) (hB w) (hX w))
    · exact prf_eq_trans (prf_substtc_substtscT zero w A B (varc (numeral 0)))
        (prf_congr_substtscT (hA w) (hB w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substtscT A B X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- Congruencia interna en la CABEZA de `consT` (copia de `DescensoLiftc:508`). -/
theorem pcc_congr_consT_arg1_code (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT X B) (consT Y B))) := by
  let Ac : Term := eqc (consT X B) (consT (varc (numeral 0)) B)
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (consT X B) (consT w B)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (consT X B) (consT (varc (numeral 0)) B)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_consT zero w X B) (prf_congr_consT (hX w) (hB w))
    · exact prf_eq_trans (prf_substtc_consT zero w (varc (numeral 0)) B)
        (prf_congr_consT (prf_substtc_varc0 w) (hB w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (consT X B))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- Congruencia interna en la COLA de `consT`. -/
theorem pcc_congr_consT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT A X) (consT A Y))) := by
  let Ac : Term := eqc (consT A X) (consT A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (consT A X) (consT A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (consT A X) (consT A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_consT zero w A X) (prf_congr_consT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_consT zero w A (varc (numeral 0)))
        (prf_congr_consT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (consT A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-! ############################################################################
    ## §6 · LAS CLAUSULAS ESTRUCTURALES (`funcc`, `nil`, `cons`) — CERRADAS
    ############################################################################ -/

theorem invA (v s X : Term) :
    ∀ W, Prf (substtc zero W (substtcT (tcFn v) (tcFn s) (tcFn X))
      =eq substtcT (tcFn v) (tcFn s) (tcFn X)) :=
  substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn X)
theorem invAs (v s X : Term) :
    ∀ W, Prf (substtc zero W (substtscT (tcFn v) (tcFn s) (tcFn X))
      =eq substtscT (tcFn v) (tcFn s) (tcFn X)) :=
  substtc_inv_substtscT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn X)

/-- **(2) PASO `funcc`** — el unico salto: pide la companera sobre la LISTA de argumentos. -/
theorem refl_caso_funcc (v s X p b : Term) (hX : Prf (X =eq funcc p b))
    (hb : Prf (targetSubsttsc v s b)) : Prf (targetSubsttc v s X) := by
  unfold targetSubsttc
  unfold targetSubsttsc at hb
  have hplain : Prf (substtc v s X =eq funcc p (substtsc v s b)) :=
    prf_eq_trans (prf_congr_substtc3 hX) (prf_substtc_func v s p b)
  have hY : ∀ W, Prf (substtc zero W (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      =eq substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b))) :=
    substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn b))
  have hZ : ∀ W, Prf (substtc zero W (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))
      =eq funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn p) (invAs v s b)
  have s1 : Prf (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (funcc p b)))
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b))))) :=
    prf_mp (pcc_congr_substtcT_arg3_code (tcFn v) (tcFn s) (tcFn (funcc p b))
      (funccT (tcFn p) (tcFn b)) (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (funcc p b))) (pcc_dot_bin_symm 1 p b)
  have s2 : Prf (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))))) :=
    pcc_substtc_func_code v s p b
  have s3 : Prf (provFromCode (eqc
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))
      (funccT (tcFn p) (tcFn (substtsc v s b))))) :=
    prf_mp (pcc_congr_binT_2_code 1 (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))
      (tcFn (substtsc v s b)) (substtc_inv_tcFn p) (invAs v s b)) hb
  have s4 : Prf (provFromCode (eqc (funccT (tcFn p) (tcFn (substtsc v s b)))
      (tcFn (funcc p (substtsc v s b))))) := pcc_dot_bin 1 p (substtsc v s b)
  have hchain : Prf (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (funcc p b)))
      (tcFn (funcc p (substtsc v s b))))) :=
    pcc_eq_trans_code _ _ _ (invA v s (funcc p b)) s1
      (pcc_eq_trans_code _ _ _ hY s2 (pcc_eq_trans_code _ _ _ hZ s3 s4))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_substtcT (prf_refl _) (prf_refl _) (prf_congr_tcFn (prf_eq_symm hX)))
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-- **(3) BASE de la LISTA (`nil`) — CERRADA, sin hipotesis ninguna.** -/
theorem refl_lista_nil (v s : Term) : Prf (targetSubsttsc v s nil) := by
  unfold targetSubsttsc
  refine prf_mp (prf_provCode_congr (prf_congr_eqCodeFn ?_ ?_)) (pcc_substtsc_nil_code v s)
  · exact prf_congr_substtscT (prf_refl _) (prf_refl _) (prf_eq_symm prf_tc_zero)
  · exact prf_eq_trans (prf_eq_symm prf_tc_zero)
      (prf_congr_tcFn (prf_eq_symm (prf_substtsc_nil v s)))

/-- **(4) PASO de la LISTA (`cons`)** — pide la companera sobre la cabeza y sobre la cola. -/
theorem refl_lista_cons (v s h t : Term) (hh : Prf (targetSubsttc v s h))
    (ht : Prf (targetSubsttsc v s t)) : Prf (targetSubsttsc v s (cons h t)) := by
  unfold targetSubsttc at hh
  unfold targetSubsttsc at ht ⊢
  have hplain : Prf (substtsc v s (cons h t)
      =eq cons (substtc v s h) (substtsc v s t)) := prf_substtsc_cons v s h t
  have hY : ∀ W, Prf (substtc zero W (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
      =eq substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t))) :=
    substtc_inv_substtscT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t))
  have hZ : ∀ W, Prf (substtc zero W (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t)))
      =eq consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t))) :=
    substtc_inv_consT (invA v s h) (invAs v s t)
  have hU : ∀ W, Prf (substtc zero W (consT (tcFn (substtc v s h))
        (substtscT (tcFn v) (tcFn s) (tcFn t)))
      =eq consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_tcFn (substtc v s h)) (invAs v s t)
  have s1 : Prf (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (tcFn (cons h t)))
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t))))) :=
    prf_mp (pcc_congr_substtscT_arg3_code (tcFn v) (tcFn s) (tcFn (cons h t))
      (consT (tcFn h) (tcFn t)) (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons h t))) (pcc_dot_cons_symm h t)
  have s2 : Prf (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t))))) := pcc_substtsc_cons_code v s h t
  have s3 : Prf (provFromCode (eqc
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h)) (substtscT (tcFn v) (tcFn s) (tcFn t)))
      (consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t))))) :=
    prf_mp (pcc_congr_consT_arg1_code (substtscT (tcFn v) (tcFn s) (tcFn t))
      (substtcT (tcFn v) (tcFn s) (tcFn h)) (tcFn (substtc v s h))
      (invAs v s t) (invA v s h)) hh
  have s4 : Prf (provFromCode (eqc
      (consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t)))
      (consT (tcFn (substtc v s h)) (tcFn (substtsc v s t))))) :=
    prf_mp (pcc_congr_consT_arg2_code (tcFn (substtc v s h))
      (substtscT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtsc v s t))
      (substtc_inv_tcFn (substtc v s h)) (invAs v s t)) ht
  have s5 : Prf (provFromCode (eqc
      (consT (tcFn (substtc v s h)) (tcFn (substtsc v s t)))
      (tcFn (cons (substtc v s h) (substtsc v s t))))) :=
    pcc_dot_cons (substtc v s h) (substtsc v s t)
  have hchain : Prf (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (tcFn (cons h t)))
      (tcFn (cons (substtc v s h) (substtsc v s t))))) :=
    pcc_eq_trans_code _ _ _ (invAs v s (cons h t)) s1
      (pcc_eq_trans_code _ _ _ hY s2
        (pcc_eq_trans_code _ _ _ hZ s3 (pcc_eq_trans_code _ _ _ hU s4 s5)))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-! ############################################################################
    ## §7 · LA CLAUSULA `varc`: LA TRICOTOMIA, REFLEJADA DENTRO DE `Prov`
    ############################################################################

    Las tres clausulas de `substtc _ _ (varc n)` estan guardadas por `v ≐ n` / `v < n` / `n < v`
    con `v` **ABSTRACTO**. La tricotomia se elimina a nivel **OBJETO** (`prf_lt_trichotomy` +
    `Prfᵢ.j3`), y cada guarda se **refleja** dentro de `Prov`:
    * `<` por `pcc_lt_tracked` (produccion, argumentos ABIERTOS);
    * `=` por reflexividad codificada + Leibniz (`pcc_eq_tracked`, aqui abajo).

    ⚠️ ***NO hace falta un or-elim INTERNO*** (`pcc_or_elim_code`): la disyuncion se elimina
    FUERA de `Prov`, porque la conclusion `targetSubsttc` es la MISMA en las tres ramas. -/

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

/- ⛔ **RETIRADA 2026‑08‑31 — `pcc_eq_tracked` YA EXISTE EN PRODUCCIÓN.**

   Aquí había una copia local del reflector del átomo `=`. El agente que la escribió la
   declaró como pieza nueva; el verificador adversarial lo refutó y yo lo confirmé:
   está en `ROBINSON_PlusPlus/Meta/Sigma1AtomPrf.lean:246`, con enunciado **idéntico**
   (`Prf ((t =eq u) ⇒ provFromCode (eqCodeFn (tcFn t) (tcFn u)))`) y ya consumida en
   `Meta/InAxiomsCodePrf.lean:220`.

   La copia local la **SOMBREABA** — la trampa registrada de «misma definición en dos
   namespaces». Este fichero abre `Sigma1AtomPrf` en la línea 17, así que el uso de
   más abajo resuelve solo a la de producción. -/

/-- Rama `v < n` (clausula `ax_substtc_var_gt`). **La UNICA que necesita `pred` dotado.** -/
theorem br_lt (v s n : Term)
    (hPred : Prf (Formula.impl (lt v n)
      (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))) :
    Prf (Formula.impl (lt v n)
      (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
        (tcFn (substtc v s (varc n)))))) := by
  refine prf_deduction ?_
  have hg : PrfH [lt v n] (lt v n) := prfH_hyp_self _
  have hdotg : PrfH [lt v n] (provFromCode (ltCodeFn (tcFn v) (tcFn n))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked v n) _) hg
  have e1 : PrfH [lt v n] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (predcT (tcFn n))))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_substtc_var_gt_code v s n) _) hdotg
  have hpd : PrfH [lt v n] (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))) :=
    PrfH.mp _ _ _ (prf_to_prfH hPred _) hg
  have e2 : PrfH [lt v n] (provFromCode (eqc
      (varcT (predcT (tcFn n))) (varcT (tcFn (pred n))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_unT_code 0 (predcT (tcFn n)) (tcFn (pred n))
      (substtc_inv_predcT (substtc_inv_tcFn n))) _) hpd
  have e3 : PrfH [lt v n] (provFromCode (eqc (varcT (tcFn (pred n))) (tcFn (varc (pred n))))) :=
    prf_to_prfH (pcc_dot_un 0 (pred n)) _
  have hchain : PrfH [lt v n] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn (varc (pred n))))) :=
    PrfH_eq_trans_code _ _ _
      (substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
        (substtc_inv_unT (substtc_inv_tcFn n))) e1
      (PrfH_eq_trans_code _ _ _
        (substtc_inv_unT (substtc_inv_predcT (substtc_inv_tcFn n))) e2 e3)
  have hobj : PrfH [lt v n] (substtc v s (varc n) =eq varc (pred n)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_substtc_var_gt v s n) _) hg
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) (PrfH_congr_tcFn (PrfH_eq_symm hobj)))
    hchain

/-- Rama `v ≐ n` (clausula `ax_substtc_var_eq`). CERRADA, sin hipotesis. -/
theorem br_eq (v s n : Term) :
    Prf (Formula.impl (v =eq n)
      (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
        (tcFn (substtc v s (varc n)))))) := by
  refine prf_deduction ?_
  have hg : PrfH [v =eq n] (v =eq n) := prfH_hyp_self _
  have hdotg : PrfH [v =eq n] (provFromCode (eqCodeFn (tcFn v) (tcFn n))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked v n) _) hg
  have e1 : PrfH [v =eq n] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn s))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_substtc_var_eq_code v s n) _) hdotg
  have hobj : PrfH [v =eq n] (substtc v s (varc n) =eq s) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_substtc_var_eq v s n) _) hg
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) (PrfH_congr_tcFn (PrfH_eq_symm hobj)))
    e1

/-- Rama `n < v` (clausula `ax_substtc_var_lt`). CERRADA, sin hipotesis. -/
theorem br_gt (v s n : Term) :
    Prf (Formula.impl (lt n v)
      (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
        (tcFn (substtc v s (varc n)))))) := by
  refine prf_deduction ?_
  have hg : PrfH [lt n v] (lt n v) := prfH_hyp_self _
  have hdotg : PrfH [lt n v] (provFromCode (ltCodeFn (tcFn n) (tcFn v))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked n v) _) hg
  have e1 : PrfH [lt n v] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (varcT (tcFn n)))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_substtc_var_lt_code v s n) _) hdotg
  have e2 : PrfH [lt n v] (provFromCode (eqc (varcT (tcFn n)) (tcFn (varc n)))) :=
    prf_to_prfH (pcc_dot_un 0 n) _
  have hchain : PrfH [lt n v] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))) (tcFn (varc n)))) :=
    PrfH_eq_trans_code _ _ _
      (substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
        (substtc_inv_unT (substtc_inv_tcFn n))) e1 e2
  have hobj : PrfH [lt n v] (substtc v s (varc n) =eq varc n) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_substtc_var_lt v s n) _) hg
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _) (PrfH_congr_tcFn (PrfH_eq_symm hobj)))
    hchain

/-- **(1) BASE `varc`, con la TRICOTOMIA ya eliminada.** Unica hipotesis: `pred` dotado. -/
theorem refl_caso_varc_at (v s n : Term)
    (hPred : Prf (Formula.impl (lt v n)
      (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))) :
    Prf (targetSubsttc v s (varc n)) := by
  unfold targetSubsttc
  have s0 : Prf (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (varc n)))
      (substtcT (tcFn v) (tcFn s) (varcT (tcFn n))))) :=
    prf_mp (pcc_congr_substtcT_arg3_code (tcFn v) (tcFn s) (tcFn (varc n)) (varcT (tcFn n))
      (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn (varc n)))
      (pcc_dot_un_symm 0 n)
  have hmain : Prf (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (varcT (tcFn n)))
      (tcFn (substtc v s (varc n))))) :=
    prf_or_elim (prf_lt_trichotomy v n) (br_lt v s n hPred)
      (prf_or_elim_imp (br_eq v s n) (br_gt v s n))
  exact pcc_eq_trans_code _ _ _ (invA v s (varc n)) s0 hmain

/-- La forma que consume la induccion: la guarda llega como ecuacion PLANA `X ≐ varc n`. -/
theorem refl_caso_varc (v s X n : Term) (hX : Prf (X =eq varc n))
    (hPred : Prf (Formula.impl (lt v n)
      (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))) :
    Prf (targetSubsttc v s X) := by
  unfold targetSubsttc
  have h := refl_caso_varc_at v s n hPred
  unfold targetSubsttc at h
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_substtcT (prf_refl _) (prf_refl _) (prf_congr_tcFn (prf_eq_symm hX)))
    (prf_congr_tcFn (prf_eq_symm (prf_congr_substtc3 hX))))) h

/-! ############################################################################
    ## §8 · EL TESTIGO Y SU FONTANERIA — copia LITERAL de `sondeos/DescensoLiftc.lean`
       §B/§C/§D.1-§D.3 (es INDEPENDIENTE del objetivo: habla solo de codigos de TERMINO)
    ############################################################################ -/

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))
def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

theorem shapeUn0_es_varc (X : Term) :
    shapeUn X 0 = Formula.eq X (varc (nthc X (numeralM 1))) := rfl
theorem shapeBin1_es_funcc (X : Term) :
    shapeBin X 1 = Formula.eq X (funcc (nthc X (numeralM 1)) (nthc X (numeralM 2))) := rfl

def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))
def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))
def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)
def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons a b)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons a b)))

theorem PrfH_congr_lenc {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (lenc a =eq lenc b) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 a)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc a) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (lenc a)) Γ)

theorem PrfH_congr_nthc_lst {Γ : List Formula} {a b : Term} (i : Term) (h : PrfH Γ (a =eq b)) :
    PrfH Γ (nthc a i =eq nthc b i) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 a) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc a i) (nthc s i) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (nthc a i)) Γ)

theorem PrfH_congr_In_left {Γ : List Formula} {u v w : Term} (h : PrfH Γ (u =eq v))
    (hin : PrfH Γ (In u w)) : PrfH Γ (In v w) := by
  have hS : ∀ s : Term, substFormula 0 s (In (.var 0) (liftTerm 0 w)) = In s w := by
    intro s
    simp only [In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS v) ▸ PrfH_leibniz_subst (A := In (.var 0) (liftTerm 0 w)) h ((hS u) ▸ hin)

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

theorem substF_isTermCodeE1 (v : Nat) (s wT X : Term) :
    substFormula v s (isTermCodeE1 wT X)
      = isTermCodeE1 (substTerm v s wT) (substTerm v s X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, substFormula, substF_argsIn,
    nthc, cons, nil, zero, substTerm, substTerms, substTerm_numeralM]

theorem liftF_isTermCodeE1 (k : Nat) (wT X : Term) :
    liftFormula k (isTermCodeE1 wT X)
      = isTermCodeE1 (liftTerm k wT) (liftTerm k X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, liftFormula, liftF_argsIn,
    nthc, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]

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

theorem substF_isTC1 (v : Nat) (s w c : Term) :
    substFormula v s (isTC1 w c) = isTC1 (substTerm v s w) (substTerm v s c) := by
  simp only [isTC1, land, In, substFormula, substF_wfAll1, substTerm, substTerms]

theorem liftF_isTC1 (k : Nat) (w c : Term) :
    liftFormula k (isTC1 w c) = isTC1 (liftTerm k w) (liftTerm k c) := by
  simp only [isTC1, land, In, liftFormula, liftF_wfAll1, liftTerm, liftTerms]

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

theorem PrfH_inst_argsIn {Γ : List Formula} (wT Y i : Term) (h : PrfH Γ (argsIn wT Y)) :
    PrfH Γ (Formula.impl (lt i (lenc Y)) (In (nthc Y i) wT)) := by
  have hi := PrfH_spec h i
  simpa only [argsInBody, lt, lenc, nthc, In, substFormula, substTerm, substTerms,
    FOL.substTerm_liftTerm, if_true] using hi

theorem PrfH_inst_wfAll1 {Γ : List Formula} (w i : Term) (h : PrfH Γ (wfAll1 w)) :
    PrfH Γ (Formula.impl (lt i (lenc w)) (isTermCodeE1 w (nthc w i))) := by
  have hi := PrfH_spec h i
  simpa only [wfAll1Body, isTermCodeE1, shapeUn, shapeBin, argsIn, argsInBody, lor, land,
    lt, lenc, nthc, In, cons, nil, zero, substFormula, substTerm, substTerms,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceGT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_lift_comm_zero, substTerm_numeralM, if_true] using hi

theorem prf_orL {A B : Formula} (h : Prf A) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prfᵢ.j1 A B)) h
theorem prf_orR {A B : Formula} (h : Prf B) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prfᵢ.j2 A B)) h

/-! ### D.1 · `⊢ Y ≐ nil ∨ consOk Y` para `Y` ARBITRARIO -/

def nilOrCons : Formula := lor (Formula.eq (.var 0) nil) (consOk (.var 0))

theorem nilOrCons_at (Y : Term) :
    substFormula 0 Y nilOrCons = lor (Formula.eq Y nil) (consOk Y) := by
  simp only [nilOrCons, consOk, lor, carc, cdrc, cons, nil, zero, substFormula, substTerm,
    substTerms, if_true]

theorem prf_nil_or_cons_all : Prf (Formula.forall nilOrCons) := by
  refine prf_list_induction nilOrCons ?base ?step
  · rw [nilOrCons_at]
    exact prf_orL (prf_refl nil)
  · refine Prf.gen _ (Prf.gen _ ?_)
    have hR : substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 nilOrCons))
        = lor (Formula.eq (cons (.var 1) (.var 0)) nil) (consOk (cons (.var 1) (.var 0))) := by
      simp only [nilOrCons, consOk, lor, carc, cdrc, cons, nil, zero, liftFormula, substFormula,
        liftTerm, liftTerms, substTerm, substTerms, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT,
        reduceIte, if_true]
    rw [hR]
    exact prf_mp (Prf.incl (Prfᵢ.p1 _ _)) (prf_orR (prf_consOk_cons _ _))

theorem prf_nil_or_cons (Y : Term) : Prf (lor (Formula.eq Y nil) (consOk Y)) := by
  have h := prf_spec prf_nil_or_cons_all Y
  rwa [nilOrCons_at] at h

/-! ### D.2 · `argsIn` se hereda a la COLA -/

theorem prf_argsIn_tail (w hd tl : Term) :
    Prf (Formula.impl (argsIn w (cons hd tl)) (argsIn w tl)) := by
  refine prf_mp (Prf.qconf (argsIn w (cons hd tl)) (argsInBody w tl)) (Prf.gen _ ?_)
  rw [liftF_argsIn]
  refine prf_deduction (deduction_aux ?_ (lt (.var 0) (liftTerm 0 (lenc tl)))
    [argsIn (liftTerm 0 w) (liftTerm 0 (cons hd tl))] rfl)
  show PrfH [lt (.var 0) (lenc (liftTerm 0 tl)),
      argsIn (liftTerm 0 w) (cons (liftTerm 0 hd) (liftTerm 0 tl))]
    (In (nthc (liftTerm 0 tl) (.var 0)) (liftTerm 0 w))
  have hlt : PrfH [lt (.var 0) (lenc (liftTerm 0 tl)),
      argsIn (liftTerm 0 w) (cons (liftTerm 0 hd) (liftTerm 0 tl))]
      (lt (.var 0) (lenc (liftTerm 0 tl))) := PrfH.hyp _ _ (List.Mem.head _)
  have hargs : PrfH [lt (.var 0) (lenc (liftTerm 0 tl)),
      argsIn (liftTerm 0 w) (cons (liftTerm 0 hd) (liftTerm 0 tl))]
      (argsIn (liftTerm 0 w) (cons (liftTerm 0 hd) (liftTerm 0 tl))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt' : PrfH [lt (.var 0) (lenc (liftTerm 0 tl)),
      argsIn (liftTerm 0 w) (cons (liftTerm 0 hd) (liftTerm 0 tl))]
      (lt (succ (.var 0)) (lenc (cons (liftTerm 0 hd) (liftTerm 0 tl)))) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH (prf_eq_symm (prf_lenc_cons (liftTerm 0 hd) (liftTerm 0 tl))) _)
      (PrfH.mp _ _ _ (prf_to_prfH
        (prf_succ_lt_succ_of_lt (.var 0) (lenc (liftTerm 0 tl))) _) hlt)
  have hin : PrfH [lt (.var 0) (lenc (liftTerm 0 tl)),
      argsIn (liftTerm 0 w) (cons (liftTerm 0 hd) (liftTerm 0 tl))]
      (In (nthc (cons (liftTerm 0 hd) (liftTerm 0 tl)) (succ (.var 0))) (liftTerm 0 w)) :=
    PrfH.mp _ _ _ (PrfH_inst_argsIn (liftTerm 0 w) (cons (liftTerm 0 hd) (liftTerm 0 tl))
      (succ (.var 0)) hargs) hlt'
  exact PrfH_congr_In_left
    (prf_to_prfH (prf_nthc_succ (liftTerm 0 hd) (liftTerm 0 tl) (.var 0)) _) hin

/-! ### D.3 · Del testigo al NODO -/

theorem prf_isTermCodeE1_of_boundedIn (w c : Term) :
    Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula, liftF_wfAll1, liftF_isTermCodeE1]
  refine deduction_aux ?_ (wfAll1 (liftTerm 0 w)) _ rfl
  have hwf : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (wfAll1 (liftTerm 0 w)) := PrfH.hyp _ _ (List.Mem.head _)
  have hbody : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (lt (.var 0) (lenc (liftTerm 0 w))) := by
    have h := PrfH_and_elim_left hbody
    simpa only [lenc, liftTerm, liftTerms] using h
  have heq := PrfH_and_elim_right hbody
  have hitc := PrfH.mp _ _ _ (PrfH_inst_wfAll1 (liftTerm 0 w) (.var 0) hwf) hlt
  exact PrfH_congr_isTermCodeE1 heq hitc

theorem prf_isTermCodeE1_of_In (w c : Term) :
    Prf (Formula.impl (In c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) :=
  impT (prf_boundedIn_of_In c w) (prf_isTermCodeE1_of_boundedIn w c)

/-! ############################################################################
    ## §9 · `liftFormula`/`substFormula` atraviesan los dos objetivos
    ############################################################################ -/

theorem liftF_targetSubsttc (k : Nat) (v s X : Term) :
    liftFormula k (targetSubsttc v s X)
      = targetSubsttc (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [targetSubsttc, liftFormula_provFromCode_open, eqc, substtcT, funcc, tcFn, substtc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]

theorem liftF_targetSubsttsc (k : Nat) (v s X : Term) :
    liftFormula k (targetSubsttsc v s X)
      = targetSubsttsc (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [targetSubsttsc, liftFormula_provFromCode_open, eqc, substtscT, funcc, tcFn, substtsc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]

theorem substF_targetSubsttc (k : Nat) (u v s X : Term) :
    substFormula k u (targetSubsttc v s X)
      = targetSubsttc (substTerm k u v) (substTerm k u s) (substTerm k u X) := by
  simp only [targetSubsttc, substFormula_provFromCode_open, eqc, substtcT, funcc, tcFn, substtc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

theorem substF_targetSubsttsc (k : Nat) (u v s X : Term) :
    substFormula k u (targetSubsttsc v s X)
      = targetSubsttsc (substTerm k u v) (substTerm k u s) (substTerm k u X) := by
  simp only [targetSubsttsc, substFormula_provFromCode_open, eqc, substtscT, funcc, tcFn, substtsc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

theorem substF_hole_tc (v s u : Term) :
    substFormula 0 u (targetSubsttc (liftTerm 0 v) (liftTerm 0 s) (.var 0))
      = targetSubsttc v s u := by
  rw [substF_targetSubsttc]
  simp only [substTerm, FOL.substTerm_liftTerm, if_true]

theorem substF_hole_tsc (v s u : Term) :
    substFormula 0 u (targetSubsttsc (liftTerm 0 v) (liftTerm 0 s) (.var 0))
      = targetSubsttsc v s u := by
  rw [substF_targetSubsttsc]
  simp only [substTerm, FOL.substTerm_liftTerm, if_true]

theorem PrfH_congr_targetSubsttc {Γ : List Formula} {v s X X' : Term} (h : PrfH Γ (X =eq X'))
    (ha : PrfH Γ (targetSubsttc v s X)) : PrfH Γ (targetSubsttc v s X') :=
  (substF_hole_tc v s X') ▸
    PrfH_leibniz_subst (A := targetSubsttc (liftTerm 0 v) (liftTerm 0 s) (.var 0)) h
      ((substF_hole_tc v s X) ▸ ha)

theorem PrfH_congr_targetSubsttsc {Γ : List Formula} {v s X X' : Term} (h : PrfH Γ (X =eq X'))
    (ha : PrfH Γ (targetSubsttsc v s X)) : PrfH Γ (targetSubsttsc v s X') :=
  (substF_hole_tsc v s X') ▸
    PrfH_leibniz_subst (A := targetSubsttsc (liftTerm 0 v) (liftTerm 0 s) (.var 0)) h
      ((substF_hole_tsc v s X) ▸ ha)

/-! ## §10 · Las clausulas en forma IMPLICACION (la moneda de la induccion OBJETO) -/

/-- La UNICA hipotesis externa del frente: la evaluacion DOTADA de `pred`, en su forma
    GUARDADA (la mas debil que sirve). Otro agente la esta construyendo. -/
def PredHyp : Prop := ∀ v n : Term,
  Prf (Formula.impl (lt v n) (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))

theorem refl_shapeUn_imp (hP : PredHyp) (v s X : Term) :
    Prf (Formula.impl (shapeUn X 0) (targetSubsttc v s X)) := by
  refine prf_deduction ?_
  have hh : PrfH [shapeUn X 0] (Formula.eq X (varc (nthc X (numeralM 1)))) := prfH_hyp_self _
  exact PrfH_congr_targetSubsttc (PrfH_eq_symm hh)
    (prf_to_prfH (refl_caso_varc_at v s (nthc X (numeralM 1)) (hP v (nthc X (numeralM 1)))) _)

theorem refl_caso_funcc_imp (v s p b : Term) :
    Prf (Formula.impl (targetSubsttsc v s b) (targetSubsttc v s (funcc p b))) := by
  refine prf_deduction ?_
  have hb : PrfH [targetSubsttsc v s b] (targetSubsttsc v s b) := prfH_hyp_self _
  have hY : ∀ W, Prf (substtc zero W (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      =eq substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b))) :=
    substtc_inv_substtcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn b))
  have hZ : ∀ W, Prf (substtc zero W (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))
      =eq funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn p) (invAs v s b)
  have s1 : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (funcc p b)))
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b))))) :=
    prf_to_prfH (prf_mp (pcc_congr_substtcT_arg3_code (tcFn v) (tcFn s) (tcFn (funcc p b))
      (funccT (tcFn p) (tcFn b)) (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (funcc p b))) (pcc_dot_bin_symm 1 p b)) _
  have s2 : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b))))) :=
    prf_to_prfH (pcc_substtc_func_code v s p b) _
  have s3 : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (funccT (tcFn p) (substtscT (tcFn v) (tcFn s) (tcFn b)))
      (funccT (tcFn p) (tcFn (substtsc v s b))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code 1 (tcFn p)
      (substtscT (tcFn v) (tcFn s) (tcFn b)) (tcFn (substtsc v s b))
      (substtc_inv_tcFn p) (invAs v s b)) _) hb
  have s4 : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (funccT (tcFn p) (tcFn (substtsc v s b))) (tcFn (funcc p (substtsc v s b))))) :=
    prf_to_prfH (pcc_dot_bin 1 p (substtsc v s b)) _
  have hchain : PrfH [targetSubsttsc v s b] (provFromCode (eqc
      (substtcT (tcFn v) (tcFn s) (tcFn (funcc p b)))
      (tcFn (funcc p (substtsc v s b))))) :=
    PrfH_eq_trans_code _ _ _ (invA v s (funcc p b)) s1
      (PrfH_eq_trans_code _ _ _ hY s2 (PrfH_eq_trans_code _ _ _ hZ s3 s4))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_substtc_func v s p b))))) _) hchain

theorem refl_shapeBin_imp (v s X : Term) :
    Prf (Formula.impl (land (shapeBin X 1) (targetSubsttsc v s (nthc X (numeralM 2))))
      (targetSubsttc v s X)) := by
  refine prf_deduction ?_
  let p : Term := nthc X (numeralM 1)
  let b : Term := nthc X (numeralM 2)
  let H : Formula := land (shapeBin X 1) (targetSubsttsc v s b)
  have hh : PrfH [H] H := prfH_hyp_self _
  have hs : PrfH [H] (Formula.eq X (funcc p b)) := PrfH_and_elim_left hh
  have hbb : PrfH [H] (targetSubsttsc v s b) := PrfH_and_elim_right hh
  have hfb : PrfH [H] (targetSubsttc v s (funcc p b)) :=
    PrfH.mp _ _ _ (prf_to_prfH (refl_caso_funcc_imp v s p b) _) hbb
  exact PrfH_congr_targetSubsttc (PrfH_eq_symm hs) hfb

theorem refl_lista_cons_imp (v s h t : Term) :
    Prf (Formula.impl (land (targetSubsttc v s h) (targetSubsttsc v s t))
      (targetSubsttsc v s (cons h t))) := by
  refine prf_deduction ?_
  let H : Formula := land (targetSubsttc v s h) (targetSubsttsc v s t)
  have hh0 : PrfH [H] H := prfH_hyp_self _
  have hh : PrfH [H] (targetSubsttc v s h) := PrfH_and_elim_left hh0
  have ht : PrfH [H] (targetSubsttsc v s t) := PrfH_and_elim_right hh0
  have hY : ∀ W, Prf (substtc zero W (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
      =eq substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t))) :=
    substtc_inv_substtscT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t))
  have hZ : ∀ W, Prf (substtc zero W (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t)))
      =eq consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t))) :=
    substtc_inv_consT (invA v s h) (invAs v s t)
  have hU : ∀ W, Prf (substtc zero W (consT (tcFn (substtc v s h))
        (substtscT (tcFn v) (tcFn s) (tcFn t)))
      =eq consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_tcFn (substtc v s h)) (invAs v s t)
  have s1 : PrfH [H] (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (tcFn (cons h t)))
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t))))) :=
    prf_to_prfH (prf_mp (pcc_congr_substtscT_arg3_code (tcFn v) (tcFn s) (tcFn (cons h t))
      (consT (tcFn h) (tcFn t)) (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons h t))) (pcc_dot_cons_symm h t)) _
  have s2 : PrfH [H] (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (consT (tcFn h) (tcFn t)))
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h))
        (substtscT (tcFn v) (tcFn s) (tcFn t))))) :=
    prf_to_prfH (pcc_substtsc_cons_code v s h t) _
  have s3 : PrfH [H] (provFromCode (eqc
      (consT (substtcT (tcFn v) (tcFn s) (tcFn h)) (substtscT (tcFn v) (tcFn s) (tcFn t)))
      (consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_consT_arg1_code
      (substtscT (tcFn v) (tcFn s) (tcFn t)) (substtcT (tcFn v) (tcFn s) (tcFn h))
      (tcFn (substtc v s h)) (invAs v s t) (invA v s h)) _) hh
  have s4 : PrfH [H] (provFromCode (eqc
      (consT (tcFn (substtc v s h)) (substtscT (tcFn v) (tcFn s) (tcFn t)))
      (consT (tcFn (substtc v s h)) (tcFn (substtsc v s t))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_consT_arg2_code (tcFn (substtc v s h))
      (substtscT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtsc v s t))
      (substtc_inv_tcFn (substtc v s h)) (invAs v s t)) _) ht
  have s5 : PrfH [H] (provFromCode (eqc
      (consT (tcFn (substtc v s h)) (tcFn (substtsc v s t)))
      (tcFn (cons (substtc v s h) (substtsc v s t))))) :=
    prf_to_prfH (pcc_dot_cons (substtc v s h) (substtsc v s t)) _
  have hchain : PrfH [H] (provFromCode (eqc
      (substtscT (tcFn v) (tcFn s) (tcFn (cons h t)))
      (tcFn (cons (substtc v s h) (substtsc v s t))))) :=
    PrfH_eq_trans_code _ _ _ (invAs v s (cons h t)) s1
      (PrfH_eq_trans_code _ _ _ hY s2
        (PrfH_eq_trans_code _ _ _ hZ s3 (PrfH_eq_trans_code _ _ _ hU s4 s5)))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_substtsc_cons v s h t))))) _) hchain

/-! ############################################################################
    ## §11 · EL PREDICADO DE LA INDUCCION FUERTE — las DOS mitades y los DOS
       parametros `v`/`s`, todos CUANTIFICADOS DENTRO (lo exige `liftFormula 1 Φ = Φ`)
    ############################################################################ -/

def CONJ (w v s X : Term) : Formula :=
  land (Formula.impl (isTC1 w X) (targetSubsttc v s X))
       (Formula.impl (land (wfAll1 w) (argsIn w X)) (targetSubsttsc v s X))

theorem liftF_CONJ (k : Nat) (w v s X : Term) :
    liftFormula k (CONJ w v s X)
      = CONJ (liftTerm k w) (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [CONJ, land, liftFormula, liftF_isTC1, liftF_wfAll1, liftF_argsIn,
    liftF_targetSubsttc, liftF_targetSubsttsc]

theorem substF_CONJ (k : Nat) (u w v s X : Term) :
    substFormula k u (CONJ w v s X)
      = CONJ (substTerm k u w) (substTerm k u v) (substTerm k u s) (substTerm k u X) := by
  simp only [CONJ, land, substFormula, substF_isTC1, substF_wfAll1, substF_argsIn,
    substF_targetSubsttc, substF_targetSubsttsc]

/-- `#3` es el CODIGO sobre el que se induce; `#2` el testigo, `#1` = `v`, `#0` = `s`. -/
def PHIbody : Formula := CONJ (.var 2) (.var 1) (.var 0) (.var 3)
def PHI : Formula := Formula.forall (Formula.forall (Formula.forall PHIbody))

theorem hPHI1 : liftFormula 1 PHI = PHI := by
  simp only [PHI, PHIbody, liftFormula, liftF_CONJ, liftTerm, Nat.reduceAdd, Nat.reduceLT,
    reduceIte]

theorem PHI_at (t : Term) :
    substFormula 0 t PHI
      = Formula.forall (Formula.forall (Formula.forall
          (CONJ (.var 2) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [PHI, PHIbody, substFormula, substF_CONJ, substTerm, Nat.reduceAdd,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

theorem PHI_spec1 (t w : Term) :
    substFormula 0 w (Formula.forall (Formula.forall
        (CONJ (.var 2) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))
      = Formula.forall (Formula.forall
          (CONJ (liftTerm 0 (liftTerm 0 w)) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 t)))) := by
  simp only [substFormula, substF_CONJ, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true,
    ROBINSON_PlusPlus.Meta.SubstArith.substTerm_liftLiftLift]

theorem PHI_spec2 (t w v : Term) :
    substFormula 0 v (Formula.forall
        (CONJ (liftTerm 0 (liftTerm 0 w)) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t))))
      = Formula.forall (CONJ (liftTerm 0 w) (liftTerm 0 v) (.var 0) (liftTerm 0 t)) := by
  simp only [substFormula, substF_CONJ, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftLift]

theorem PHI_spec3 (t w v s : Term) :
    substFormula 0 s (CONJ (liftTerm 0 w) (liftTerm 0 v) (.var 0) (liftTerm 0 t))
      = CONJ w v s t := by
  simp only [substF_CONJ, substTerm, FOL.substTerm_liftTerm, if_true]

/-- Instanciacion de las DOS mitades a `w`, `v`, `s` concretos. -/
theorem PHI_use {Γ : List Formula} (t w v s : Term) (h : PrfH Γ (substFormula 0 t PHI)) :
    PrfH Γ (CONJ w v s t) := by
  rw [PHI_at] at h
  have h1 := PrfH_spec h w
  rw [PHI_spec1] at h1
  have h2 := PrfH_spec h1 v
  rw [PHI_spec2] at h2
  have h3 := PrfH_spec h2 s
  rwa [PHI_spec3] at h3

theorem psi_l1 : liftFormula 0 (PSI PHI)
    = Formula.forall (Formula.impl (lt (.var 0) (.var 2)) PHI) := by
  simp only [PSI, lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hPHI1]

theorem psi_l2 : liftFormula 0 (liftFormula 0 (PSI PHI))
    = Formula.forall (Formula.impl (lt (.var 0) (.var 3)) PHI) := by
  rw [psi_l1]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hPHI1]

theorem psi_l3 : liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))
    = Formula.forall (Formula.impl (lt (.var 0) (.var 4)) PHI) := by
  rw [psi_l2]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hPHI1]

def PSI3 : Formula := liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))

theorem PSI_inst {Γ : List Formula} (hpsi : PrfH Γ PSI3) (z : Term) :
    PrfH Γ (Formula.impl (lt z (.var 3)) (substFormula 0 z PHI)) := by
  unfold PSI3 at hpsi
  rw [psi_l3] at hpsi
  have h := PrfH_spec hpsi z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (.var 4)) PHI)
      = Formula.impl (lt z (.var 3)) (substFormula 0 z PHI) := by
    simp only [substFormula, lt, substTerm, substTerms, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, if_true]
  rwa [e] at h

/-! ### El PASO de la induccion fuerte -/

theorem PHI_step (hP : PredHyp) : Prf (Formula.forall (Formula.impl (PSI PHI) PHI)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHI] (Formula.forall (Formula.forall PHIbody)) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ (Formula.forall PHIbody) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ PHIbody ?_
  simp only [List.map_cons, List.map_nil]
  show PrfH [PSI3] PHIbody
  refine PrfH_and_intro ?half1 ?half2
  case half1 =>
    refine deduction_aux ?_ (isTC1 (.var 2) (.var 3)) [PSI3] rfl
    have hh : PrfH [isTC1 (.var 2) (.var 3), PSI3] (isTC1 (.var 2) (.var 3)) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hwf : PrfH [isTC1 (.var 2) (.var 3), PSI3] (wfAll1 (.var 2)) :=
      PrfH_and_elim_left hh
    have hin : PrfH [isTC1 (.var 2) (.var 3), PSI3] (In (.var 3) (.var 2)) :=
      PrfH_and_elim_right hh
    have hitc : PrfH [isTC1 (.var 2) (.var 3), PSI3]
        (isTermCodeE1 (.var 2) (.var 3)) :=
      PrfH.mp _ _ _ (PrfH.mp _ _ _
        (prf_to_prfH (prf_isTermCodeE1_of_In (.var 2) (.var 3)) _) hin) hwf
    refine PrfH_or_elim hitc ?varc ?func
    case varc =>
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeUn_imp hP (.var 1) (.var 0) (.var 3)) _)
        (PrfH.hyp _ _ (List.Mem.head _))
    case func =>
      have hb : PrfH [land (shapeBin (.var 3) 1)
            (argsIn (.var 2) (nthc (.var 3) (numeralM 2))),
          isTC1 (.var 2) (.var 3), PSI3]
          (land (shapeBin (.var 3) 1) (argsIn (.var 2) (nthc (.var 3) (numeralM 2)))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hwf' : PrfH [land (shapeBin (.var 3) 1)
            (argsIn (.var 2) (nthc (.var 3) (numeralM 2))),
          isTC1 (.var 2) (.var 3), PSI3] (wfAll1 (.var 2)) :=
        PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
      have hpsi' : PrfH [land (shapeBin (.var 3) 1)
            (argsIn (.var 2) (nthc (.var 3) (numeralM 2))),
          isTC1 (.var 2) (.var 3), PSI3] PSI3 :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hshape := PrfH_and_elim_left hb
      have hargs := PrfH_and_elim_right hb
      have h1 : Prf (lt (nthc (.var 3) (numeralM 2)) (cons (nthc (.var 3) (numeralM 2)) nil)) :=
        prf_cantor_mono_left _ _
      have h2 : Prf (lt (cons (nthc (.var 3) (numeralM 2)) nil)
          (cons (nthc (.var 3) (numeralM 1)) (cons (nthc (.var 3) (numeralM 2)) nil))) :=
        prf_cantor_mono_right _ _
      have h3 : Prf (lt (cons (nthc (.var 3) (numeralM 1))
            (cons (nthc (.var 3) (numeralM 2)) nil))
          (cons (numeralM 1) (cons (nthc (.var 3) (numeralM 1))
            (cons (nthc (.var 3) (numeralM 2)) nil)))) :=
        prf_cantor_mono_right _ _
      have h12 : Prf (lt (nthc (.var 3) (numeralM 2))
          (cons (nthc (.var 3) (numeralM 1)) (cons (nthc (.var 3) (numeralM 2)) nil))) :=
        prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
      have h123 : Prf (lt (nthc (.var 3) (numeralM 2))
          (cons (numeralM 1) (cons (nthc (.var 3) (numeralM 1))
            (cons (nthc (.var 3) (numeralM 2)) nil)))) :=
        prf_mp (prf_mp (prf_lt_trans _ _ _) h12) h3
      have hltb := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
        (PrfH_eq_symm hshape) (prf_to_prfH h123 _)
      have hphi := PrfH.mp _ _ _ (PSI_inst hpsi' (nthc (.var 3) (numeralM 2))) hltb
      have huse := PHI_use (nthc (.var 3) (numeralM 2)) (.var 2) (.var 1) (.var 0) hphi
      have htls := PrfH.mp _ _ _ (PrfH_and_elim_right huse) (PrfH_and_intro hwf' hargs)
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeBin_imp (.var 1) (.var 0) (.var 3)) _)
        (PrfH_and_intro hshape htls)
  case half2 =>
    refine deduction_aux ?_ (land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3))) [PSI3] rfl
    refine PrfH_or_elim (prf_to_prfH (prf_nil_or_cons (.var 3)) _) ?nilc ?consc
    case nilc =>
      have heq : PrfH [Formula.eq (.var 3) nil,
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSI3]
          (Formula.eq (.var 3) nil) := PrfH.hyp _ _ (List.Mem.head _)
      exact PrfH_congr_targetSubsttsc (PrfH_eq_symm heq)
        (prf_to_prfH (refl_lista_nil (.var 1) (.var 0)) _)
    case consc =>
      have hcons : PrfH [consOk (.var 3),
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSI3]
          (Formula.eq (.var 3) (cons (carc (.var 3)) (cdrc (.var 3)))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hh' : PrfH [consOk (.var 3),
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSI3]
          (land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3))) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
      have hpsi : PrfH [consOk (.var 3),
          land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3)), PSI3] PSI3 :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hwf := PrfH_and_elim_left hh'
      have hargs := PrfH_and_elim_right hh'
      -- (a) la CABEZA esta en el testigo y es MENOR
      have hlenX := PrfH_eq_trans (PrfH_congr_lenc hcons)
        (prf_to_prfH (prf_lenc_cons (carc (.var 3)) (cdrc (.var 3))) _)
      have hzlt := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
        (PrfH_eq_symm hlenX) (prf_to_prfH (prf_zero_lt_succ (lenc (cdrc (.var 3)))) _)
      have hin0 := PrfH.mp _ _ _ (PrfH_inst_argsIn (.var 2) (.var 3) zero hargs) hzlt
      have hnth0 := PrfH_eq_trans (PrfH_congr_nthc_lst zero hcons)
        (prf_to_prfH (prf_nthc_zero (carc (.var 3)) (cdrc (.var 3))) _)
      have hinhd := PrfH_congr_In_left hnth0 hin0
      have hlthd := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
        (prf_to_prfH (prf_cantor_mono_left (carc (.var 3)) (cdrc (.var 3))) _)
      have huse_hd := PHI_use (carc (.var 3)) (.var 2) (.var 1) (.var 0)
        (PrfH.mp _ _ _ (PSI_inst hpsi (carc (.var 3))) hlthd)
      have hTL_hd := PrfH.mp _ _ _ (PrfH_and_elim_left huse_hd) (PrfH_and_intro hwf hinhd)
      -- (b) la COLA hereda `argsIn` y es MENOR
      have hargs_cons := PrfH_congr_argsIn hcons hargs
      have hargs_tl := PrfH.mp _ _ _
        (prf_to_prfH (prf_argsIn_tail (.var 2) (carc (.var 3)) (cdrc (.var 3))) _) hargs_cons
      have hlttl := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
        (prf_to_prfH (prf_cantor_mono_right (carc (.var 3)) (cdrc (.var 3))) _)
      have huse_tl := PHI_use (cdrc (.var 3)) (.var 2) (.var 1) (.var 0)
        (PrfH.mp _ _ _ (PSI_inst hpsi (cdrc (.var 3))) hlttl)
      have hTLs_tl := PrfH.mp _ _ _ (PrfH_and_elim_right huse_tl) (PrfH_and_intro hwf hargs_tl)
      -- (c) el paso `cons` del reflector, y vuelta a `X` por Leibniz
      have hres := PrfH.mp _ _ _
        (prf_to_prfH (refl_lista_cons_imp (.var 1) (.var 0)
          (carc (.var 3)) (cdrc (.var 3))) _)
        (PrfH_and_intro hTL_hd hTLs_tl)
      exact PrfH_congr_targetSubsttsc (PrfH_eq_symm hcons) hres

/-! ### §12 · EL DESCENSO y `pcc_eval_substtc` -/

theorem PHI_all (hP : PredHyp) (t : Term) : Prf (substFormula 0 t PHI) :=
  prf_strong_induction PHI hPHI1 (PHI_step hP) t

theorem DESCENSO_imp (hP : PredHyp) (w v s t : Term) :
    Prf (Formula.impl (isTC1 w t) (targetSubsttc v s t)) :=
  prfH_nil_to_prf
    (PrfH_and_elim_left (PHI_use t w v s (prf_to_prfH (PHI_all hP t) []))) rfl

theorem DESCENSO_lista_imp (hP : PredHyp) (w v s t : Term) :
    Prf (Formula.impl (land (wfAll1 w) (argsIn w t)) (targetSubsttsc v s t)) :=
  prfH_nil_to_prf
    (PrfH_and_elim_right (PHI_use t w v s (prf_to_prfH (PHI_all hP t) []))) rfl

/-- **`pcc_eval_substtc`** — el objetivo del encargo, con `v`, `s`, `t` **ABSTRACTOS**
    y el testigo `w` como GUARDA (igual que `pcc_eval_liftc`). -/
theorem pcc_eval_substtc (hP : PredHyp) (w v s t : Term) (h : Prf (isTC1 w t)) :
    Prf (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtc v s t)))) :=
  prf_mp (DESCENSO_imp hP w v s t) h

/-- Su gemela sobre LISTAS de codigos de termino. -/
theorem pcc_eval_substtsc (hP : PredHyp) (w v s t : Term)
    (hwf : Prf (wfAll1 w)) (hargs : Prf (argsIn w t)) :
    Prf (provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn t))
      (tcFn (substtsc v s t)))) :=
  prf_mp (DESCENSO_lista_imp hP w v s t) (prf_and_intro hwf hargs)

/-- La forma que de verdad llega rio abajo: el testigo viene de un `∃`. -/
def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

theorem pcc_eval_substtc_hasWit (hP : PredHyp) (v s t : Term) :
    Prf (Formula.impl (hasWit t) (targetSubsttc v s t)) := by
  refine prf_ex_elim_imp ?_
  rw [liftF_targetSubsttc]
  exact PrfH.mp _ _ _
    (prf_to_prfH (DESCENSO_imp hP (.var 0) (liftTerm 0 v) (liftTerm 0 s) (liftTerm 0 t)) _)
    (prfH_hyp_self _)

/-! ############################################################################
    ## §13 · LA HIPOTESIS `PredHyp` SE DESCARGA — `pred` DOTADO bajo la guarda `v < n`.

    `v < n` da (por `ax13`) un testigo `k` con `v + σk = n`, o sea **`n` es un SUCESOR**
    (`prf_add_succ_t`). Y para un sucesor, `pred` dotado sale de **`ax26_pred_succ`
    instanciado DENTRO de `Prov`** (`pcc_axiom_inst`), sin induccion ninguna.
    ############################################################################ -/

def AX26_BODY : Formula := pred (succ (.var 0)) =eq (.var 0)

theorem AX26_BODY_ok : ax26_pred_succ = Formula.forall AX26_BODY := rfl

/-- **`ax26_pred_succ` DOTADA**: `⊢ Prov(⌜ pred(σ(ṁ)) = ṁ ⌝)`, con `m` **ABSTRACTO**. -/
theorem pcc_pred_succ_code (m : Term) :
    Prf (provFromCode (eqCodeFn (predcT (succcT (tcFn m))) (tcFn m))) := by
  have hin : Prf (substfc zero (tcFn m) (formCode AX26_BODY)
      =eq eqCodeFn (predcT (succcT (tcFn m))) (tcFn m)) :=
    prf_substfc_arith_open 0 (tcFn m) AX26_BODY
  exact prf_mp (prf_provCode_congr hin)
    (pcc_axiom_inst AX26_BODY (show ax26_pred_succ ∈ axioms by simp [axioms]) (tcFn m))

theorem PrfH_congr_pred {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (pred a =eq pred b) := by
  let f : Formula := Formula.eq (pred (liftTerm 0 a)) (pred (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (pred a) (pred s) := by
    intro s
    simp only [f, pred, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (pred a)) Γ)

theorem PrfH_congr_predcT {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (predcT a =eq predcT b) := by
  let f : Formula := Formula.eq (predcT (liftTerm 0 a)) (predcT (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (predcT a) (predcT s) := by
    intro s
    simp only [f, predcT, funcc, cons, nil, zero, succ, substFormula, substTerm, substTerms,
      substTerm_strCode, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (predcT a)) Γ)

theorem PrfH_pred_dot_of_succ {Γ : List Formula} (n m : Term) (h : PrfH Γ (n =eq succ m)) :
    PrfH Γ (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))) := by
  have e1 : PrfH Γ (predcT (tcFn n) =eq predcT (succcT (tcFn m))) :=
    PrfH_congr_predcT (PrfH_eq_trans (PrfH_congr_tcFn h) (prf_to_prfH (prf_tc_succ' m) _))
  have hpn : PrfH Γ (pred n =eq m) :=
    PrfH_eq_trans (PrfH_congr_pred h) (prf_to_prfH (prf_pred_succ m) _)
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_eq_symm e1) (PrfH_congr_tcFn (PrfH_eq_symm hpn)))
    (prf_to_prfH (pcc_pred_succ_code m) _)

theorem liftT_predcode (k : Nat) (n : Term) :
    liftTerm k (eqc (predcT (tcFn n)) (tcFn (pred n)))
      = eqc (predcT (tcFn (liftTerm k n))) (tcFn (pred (liftTerm k n))) := by
  simp only [eqc, predcT, funcc, tcFn, pred, cons, nil, zero, succ, liftTerm, liftTerms,
    liftTerm_strCode]

/-- **`PredHyp` DESCARGADA.** -/
theorem predHyp : PredHyp := by
  intro v n
  refine prf_deduction ?_
  have hiff : PrfH [lt v n]
      (Formula.ex (Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_lt_iff v n)) _) (prfH_hyp_self _)
  refine PrfH_ex_elim hiff ?_
  rw [liftFormula_provFromCode_open, liftT_predcode]
  have hh : PrfH [Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n),
      liftFormula 0 (lt v n)]
      (Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hsucc : PrfH [Formula.eq (add (liftTerm 0 v) (succ (.var 0))) (liftTerm 0 n),
      liftFormula 0 (lt v n)]
      (liftTerm 0 n =eq succ (add (liftTerm 0 v) (.var 0))) :=
    PrfH_eq_trans (PrfH_eq_symm hh)
      (prf_to_prfH (prf_add_succ_t (liftTerm 0 v) (.var 0)) _)
  exact PrfH_pred_dot_of_succ (liftTerm 0 n) (add (liftTerm 0 v) (.var 0)) hsucc

/-! ### §14 · EL TEOREMA, YA SIN NINGUNA HIPOTESIS EXTERNA -/

/-- **`pcc_eval_substtc`** — SIN hipotesis: la evaluacion PROVABLE de `substtc` con
    `v`, `s`, `t` **ABSTRACTOS**, guardada por el testigo `w` (igual que `pcc_eval_liftc`). -/
theorem pcc_eval_substtc' (w v s t : Term) (h : Prf (isTC1 w t)) :
    Prf (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn t)) (tcFn (substtc v s t)))) :=
  pcc_eval_substtc predHyp w v s t h

/-- Su gemela sobre LISTAS de codigos de termino, SIN hipotesis. -/
theorem pcc_eval_substtsc' (w v s t : Term)
    (hwf : Prf (wfAll1 w)) (hargs : Prf (argsIn w t)) :
    Prf (provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn t))
      (tcFn (substtsc v s t)))) :=
  pcc_eval_substtsc predHyp w v s t hwf hargs

/-- La forma con el testigo CUANTIFICADO (la que llega rio abajo), SIN hipotesis. -/
theorem pcc_eval_substtc_hasWit' (v s t : Term) :
    Prf (Formula.impl (hasWit t) (targetSubsttc v s t)) :=
  pcc_eval_substtc_hasWit predHyp v s t

end SFsubsttc



/-! ############################################################################
    # AUDITORIA — todo lo que sigue es del angulo B, no del sondeo
    ############################################################################ -/

namespace DEDUP

set_option linter.unusedVariables false

/-! ## §A · LOS 69 DUPLICADOS POR ENUNCIADO — puentes `rfl` COMPILADOS.

    `@A = @B := rfl` solo elabora si los TIPOS de `A` y `B` son definicionalmente iguales: es
    la prueba mecanica de «mismo enunciado», tengan el mismo nombre o no.
    **NINGUNO de estos 69 debe promoverse.** -/

/-- L49 - `varcT` (definicion) -/
theorem dup_49_varcT : @SFsubsttc.varcT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.varcT := rfl

/-- L51 - `funccT` (definicion) -/
theorem dup_51_funccT : @SFsubsttc.funccT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.funccT := rfl

/-- L53 - `predcT` (definicion) -/
theorem dup_53_predcT : @SFsubsttc.predcT = @ROBINSON_PlusPlus.Meta.EvalPredPrf.predcT := rfl

/-- L59 - `varcT_termCode` (teorema) -/
theorem dup_59_varcT_termCode : @SFsubsttc.varcT_termCode = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.varcT_termCode := rfl

/-- L60 - `funccT_termCode` (teorema) -/
theorem dup_60_funccT_termCode : @SFsubsttc.funccT_termCode = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.funccT_termCode := rfl

/-- L62 - `predcT_termCode` (teorema) -/
theorem dup_62_predcT_termCode : @SFsubsttc.predcT_termCode = @ROBINSON_PlusPlus.Meta.EvalPredPrf.predcT_termCode := rfl

/-- L64 - `eqc_eq_eqCodeFn` (teorema) -/
theorem dup_64_eqc_eq_eqCodeFn : @SFsubsttc.eqc_eq_eqCodeFn = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.eqc_eq_eqCodeFn_es_symm := rfl

/-- L96 - `prf_congr_varcT` (teorema) -/
theorem dup_96_prf_congr_varcT : @SFsubsttc.prf_congr_varcT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_congr_varcT := rfl

/-- L98 - `prf_congr_funccT` (teorema) -/
theorem dup_98_prf_congr_funccT : @SFsubsttc.prf_congr_funccT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_congr_funccT := rfl

/-- L100 - `prf_congr_predcT` (teorema) -/
theorem dup_100_prf_congr_predcT : @SFsubsttc.prf_congr_predcT = @ROBINSON_PlusPlus.Meta.EvalPredPrf.prf_congr_predcT := rfl

/-- L111 - `prf_substtc_predcT` (teorema) -/
theorem dup_111_prf_substtc_predcT : @SFsubsttc.prf_substtc_predcT = @ROBINSON_PlusPlus.Meta.EvalPredPrf.prf_substtc_predcT := rfl

/-- L125 - `substtc_inv_predcT` (teorema) -/
theorem dup_125_substtc_inv_predcT : @SFsubsttc.substtc_inv_predcT = @ROBINSON_PlusPlus.Meta.EvalPredPrf.substtc_inv_predcT := rfl

/-- L131 - `prf_substtc_termCode_closed` (teorema) -/
theorem dup_131_prf_substtc_termCode_closed : @SFsubsttc.prf_substtc_termCode_closed = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_closed := rfl

/-- L136 - `prf_substtc_termCode_numeralM` (teorema) -/
theorem dup_136_prf_substtc_termCode_numeralM : @SFsubsttc.prf_substtc_termCode_numeralM = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_numeralM := rfl

/-- L140 - `prf_substtc_termCode_zero` (teorema) -/
theorem dup_140_prf_substtc_termCode_zero : @SFsubsttc.prf_substtc_termCode_zero = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_zero := rfl

/-- L144 - `prf_substtc_unT_at` (teorema) -/
theorem dup_144_prf_substtc_unT_at : @SFsubsttc.prf_substtc_unT_at = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_unT_at := rfl

/-- L155 - `prf_substtc_binT_at` (teorema) -/
theorem dup_155_prf_substtc_binT_at : @SFsubsttc.prf_substtc_binT_at = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_binT_at := rfl

/-- L170 - `prf_substtc_varcT_at` (teorema) -/
theorem dup_170_prf_substtc_varcT_at : @SFsubsttc.prf_substtc_varcT_at = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_varcT_at := rfl

/-- L173 - `prf_substtc_funccT_at` (teorema) -/
theorem dup_173_prf_substtc_funccT_at : @SFsubsttc.prf_substtc_funccT_at = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_funccT_at := rfl

/-- L180 - `pcc_thm_inst4` (teorema) -/
theorem dup_180_pcc_thm_inst4 : @SFsubsttc.pcc_thm_inst4 = @ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_thm_inst4 := rfl

/-- L217 - `pcc_axiom_inst4` (teorema) -/
theorem dup_217_pcc_axiom_inst4 : @SFsubsttc.pcc_axiom_inst4 = @ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_axiom_inst4 := rfl

/-- L504 - `prf_substfc_atom2CodeFn` (teorema) -/
theorem dup_504_prf_substfc_atom2CodeFn : @SFsubsttc.prf_substfc_atom2CodeFn = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substfc_atom2CodeFn := rfl

/-- L514 - `prf_substfc_ltCodeFn'` (teorema) -/
theorem dup_514_prf_substfc_ltCodeFn_p : @SFsubsttc.prf_substfc_ltCodeFn' = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substfc_ltCodeFn' := rfl

/-- L808 - `pcc_congr_consT_arg1_code` (teorema) -/
theorem dup_808_pcc_congr_consT_arg1_code : @SFsubsttc.pcc_congr_consT_arg1_code = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_consT_arg1_code := rfl

/-- L827 - `pcc_congr_consT_arg2_code` (teorema) -/
theorem dup_827_pcc_congr_consT_arg2_code : @SFsubsttc.pcc_congr_consT_arg2_code = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_consT_arg2_code := rfl

/-- L974 - `prf_or_elim_imp` (teorema) -/
theorem dup_974_prf_or_elim_imp : @SFsubsttc.prf_or_elim_imp = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_or_elim_imp := rfl

/-- L1106 - `shapeUn` (definicion) -/
theorem dup_1106_shapeUn : @SFsubsttc.shapeUn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeUn := rfl

/-- L1108 - `shapeBin` (definicion) -/
theorem dup_1108_shapeBin : @SFsubsttc.shapeBin = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeBin := rfl

/-- L1112 - `shapeUn0_es_varc` (teorema) -/
theorem dup_1112_shapeUn0_es_varc : @SFsubsttc.shapeUn0_es_varc = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.shapeUn0_es_varc := rfl

/-- L1114 - `shapeBin1_es_funcc` (teorema) -/
theorem dup_1114_shapeBin1_es_funcc : @SFsubsttc.shapeBin1_es_funcc = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.shapeBin1_es_funcc := rfl

/-- L1117 - `argsInBody` (definicion) -/
theorem dup_1117_argsInBody : @SFsubsttc.argsInBody = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsInBody := rfl

/-- L1120 - `argsIn` (definicion) -/
theorem dup_1120_argsIn : @SFsubsttc.argsIn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsIn := rfl

/-- L1122 - `isTermCodeE1` (definicion) -/
theorem dup_1122_isTermCodeE1 : @SFsubsttc.isTermCodeE1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTermCodeE1 := rfl

/-- L1125 - `impT` (teorema) -/
theorem dup_1125_impT : @SFsubsttc.impT = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT := rfl

/-- L1129 - `prf_cdrc_cons` (teorema) -/
theorem dup_1129_prf_cdrc_cons : @SFsubsttc.prf_cdrc_cons = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_cdrc_cons := rfl

/-- L1135 - `consOk` (definicion) -/
theorem dup_1135_consOk : @SFsubsttc.consOk = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.consOk := rfl

/-- L1137 - `wfAll1Body` (definicion) -/
theorem dup_1137_wfAll1Body : @SFsubsttc.wfAll1Body = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.wfAll1Body := rfl

/-- L1140 - `wfAll1` (definicion) -/
theorem dup_1140_wfAll1 : @SFsubsttc.wfAll1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.wfAll1 := rfl

/-- L1141 - `isTC1` (definicion) -/
theorem dup_1141_isTC1 : @SFsubsttc.isTC1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTC1 := rfl

/-- L1143 - `prf_consOk_cons` (teorema) -/
theorem dup_1143_prf_consOk_cons : @SFsubsttc.prf_consOk_cons = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_consOk_cons := rfl

/-- L1147 - `PrfH_congr_lenc` (teorema) -/
theorem dup_1147_PrfH_congr_lenc : @SFsubsttc.PrfH_congr_lenc = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_lenc := rfl

/-- L1155 - `PrfH_congr_nthc_lst` (teorema) -/
theorem dup_1155_PrfH_congr_nthc_lst : @SFsubsttc.PrfH_congr_nthc_lst = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_nthc_lst := rfl

/-- L1163 - `PrfH_congr_In_left` (teorema) -/
theorem dup_1163_PrfH_congr_In_left : @SFsubsttc.PrfH_congr_In_left = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_In_left := rfl

/-- L1170 - `liftF_argsIn` (teorema) -/
theorem dup_1170_liftF_argsIn : @SFsubsttc.liftF_argsIn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_argsIn := rfl

/-- L1175 - `substF_argsIn` (teorema) -/
theorem dup_1175_substF_argsIn : @SFsubsttc.substF_argsIn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.substF_argsIn := rfl

/-- L1183 - `substF_isTermCodeE1` (teorema) -/
theorem dup_1183_substF_isTermCodeE1 : @SFsubsttc.substF_isTermCodeE1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.substF_isTermCodeE1 := rfl

/-- L1189 - `liftF_isTermCodeE1` (teorema) -/
theorem dup_1189_liftF_isTermCodeE1 : @SFsubsttc.liftF_isTermCodeE1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_isTermCodeE1 := rfl

/-- L1195 - `liftF_wfAll1` (teorema) -/
theorem dup_1195_liftF_wfAll1 : @SFsubsttc.liftF_wfAll1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.liftF_wfAll1 := rfl

/-- L1200 - `substF_wfAll1` (teorema) -/
theorem dup_1200_substF_wfAll1 : @SFsubsttc.substF_wfAll1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.substF_wfAll1 := rfl

/-- L1208 - `substF_isTC1` (teorema) -/
theorem dup_1208_substF_isTC1 : @SFsubsttc.substF_isTC1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.substF_isTC1 := rfl

/-- L1212 - `liftF_isTC1` (teorema) -/
theorem dup_1212_liftF_isTC1 : @SFsubsttc.liftF_isTC1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.liftF_isTC1 := rfl

/-- L1216 - `PrfH_congr_argsIn` (teorema) -/
theorem dup_1216_PrfH_congr_argsIn : @SFsubsttc.PrfH_congr_argsIn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_argsIn := rfl

/-- L1223 - `PrfH_congr_isTermCodeE1` (teorema) -/
theorem dup_1223_PrfH_congr_isTermCodeE1 : @SFsubsttc.PrfH_congr_isTermCodeE1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_isTermCodeE1 := rfl

/-- L1231 - `PrfH_inst_argsIn` (teorema) -/
theorem dup_1231_PrfH_inst_argsIn : @SFsubsttc.PrfH_inst_argsIn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_inst_argsIn := rfl

/-- L1237 - `PrfH_inst_wfAll1` (teorema) -/
theorem dup_1237_PrfH_inst_wfAll1 : @SFsubsttc.PrfH_inst_wfAll1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_inst_wfAll1 := rfl

/-- L1245 - `prf_orL` (teorema) -/
theorem dup_1245_prf_orL : @SFsubsttc.prf_orL = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_orL := rfl

/-- L1247 - `prf_orR` (teorema) -/
theorem dup_1247_prf_orR : @SFsubsttc.prf_orR = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_orR := rfl

/-- L1252 - `nilOrCons` (definicion) -/
theorem dup_1252_nilOrCons : @SFsubsttc.nilOrCons = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.nilOrCons := rfl

/-- L1254 - `nilOrCons_at` (teorema) -/
theorem dup_1254_nilOrCons_at : @SFsubsttc.nilOrCons_at = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.nilOrCons_at := rfl

/-- L1259 - `prf_nil_or_cons_all` (teorema) -/
theorem dup_1259_prf_nil_or_cons_all : @SFsubsttc.prf_nil_or_cons_all = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons_all := rfl

/-- L1272 - `prf_nil_or_cons` (teorema) -/
theorem dup_1272_prf_nil_or_cons : @SFsubsttc.prf_nil_or_cons = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons := rfl

/-- L1278 - `prf_argsIn_tail` (teorema) -/
theorem dup_1278_prf_argsIn_tail : @SFsubsttc.prf_argsIn_tail = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_tail := rfl

/-- L1311 - `prf_isTermCodeE1_of_boundedIn` (teorema) -/
theorem dup_1311_prf_isTermCodeE1_of_boundedIn : @SFsubsttc.prf_isTermCodeE1_of_boundedIn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_boundedIn := rfl

/-- L1336 - `prf_isTermCodeE1_of_In` (teorema) -/
theorem dup_1336_prf_isTermCodeE1_of_In : @SFsubsttc.prf_isTermCodeE1_of_In = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_In := rfl

/-- L1765 - `hasWit` (definicion) -/
theorem dup_1765_hasWit : @SFsubsttc.hasWit = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.hasWit := rfl

/-- L1783 - `AX26_BODY` (definicion) -/
theorem dup_1783_AX26_BODY : @SFsubsttc.AX26_BODY = @ROBINSON_PlusPlus.Meta.EvalPredPrf.AX26_BODY := rfl

/-- L1785 - `AX26_BODY_ok` (teorema) -/
theorem dup_1785_AX26_BODY_ok : @SFsubsttc.AX26_BODY_ok = @ROBINSON_PlusPlus.Meta.EvalPredPrf.AX26_BODY_ok := rfl

/-- L1796 - `PrfH_congr_pred` (teorema) -/
theorem dup_1796_PrfH_congr_pred : @SFsubsttc.PrfH_congr_pred = @ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_eq_congr_pred := rfl

/-- L1823 - `liftT_predcode` (teorema) -/
theorem dup_1823_liftT_predcode : @SFsubsttc.liftT_predcode = @ROBINSON_PlusPlus.Meta.EvalPredPrf.liftTerm_evalPredCode := rfl


/-! ## §B · LAS 17 COLISIONES DE NOMBRE — el homonimo de produccion NO dice lo mismo.

    Estas 17 SI son contenido nuevo. Coinciden en NOMBRE con lemas de `LiftcCodePrf` /
    `EvalLiftcPrf` / `StrongInductionPrf` que hablan de `liftc` (o de OTRO `PHI`), no de
    `substtc`. **Al promover hay que renombrarlas**, porque el modulo destino abrira los dos
    namespaces y el nombre corto quedara ambiguo.

    Control negativo: cada `fail_if_success` de abajo compila **porque el puente falla**. -/

/-- L859 - `refl_caso_funcc` - homonimo en `ROBINSON_PlusPlus/Meta/LiftcCodePrf.lean:647`. -/
example : True := by
  fail_if_success have : @SFsubsttc.refl_caso_funcc = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc := rfl
  trivial

/-- L899 - `refl_lista_nil` - homonimo en `ROBINSON_PlusPlus/Meta/LiftcCodePrf.lean:688`. -/
example : True := by
  fail_if_success have : @SFsubsttc.refl_lista_nil = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil := rfl
  trivial

/-- L907 - `refl_lista_cons` - homonimo en `ROBINSON_PlusPlus/Meta/LiftcCodePrf.lean:694`. -/
example : True := by
  fail_if_success have : @SFsubsttc.refl_lista_cons = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons := rfl
  trivial

/-- L1090 - `refl_caso_varc` - homonimo en `ROBINSON_PlusPlus/Meta/LiftcCodePrf.lean:619`. -/
example : True := by
  fail_if_success have : @SFsubsttc.refl_caso_varc = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_varc := rfl
  trivial

/-- L1399 - `refl_shapeUn_imp` - homonimo en `ROBINSON_PlusPlus/Meta/LiftcCodePrf.lean:836`. -/
example : True := by
  fail_if_success have : @SFsubsttc.refl_shapeUn_imp = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp := rfl
  trivial

/-- L1406 - `refl_caso_funcc_imp` - homonimo en `ROBINSON_PlusPlus/Meta/LiftcCodePrf.lean:850`. -/
example : True := by
  fail_if_success have : @SFsubsttc.refl_caso_funcc_imp = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc_imp := rfl
  trivial

/-- L1444 - `refl_shapeBin_imp` - homonimo en `ROBINSON_PlusPlus/Meta/LiftcCodePrf.lean:891`. -/
example : True := by
  fail_if_success have : @SFsubsttc.refl_shapeBin_imp = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeBin_imp := rfl
  trivial

/-- L1458 - `refl_lista_cons_imp` - homonimo en `ROBINSON_PlusPlus/Meta/LiftcCodePrf.lean:906`. -/
example : True := by
  fail_if_success have : @SFsubsttc.refl_lista_cons_imp = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_imp := rfl
  trivial

/-- L1537 - `PHIbody` - homonimo en `ROBINSON_PlusPlus/Meta/EvalLiftcPrf.lean:349`. -/
example : True := by
  fail_if_success have : @SFsubsttc.PHIbody = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHIbody := rfl
  trivial

/-- L1538 - `PHI` - homonimo en `ROBINSON_PlusPlus/Meta/EvalLiftcPrf.lean:354`. -/
example : True := by
  fail_if_success have : @SFsubsttc.PHI = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI := rfl
  trivial

/-- L1544 - `PHI_at` - homonimo en `ROBINSON_PlusPlus/Meta/EvalLiftcPrf.lean:360`. -/
example : True := by
  fail_if_success have : @SFsubsttc.PHI_at = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_at := rfl
  trivial

/-- L1575 - `PHI_use` - homonimo en `ROBINSON_PlusPlus/Meta/EvalLiftcPrf.lean:370`. -/
example : True := by
  fail_if_success have : @SFsubsttc.PHI_use = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_use := rfl
  trivial

/-- L1604 - `PSI_inst` - homonimo en `ROBINSON_PlusPlus/Meta/StrongInductionPrf.lean:203`. -/
example : True := by
  fail_if_success have : @SFsubsttc.PSI_inst = @ROBINSON_PlusPlus.Meta.StrongInductionPrf.PSI_inst := rfl
  trivial

/-- L1617 - `PHI_step` - homonimo en `ROBINSON_PlusPlus/Meta/EvalLiftcPrf.lean:396`. -/
example : True := by
  fail_if_success have : @SFsubsttc.PHI_step = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_step := rfl
  trivial

/-- L1738 - `PHI_all` - homonimo en `ROBINSON_PlusPlus/Meta/EvalLiftcPrf.lean:515`. -/
example : True := by
  fail_if_success have : @SFsubsttc.PHI_all = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_all := rfl
  trivial

/-- L1741 - `DESCENSO_imp` - homonimo en `ROBINSON_PlusPlus/Meta/EvalLiftcPrf.lean:519`. -/
example : True := by
  fail_if_success have : @SFsubsttc.DESCENSO_imp = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_imp := rfl
  trivial

/-- L1746 - `DESCENSO_lista_imp` - homonimo en `ROBINSON_PlusPlus/Meta/EvalLiftcPrf.lean:523`. -/
example : True := by
  fail_if_success have : @SFsubsttc.DESCENSO_lista_imp = @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista_imp := rfl
  trivial


/-! ## §C · SUBSUNCIONES — no son `rfl`, pero tampoco son contenido nuevo.

    Aqui produccion tiene un lema ESTRICTAMENTE MAS GENERAL y el del sondeo es una INSTANCIA.
    El escaneo por `isDefEq` NO los ve (los enunciados son distintos de verdad), y son justo la
    clase de duplicado que se colo en las cuatro promociones anteriores. -/

/-- **C.1** · `SFsubsttc.pcc_pred_succ_code` (L1788) es la instancia `w := tcFn m` de
    `EvalPredPrf.pcc_ax26_computed`, que vale para `w` **ARBITRARIO**.
    ⚠️ `pcc_ax26_computed` **NO esta en el bloque `export`** de `EvalPredPrf`: hay que citarla
    con el nombre largo, o anadirla al `export` al promover. -/
theorem sub_pcc_pred_succ_code (m : Term) :
    Prf (provFromCode (eqCodeFn (SFsubsttc.predcT (succcT (tcFn m))) (tcFn m))) :=
  ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_ax26_computed (tcFn m)

/-- **C.2** · `SFsubsttc.psi_l1` (L1585) es EXACTAMENTE `StrongInductionPrf.psi_lift_form`
    instanciado en `Φ := PHI`. Que el `rfl` cierre prueba que los dos tipos son el mismo.
    ⚠️ `psi_l2` / `psi_l3` / `PSI3` / `PSI_inst` NO son instancias de nada de produccion, pero
    se copian LETRA POR LETRA en 5 sondeos (`EvalSubstfcPrf`, `EnsamblajeTriple`,
    `EnsamblajeMedida`, `HasWitFReal` y este): son el caso ADR-019 — el general, cuantificado
    en `Φ`, tiene que BAJAR a `Meta/StrongInductionPrf.lean`, junto a `psi_lift_form` y
    `PSI_inst`, que ya bajaron alli por esta misma razon al promover B2. Comprobado con los
    imports EXACTOS de ese modulo en `Probe/B3_substtc_dedup_STRONGIND.lean`. -/
theorem sub_psi_l1 :
    @SFsubsttc.psi_l1
      = ROBINSON_PlusPlus.Meta.StrongInductionPrf.psi_lift_form SFsubsttc.PHI SFsubsttc.hPHI1 :=
  rfl

/-- **C.3** · `SFsubsttc.PredHyp` (L1396) es una hipotesis que produccion ya DESCARGA, y con
    MENOS: `EvalPredPrf.pcc_eval_pred` da la conclusion **sin la guarda `v < n`**. -/
theorem predHyp_desde_produccion : SFsubsttc.PredHyp := fun v n =>
  prf_deduction (prf_to_prfH (ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_pred n) _)

/-- Y la version SIN guarda, que es la que de verdad hay que consumir. -/
theorem predDot_sin_guarda (n : Term) :
    Prf (provFromCode (eqc (SFsubsttc.predcT (tcFn n)) (tcFn (pred n)))) :=
  ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_pred n

/-! ### §C.4 · `psi_l2` / `psi_l3` / `PSI3` / `PSI_inst`: el general, y el puente que prueba
    que los del sondeo son SU INSTANCIA en `Φ := PHI`.

    Los tres generales estan probados aparte en `Probe/B3_substtc_dedup_STRONGIND.lean`
    importando **solo `ROBINSON_PlusPlus.Meta.StrongInductionPrf`** (ni el barrel ni nada aguas
    abajo) y salen NET-0 (`[propext, Classical.choice, Quot.sound]`), asi que caben al final
    de ese modulo sin tocar su cabecera de imports. Aqui se repiten para poder atarlos. -/

theorem psi_lift_form2 (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) :
    liftFormula 0 (liftFormula 0 (PSI Φ))
      = Formula.forall (Formula.impl (lt (.var 0) (.var 3)) Φ) := by
  rw [ROBINSON_PlusPlus.Meta.StrongInductionPrf.psi_lift_form Φ hΦ]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT, reduceIte, hΦ]

theorem psi_lift_form3 (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) :
    liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI Φ)))
      = Formula.forall (Formula.impl (lt (.var 0) (.var 4)) Φ) := by
  rw [psi_lift_form2 Φ hΦ]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT, reduceIte, hΦ]

theorem PSI_inst3 (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) {Γ : List Formula}
    (hpsi : PrfH Γ (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI Φ))))) (z : Term) :
    PrfH Γ (Formula.impl (lt z (.var 3)) (substFormula 0 z Φ)) := by
  rw [psi_lift_form3 Φ hΦ] at hpsi
  have h := PrfH_spec hpsi z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (.var 4)) Φ)
      = Formula.impl (lt z (.var 3)) (substFormula 0 z Φ) := by
    simp only [substFormula, lt, substTerm, substTerms, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, if_true]
  rwa [e] at h

/-- `psi_l2` del sondeo ES `psi_lift_form2 PHI hPHI1`. -/
theorem sub_psi_l2 : @SFsubsttc.psi_l2 = psi_lift_form2 SFsubsttc.PHI SFsubsttc.hPHI1 := rfl
/-- `psi_l3` del sondeo ES `psi_lift_form3 PHI hPHI1`. -/
theorem sub_psi_l3 : @SFsubsttc.psi_l3 = psi_lift_form3 SFsubsttc.PHI SFsubsttc.hPHI1 := rfl
/-- Y `PSI_inst` del sondeo (L1604) ES `PSI_inst3 PHI hPHI1` — `PSI3` se desdobla por `rfl`. -/
theorem sub_PSI_inst : @SFsubsttc.PSI_inst = @PSI_inst3 SFsubsttc.PHI SFsubsttc.hPHI1 := rfl

/-! ## §D · EL §13 DEL SONDEO ES MUERTO — los tres teoremas finales, RECONSTRUIDOS.

    Se reprueban `pcc_eval_substtc'`, `pcc_eval_substtsc'` y `pcc_eval_substtc_hasWit'` sin
    tocar NADA del §13 (L1783-L1851: `AX26_BODY`, `AX26_BODY_ok`, `pcc_pred_succ_code`,
    `PrfH_congr_pred`, `PrfH_congr_predcT`, `PrfH_pred_dot_of_succ`, `liftT_predcode` y
    `predHyp` = **8 declaraciones**), y ademas con el VOCABULARIO DE PRODUCCION
    (`SinWTs.isTC1`, `SinWTs.wfAll1`, `SinWTs.argsIn`, `ENS.hasWit`), que es lo que los
    consumidores rio abajo (`prf_hasWitF_real`) saben leer. -/

theorem pcc_eval_substtc_SIN_S13 (w v s t : Term)
    (h : Prf (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTC1 w t)) :
    Prf (provFromCode (eqc (SFsubsttc.substtcT (tcFn v) (tcFn s) (tcFn t))
      (tcFn (substtc v s t)))) :=
  SFsubsttc.pcc_eval_substtc predHyp_desde_produccion w v s t h

theorem pcc_eval_substtsc_SIN_S13 (w v s t : Term)
    (hwf : Prf (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.wfAll1 w))
    (hargs : Prf (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsIn w t)) :
    Prf (provFromCode (eqc (SFsubsttc.substtscT (tcFn v) (tcFn s) (tcFn t))
      (tcFn (substtsc v s t)))) :=
  SFsubsttc.pcc_eval_substtsc predHyp_desde_produccion w v s t hwf hargs

theorem pcc_eval_substtc_hasWit_SIN_S13 (v s t : Term) :
    Prf (Formula.impl (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.hasWit t)
      (SFsubsttc.targetSubsttc v s t)) :=
  SFsubsttc.pcc_eval_substtc_hasWit predHyp_desde_produccion v s t

/-! ## §E · DUPLICADOS QUE YA ESTABAN EN PRODUCCION (no los trae este sondeo).

    El escaneo los destapa de paso. No bloquean B3, pero conviene que consten. -/

theorem pre_dup_argsIn :
    @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsIn
      = @ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf.boundedAllIn := rfl

theorem pre_dup_nthc :
    @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_nthc_lst
      = @ROBINSON_PlusPlus.Meta.RunFnBoundedPrf.PrfH_eq_congr_nthc1 := rfl

theorem pre_dup_In_left :
    @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_In_left
      = @ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf.PrfH_eq_subst_in1 := rfl

/-! ## §F · CONTROL: `pcc_eq_tracked` NO esta duplicada en este sondeo.

    El encargo avisaba de una copia LOCAL de `pcc_eq_tracked` que SOMBREABA a
    `Meta/Sigma1AtomPrf.lean` (tarea B7). **En el arbol de HOY ya no existe**: el sondeo la
    retiro (comentario en L975-L988) y `br_eq` (L1029) usa la de produccion. -/

theorem eq_tracked_es_de_produccion (t u : Term) :
    Prf ((t =eq u) ⇒ provFromCode (eqCodeFn (tcFn t) (tcFn u))) :=
  ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.pcc_eq_tracked t u

end DEDUP

/-! ## §G · POR QUE LAS 17 COLISIONES SON UN PELIGRO REAL, Y NO UNA PEGA DE ESTILO.

    **Nueve de las diecisiete ya viven en la RAIZ.** `Meta/LiftcCodePrf.lean` tiene un bloque
    `export` que sube a la raiz `refl_caso_varc`, `refl_caso_funcc`, `refl_lista_nil`,
    `refl_lista_cons`, `refl_shapeUn_imp`, `refl_caso_funcc_imp`, `refl_shapeBin_imp` y
    `refl_lista_cons_imp`; y `Meta/StrongInductionPrf.lean` sube `PSI_inst`. Si el modulo
    promovido `Meta/EvalSubsttcPrf.lean` recibe su propio `export` con esos mismos nombres
    cortos —que es EXACTAMENTE lo que se acaba de hacer con `CodeWitnessPrf` en B2b/B2c—, la
    raiz pasa a tener DOS `refl_lista_nil` y cualquier uso sin cualificar rio abajo es
    **ERROR DURO**, no aviso.

    Las otras ocho (`PHIbody`, `PHI`, `PHI_at`, `PHI_use`, `PHI_step`, `PHI_all`,
    `DESCENSO_imp`, `DESCENSO_lista_imp`) NO estan exportadas por `EvalLiftcPrf`, asi que solo
    muerden si un consumidor abre los dos namespaces.

    Demostracion COMPILADA del primer caso: se simula el `export` del modulo promovido. -/

namespace COLISION_DEMO
/-- El `refl_lista_nil` del sondeo, tal cual saldria del modulo promovido. -/
theorem refl_lista_nil (v s : Term) : Prf (SFsubsttc.targetSubsttsc v s nil) :=
  SFsubsttc.refl_lista_nil v s
end COLISION_DEMO

export COLISION_DEMO (refl_lista_nil)

/-- Antes del `export` de arriba, `refl_lista_nil` a secas era el de `LiftcCodePrf` (esta en la
    raiz por su `export`). Ahora hay DOS y el nombre corto ya no resuelve. -/
example : True := by
  fail_if_success have := refl_lista_nil
  trivial

/-- Y con el nombre largo los dos siguen ahi, cada uno diciendo lo suyo. -/
example : Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc nil) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil
example (v s : Term) : Prf (SFsubsttc.targetSubsttsc v s nil) :=
  COLISION_DEMO.refl_lista_nil v s

/-! ## HUELLA de lo reconstruido en §D: debe salir la MISMA que la del sondeo (4 axiomas,
    el cuarto `Representability2Prf.prf_axiomsCodeT_eq`, sancionado y ya en la linea base). -/
#print axioms DEDUP.pcc_eval_substtc_SIN_S13
#print axioms DEDUP.pcc_eval_substtsc_SIN_S13
#print axioms DEDUP.pcc_eval_substtc_hasWit_SIN_S13
#print axioms DEDUP.predHyp_desde_produccion
#print axioms DEDUP.sub_pcc_pred_succ_code
#print axioms DEDUP.predDot_sin_guarda
