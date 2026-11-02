/- # B3_planos_conexion — ANGULO (C): ¿`sondeos/SubstfcPlanos.lean` CONECTA con produccion?

   Sondeo auditado: `sondeos/SubstfcPlanos.lean`, 581 lineas, md5 d1ec711199d5099bbcac8d8dc0be0cf8.
   Todo lo que aqui se afirma esta COMPILADO. Nada se integra.

   §A duplicados exactos · §B puentes `rfl` de las definiciones · §C subsuncion AL REVES
   §D `pcc_substfc_bin_dot` reconstruido SIN `binK` · §E la moneda Γ · §F el consumidor
   §G controles.

   RESULTADO (todo compilado, exit 0, huella = 3 de Lean + `prf_axiomsCodeT_eq` sancionado):
   * §A · CINCO declaraciones del sondeo YA ESTAN en produccion, con el enunciado IDENTICO:
     `prf_substtc_termCode_closed/_numeralM/_zero` (`Meta/LiftcCodePrf.lean`) y
     `pcc_thm_inst4`/`pcc_axiom_inst4` (`Meta/MpCodePrf.lean`, promovidos DESDE ESTE MISMO
     sondeo el 2026-08-31 — la cabecera del sondeo, que dice que no existen, esta OBSOLETA).
   * §C · `prf_substtc_binK_at` SUBSUME a DOS lemas de produccion
     (`LiftcCodePrf.prf_substtc_binT_at` y `CodeCtorKit.prf_substtc_binT`) y `prf_congr_binK`
     a `CodeCtorKit.prf_congr_binT` — pero (C4/C5) en los UNICOS usos del sondeo (tags 5/7/8,
     o sea `numeralM k`) los de PRODUCCION bastan TAL CUAL.
   * §D · y en efecto: `pcc_substfc_bin_dot` sale entero con `binT k` +
     `prf_substtc_binT_at` + `prf_congr_binT`. `binK`, `binK_binT`, `prf_congr_binK`,
     `prf_substtc_binK_at`, `binct`, `binct_implc/_andc/_orc` — OCHO declaraciones — sobran.
   * §E · `paso2_caso_bin` NO sirve tal cual al consumidor: da las HI como hipotesis META y
     `ENS3.CasesCtx.cBinC` las pide Γ-parametricas. La reescritura es mecanica
     (`pcc_eq_trans_code` -> `PrfH_eq_trans_code`, produccion) y esta AQUI, compilada.
   * §F · el sondeo descarga 2 de los 11 campos de `ENS3.CasesCtx`: `cBotC` y `cBinC`.
   * PLACEMENT: este fichero entero compila tambien con
     `import ROBINSON_PlusPlus.Meta.LiftcCodePrf` en vez de `ROBINSON_PlusPlus.Meta`
     (verificado, exit 0) — el modulo nuevo va en el mismo escalon que `Meta/EvalLiftcPrf.lean`
     y NO hay ciclo de imports ni hay que BAJAR nada (ADR-019 no se dispara). -/
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
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.LiftcCodePrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.Representability2Prf ROBINSON_PlusPlus.Meta.ForallElimCodePrf

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace B3Conexion

/-! ############################################################################
    ## §A · DUPLICADOS EXACTOS — cinco declaraciones del sondeo YA estan en produccion
    ############################################################################

    Cada `example` reproduce el ENUNCIADO del sondeo palabra por palabra y lo cierra con la
    constante de PRODUCCION aplicada. Si typechequea, el enunciado es LITERALMENTE el mismo. -/

/-- Sondeo `prf_substtc_termCode_closed` (:90) = `LiftcCodePrf.prf_substtc_termCode_closed`. -/
example (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_closed v W t ht

/-- Sondeo `prf_substtc_termCode_numeralM` (:95) = el de `LiftcCodePrf`. -/
example (v m : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_numeralM v m W

/-- Sondeo `prf_substtc_termCode_zero` (:99) = el de `LiftcCodePrf`. -/
example (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_zero v W

/-- Sondeo `pcc_thm_inst4` (:142) = `MpCodePrf.pcc_thm_inst4`. -/
example (φ : Formula) (h : Prf (forall_4 φ)) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
  ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_thm_inst4 φ h w₁ w₂ w₃ w₄

/-- Sondeo `pcc_axiom_inst4` (:185) = `MpCodePrf.pcc_axiom_inst4`. -/
example (φ : Formula) (hmem : forall_4 φ ∈ axioms) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
  ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_axiom_inst4 φ hmem w₁ w₂ w₃ w₄

/-! ############################################################################
    ## §B · PUENTES `rfl` de las DEFINICIONES que el sondeo introduce
    ############################################################################ -/

/-- Copia LITERAL de la definicion del sondeo (:59). -/
def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))

/-- Copia LITERAL de la definicion del sondeo (:110). -/
def binK (H a b : Term) : Term := consT H (consT a (consT b (termCode nil)))

/-- Copia LITERAL de la definicion del sondeo (:216). -/
def evalSubstfcCode (v s f : Term) : Term :=
  eqCodeFn (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f))

/-- Copia LITERAL de la definicion del sondeo (:300). -/
def binct (T a b : Term) : Term := cons T (cons a (cons b nil))

/-- (B1) `binK` con el tag como codigo de numeral **ES** el `binT` de produccion. -/
theorem PUENTE_binK_binT (m : Nat) (a b : Term) : binK (termCode (numeralM m)) a b = binT m a b :=
  rfl

/-- (B2) `binct` con tag 5/7/8 **ES** `implc` / `andc` / `orc`. -/
theorem PUENTE_binct_implc (a b : Term) : binct (numeralM 5) a b = implc a b := rfl
theorem PUENTE_binct_andc (a b : Term) : binct (numeralM 7) a b = andc a b := rfl
theorem PUENTE_binct_orc (a b : Term) : binct (numeralM 8) a b = orc a b := rfl

/-- (B3) `binct` es el `bnc` del ensamblaje (`sondeos/EnsamblajeTriple.lean:765`). -/
theorem PUENTE_binct_bnc (k : Nat) (a b : Term) :
    binct (numeralM k) a b = cons (numeralM k) (cons a (cons b nil)) := rfl

/-- (B4) `eqc` y `eqCodeFn` son la MISMA funcion: el sondeo las mezcla sin puente y puede. -/
theorem PUENTE_eqc_eqCodeFn (a b : Term) : eqc a b = eqCodeFn a b := rfl

/-- (B5) `substfcT` sobre `termCode` **es** el `termCode` de `substfc`: el puente del sondeo. -/
theorem PUENTE_substfcT_termCode (v s f : Term) :
    substfcT (termCode v) (termCode s) (termCode f) = termCode (substfc v s f) := rfl

/-- (B6) `numeral 0` **es** `zero`: los lemas `_at` de produccion a nivel 0 son los de nivel
    `zero`, sin puente. -/
theorem PUENTE_numeral0_zero : numeral 0 = zero := rfl

/-- (B7) CONTROL NEGATIVO: `substfcT` NO tiene analogo en produccion, y no es `substtcT`
    (que si esta, en `sondeos/`, no en `Meta/`). Aqui solo se comprueba que NO colapsa
    con `funccT`, el unico constructor binario homonimo de produccion. -/
example (v s f : Term) : True := by
  fail_if_success exact (rfl : substfcT v s f = funccT v s)
  trivial


/-! ############################################################################
    ## §C · SUBSUNCION AL REVES (ADR-019) — `prf_substtc_binK_at` es MAS GENERAL
    ##      que `LiftcCodePrf.prf_substtc_binT_at`, que YA ESTA en produccion
    ############################################################################

    Produccion NO tenia `binK`, pero SI tiene desde hace tiempo la generalizacion a nivel
    `numeral v` arbitrario del constructor binario: `LiftcCodePrf.prf_substtc_binT_at`, con un
    guion de prueba **linea por linea identico** al del sondeo. La unica diferencia es que el
    tag es `numeralM m` (`m : Nat`) en vez de un `T : Term` abstracto con `hT`. -/

/-- Copia LITERAL del sondeo (:115). -/
theorem prf_congr_binK {H a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (binK H a b =eq binK H a' b') :=
  prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_congr_consT hb (prf_refl _)))

/-- Copia LITERAL del sondeo (:121). -/
theorem prf_substtc_binK_at (T : Term) (hT : ∀ c : Nat, liftTerm c T = T)
    (n : Nat) (W a b : Term) :
    Prf (substtc (numeral n) W (binK (termCode T) a b)
      =eq binK (termCode T) (substtc (numeral n) W a) (substtc (numeral n) W b)) := by
  unfold binK consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head
    (ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_closed n W T hT)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2 (prf_congr_cons_tail (prf_congr_cons_head
    (ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_zero n W)))

/-- (C1) El lema del sondeo SUBSUME al de produccion `prf_substtc_binT_at`: instanciando
    `T := numeralM m` sale EXACTAMENTE su enunciado, y el puente es `rfl`. -/
theorem SUBSUME_binT_at (m v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (binT m a b)
      =eq binT m (substtc (numeral v) W a) (substtc (numeral v) W b)) :=
  prf_substtc_binK_at (numeralM m) (fun c => liftTerm_numeralM c m) v W a b

/-- (C2) Y tambien al de `CodeCtorKit.prf_substtc_binT` (nivel `zero`), porque `numeral 0`
    **es** `zero`. Dos lemas de produccion bajo el mismo sondeo. -/
theorem SUBSUME_binT_zero (m : Nat) (W a b : Term) :
    Prf (substtc zero W (binT m a b) =eq binT m (substtc zero W a) (substtc zero W b)) :=
  prf_substtc_binK_at (numeralM m) (fun c => liftTerm_numeralM c m) 0 W a b

/-- (C3) `prf_congr_binK` subsume a `CodeCtorKit.prf_congr_binT`. -/
theorem SUBSUME_congr_binT {m : Nat} {a a' b b' : Term}
    (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) : Prf (binT m a b =eq binT m a' b') :=
  prf_congr_binK (H := termCode (numeralM m)) ha hb

/-- (C4) **Y AL REVES TAMBIEN**: en el unico uso real (tags 5/7/8, o sea `numeralM k` con
    `k : Nat`) el lema de PRODUCCION basta tal cual. La generalidad extra de `binK`
    —un tag `T : Term` que no sea un `numeralM`— NO se usa en ningun sitio del sondeo. -/
theorem PROD_BASTA_binK_at (k n : Nat) (W a b : Term) :
    Prf (substtc (numeral n) W (binK (termCode (numeralM k)) a b)
      =eq binK (termCode (numeralM k)) (substtc (numeral n) W a) (substtc (numeral n) W b)) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_binT_at k n W a b

/-- (C5) idem para la congruencia. -/
theorem PROD_BASTA_congr_binK {k : Nat} {a a' b b' : Term}
    (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (binK (termCode (numeralM k)) a b =eq binK (termCode (numeralM k)) a' b') :=
  prf_congr_binT (m := k) ha hb


/-! ############################################################################
    ## §D · `pcc_substfc_bin_dot` RECONSTRUIDO SOBRE VOCABULARIO DE PRODUCCION
    ##      — sin `binK`, sin `binct`, sin `prf_congr_binK`, sin `prf_substtc_binK_at`
    ############################################################################

    Mismo enunciado que el del sondeo (:316) especializado al unico caso que se usa (tag
    `numeralM k` con `k : Nat`), y misma prueba, pero con `binT k`,
    `LiftcCodePrf.prf_substtc_binT_at` y `CodeCtorKit.prf_congr_binT`, todo de PRODUCCION.

    Lo que SI hace falta del sondeo es el kit 3-ario de `substfcT`, que produccion NO tiene
    (solo llega a `funcc2`). -/

/-! ### D.0 · el kit 3-ario — esto SI es nuevo (copia literal del sondeo §0) -/

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

theorem prf_congr_funcc3 {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head hy)
      (prf_congr_cons_tail (prf_congr_cons_head hz)))))

theorem prf_congr_substfcT {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (substfcT v s f =eq substfcT v' s' f') := prf_congr_funcc3 hv hs hf

theorem prf_substtc_substfcT (v W x y z : Term) :
    Prf (substtc v W (substfcT x y z)
      =eq substfcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substfc") x y z

theorem substtc_inv_substfcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substfcT X Y Z) =eq substfcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substfcT zero W X Y Z) (prf_congr_substfcT (hX W) (hY W) (hZ W))

/-! ### D.1 · el cuerpo del axioma binario, generico en el tag `k : Nat` (sin `binct`) -/

def AXBIN_BODY_k (k : Nat) : Formula :=
  substfc (.var 3) (.var 2) (cons (numeralM k) (cons (.var 1) (cons (.var 0) nil)))
    =eq cons (numeralM k) (cons (substfc (.var 3) (.var 2) (.var 1))
      (cons (substfc (.var 3) (.var 2) (.var 0)) nil))

theorem AXBIN_impl_k : ax_substfc_impl = forall_4 (AXBIN_BODY_k 5) := rfl
theorem AXBIN_and_k : ax_substfc_and = forall_4 (AXBIN_BODY_k 7) := rfl
theorem AXBIN_or_k : ax_substfc_or = forall_4 (AXBIN_BODY_k 8) := rfl

/-! ### D.2 · la instancia interna DOTADA, con `binT k` de produccion -/

theorem pcc_substfc_bin_dot_prod (k : Nat) (hmem : forall_4 (AXBIN_BODY_k k) ∈ axioms)
    (v s a b : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b)))
      (binT k (substfcT (tcFn v) (tcFn s) (tcFn a))
        (substfcT (tcFn v) (tcFn s) (tcFn b))))) := by
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn a)
  let W0 : Term := tcFn b
  have hv3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc
      (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)))
      (prf_liftc_tcFn v)
  have hs2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have ha1 : Prf (W1 =eq tcFn a) := prf_liftc_tcFn a
  -- (0) la instancia bruta, con la hoja del tag SIN evaluar, escrita con `consT` a pelo
  have hkc : substCodeT 3 W3 (numeralM k) = termCode (numeralM k) :=
    substCodeT_closed 3 W3 (numeralM k) (fun c => liftTerm_numeralM c k)
  have hin0 : Prf (substfc (numeral 3) W3 (formCode (AXBIN_BODY_k k))
      =eq eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (consT (substCodeT 3 W3 (numeralM k))
            (consT (varc (numeral 1)) (consT (varc (numeral 0)) (termCode nil)))))
        (consT (substCodeT 3 W3 (numeralM k))
          (consT (substfcT W3 (varc (numeral 2)) (varc (numeral 1)))
            (consT (substfcT W3 (varc (numeral 2)) (varc (numeral 0))) (termCode nil))))) :=
    prf_substfc_arith_open 3 W3 (AXBIN_BODY_k k)
  rw [hkc] at hin0
  -- a partir de aqui `consT (termCode (numeralM k)) (consT _ (consT _ (termCode nil)))`
  -- **ES** `binT k _ _` por `rfl`, asi que el resto se escribe con `binT`.
  -- (1) nivel 3 : `W3 |-> v.`
  have hnorm3 : Prf (eqCodeFn
        (substfcT W3 (varc (numeral 2)) (binT k (varc (numeral 1)) (varc (numeral 0))))
        (binT k (substfcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substfcT W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2)) (binT k (varc (numeral 1)) (varc (numeral 0))))
        (binT k (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn
      (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _))
      (prf_congr_binT (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _))
        (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _)))
  -- (2) nivel 2
  have k2v : Prf (substtc (numeral 2) W2 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 2 W2 v
  have k2s : Prf (substtc (numeral 2) W2 (varc (numeral 2)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 2) W2 (numeral 2)) (prf_refl _)) hs2
  have k21 : Prf (substtc (numeral 2) W2 (varc (numeral 1)) =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 1))
      (prf_gnum_lt (show (1 : Nat) < 2 by omega))
  have k20 : Prf (substtc (numeral 2) W2 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 2 by omega))
  have hmid2 : Prf (substfc (numeral 2) W2 (eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2)) (binT k (varc (numeral 1)) (varc (numeral 0))))
        (binT k (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binT k (varc (numeral 1)) (varc (numeral 0))))
        (binT k (substfcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substfcT k2v k2s ?_
      exact prf_eq_trans
        (ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_binT_at k 2 W2 _ _)
        (prf_congr_binT k21 k20)
    · refine prf_eq_trans
        (ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_binT_at k 2 W2 _ _) ?_
      refine prf_congr_binT ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _)
          (prf_congr_substfcT k2v k2s k21)
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _)
          (prf_congr_substfcT k2v k2s k20)
  -- (3) nivel 1
  have k1v : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have k1s : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have k1a : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn a) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) ha1
  have k10 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 1 by omega))
  have hmid1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binT k (varc (numeral 1)) (varc (numeral 0))))
        (binT k (substfcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (varc (numeral 0))))
        (binT k (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substfcT k1v k1s ?_
      exact prf_eq_trans
        (ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_binT_at k 1 W1 _ _)
        (prf_congr_binT k1a k10)
    · refine prf_eq_trans
        (ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_binT_at k 1 W1 _ _) ?_
      refine prf_congr_binT ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _)
          (prf_congr_substfcT k1v k1s k1a)
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _)
          (prf_congr_substfcT k1v k1s k10)
  -- (4) nivel 0
  have k0v : Prf (substtc zero W0 (tcFn v) =eq tcFn v) := prf_substtc_tcFn W0 v
  have k0s : Prf (substtc zero W0 (tcFn s) =eq tcFn s) := prf_substtc_tcFn W0 s
  have k0a : Prf (substtc zero W0 (tcFn a) =eq tcFn a) := prf_substtc_tcFn W0 a
  have k0b : Prf (substtc zero W0 (varc (numeral 0)) =eq tcFn b) := prf_substtc_varc0 W0
  have hout : Prf (substfc zero W0 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (varc (numeral 0))))
        (binT k (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b)))
        (binT k (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT k0v k0s ?_
      exact prf_eq_trans
        (ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_binT_at k 0 W0 _ _)
        (prf_congr_binT k0a k0b)
    · refine prf_eq_trans
        (ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_binT_at k 0 W0 _ _) ?_
      refine prf_congr_binT ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _)
          (prf_congr_substfcT k0v k0s k0a)
      · exact prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _)
          (prf_congr_substfcT k0v k0s k0b)
  have hchain : Prf (substfc zero W0 (substfc (numeral 1) W1 (substfc (numeral 2) W2
        (substfc (numeral 3) W3 (formCode (AXBIN_BODY_k k)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b)))
        (binT k (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3
        (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin0 hnorm3)) hmid2)) hmid1)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_axiom_inst4 (AXBIN_BODY_k k) hmem
      (tcFn v) (tcFn s) (tcFn a) (tcFn b))

/-- (D3) Y da las tres instancias del sondeo, con `binT k` en vez de `binK (termCode T)`
    —que son la MISMA cosa por `rfl` (§B1). -/
theorem BIN_DOT_impl (v s a b : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binT 5 (tcFn a) (tcFn b)))
      (binT 5 (substfcT (tcFn v) (tcFn s) (tcFn a))
        (substfcT (tcFn v) (tcFn s) (tcFn b))))) :=
  pcc_substfc_bin_dot_prod 5 (show ax_substfc_impl ∈ axioms by simp [axioms]) v s a b

theorem BIN_DOT_and (v s a b : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binT 7 (tcFn a) (tcFn b)))
      (binT 7 (substfcT (tcFn v) (tcFn s) (tcFn a))
        (substfcT (tcFn v) (tcFn s) (tcFn b))))) :=
  pcc_substfc_bin_dot_prod 7 (show ax_substfc_and ∈ axioms by simp [axioms]) v s a b

theorem BIN_DOT_or (v s a b : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binT 8 (tcFn a) (tcFn b)))
      (binT 8 (substfcT (tcFn v) (tcFn s) (tcFn a))
        (substfcT (tcFn v) (tcFn s) (tcFn b))))) :=
  pcc_substfc_bin_dot_prod 8 (show ax_substfc_or ∈ axioms by simp [axioms]) v s a b


/-! ############################################################################
    ## §E · LA MONEDA DE LA INDUCCION OBJETO — `paso2_caso_bin` NO sirve TAL CUAL
    ############################################################################

    El consumidor final es `sondeos/EnsamblajeTriple.lean` §12, `ENS3.CasesCtx`, cuyo campo
    `cBinC` esta escrito (`:1254`) como

    ```text
    cBinC : ∀ (k : Nat), (k=5 ∨ k=7 ∨ k=8) → ∀ (Γ : List Formula) (v s a b : Term),
      PrfH Γ (targetSubstfc v s a) → PrfH Γ (targetSubstfc v s b) →
      PrfH Γ (targetSubstfc v s (bnc k a b))
    ```

    y el sondeo entrega las HI como hipotesis META (`Prf …`). El propio ensamblaje lo dice en
    `EnsamblajeTriple.lean:806-809`. Aqui se COMPILA la version Γ-parametrica y se comprueba
    que (a) es estrictamente mas fuerte y (b) el guion es el mismo cambiando
    `pcc_eq_trans_code` por `PrfH_eq_trans_code` (produccion, `EvalCarcNthcPrf:66`). -/

/-! ### E.0 · las piezas de contexto que el sondeo aporta y produccion no -/

/-- Copia LITERAL del sondeo (:193). NO existe analogo en produccion: los `pcc_congr_*_code`
    de `Meta/` son de aridad 1 o 2 (`predcT`, `unT`, `binT`, `liftcT`, `consT`). -/
theorem pcc_congr_substfcT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substfcT A B X) (substfcT A B Y))) := by
  let Ac : Term := eqc (substfcT A B X) (substfcT A B (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (substfcT A B X) (substfcT A B w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substfcT A B X)
      (substfcT A B (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substfcT zero w A B X)
        (prf_congr_substfcT (hA w) (hB w) (hX w))
    · exact prf_eq_trans (prf_substtc_substfcT zero w A B (varc (numeral 0)))
        (prf_congr_substfcT (hA w) (hB w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substfcT A B X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- El objetivo del ensamblaje (`EnsamblajeTriple.lean:91`). -/
def targetSubstfc (v s X : Term) : Formula :=
  provFromCode (eqCodeFn (substfcT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substfc v s X)))

/-- (E1) PUENTE: el objetivo del ensamblaje **es** `provFromCode (evalSubstfcCode …)`
    del sondeo, por `rfl`. Las dos capas hablan el mismo idioma. -/
theorem PUENTE_target_eval (v s X : Term) :
    targetSubstfc v s X = provFromCode (evalSubstfcCode v s X) := rfl

/-- El `bnc` del ensamblaje (`EnsamblajeTriple.lean:765`). -/
def bnc (m : Nat) (a b : Term) : Term := cons (numeralM m) (cons a (cons b nil))

/-- (E2) PUENTE: el `AXBIN_BODY` del sondeo, generico en un `T : Term`, no aporta nada sobre la
    version generica en `k : Nat` — coinciden por `rfl` en el unico punto donde se usa. -/
def AXBIN_BODY_T (T : Term) : Formula :=
  substfc (.var 3) (.var 2) (cons T (cons (.var 1) (cons (.var 0) nil)))
    =eq cons T (cons (substfc (.var 3) (.var 2) (.var 1))
      (cons (substfc (.var 3) (.var 2) (.var 0)) nil))

theorem PUENTE_AXBIN (k : Nat) : AXBIN_BODY_T (numeralM k) = AXBIN_BODY_k k := rfl

/-! ### E.1 · `paso2_caso_bin` en forma Γ-PARAMETRICA — la moneda que el ensamblaje consume -/

theorem paso2_caso_bin_ctx (k : Nat) (Γ : List Formula) (v s a b : Term)
    (hax : Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b)))
      (binT k (substfcT (tcFn v) (tcFn s) (tcFn a)) (substfcT (tcFn v) (tcFn s) (tcFn b))))))
    (hobj : Prf (substfc v s (bnc k a b)
      =eq cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil))))
    (hA : PrfH Γ (targetSubstfc v s a))
    (hB : PrfH Γ (targetSubstfc v s b)) :
    PrfH Γ (targetSubstfc v s (bnc k a b)) := by
  unfold targetSubstfc at hA hB ⊢
  let C : Term := bnc k a b
  have iSA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn a))
      =eq substfcT (tcFn v) (tcFn s) (tcFn a)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn a)
  have iSB : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn b))
      =eq substfcT (tcFn v) (tcFn s) (tcFn b)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn b)
  have iX0 : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn C))
      =eq substfcT (tcFn v) (tcFn s) (tcFn C)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn C)
  have iX1 : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b)))
      =eq substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_binT (substtc_inv_tcFn a) (substtc_inv_tcFn b))
  have iX2 : ∀ W, Prf (substtc zero W (binT k (substfcT (tcFn v) (tcFn s) (tcFn a))
        (substfcT (tcFn v) (tcFn s) (tcFn b)))
      =eq binT k (substfcT (tcFn v) (tcFn s) (tcFn a)) (substfcT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT iSA iSB
  have iX3 : ∀ W, Prf (substtc zero W (binT k (tcFn (substfc v s a))
        (substfcT (tcFn v) (tcFn s) (tcFn b)))
      =eq binT k (tcFn (substfc v s a)) (substfcT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn (substfc v s a)) iSB
  have iX4 : ∀ W, Prf (substtc zero W (binT k (tcFn (substfc v s a)) (tcFn (substfc v s b)))
      =eq binT k (tcFn (substfc v s a)) (tcFn (substfc v s b))) :=
    substtc_inv_binT (substtc_inv_tcFn (substfc v s a)) (substtc_inv_tcFn (substfc v s b))
  -- (1) cerrado: sube con `prf_to_prfH`
  have h1 : PrfH Γ (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn C))
      (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b))))) :=
    prf_to_prfH (prf_mp (pcc_congr_substfcT_arg3_code (tcFn v) (tcFn s) (tcFn C)
      (binT k (tcFn a) (tcFn b))
      (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn C)) (pcc_dot_bin_symm k a b)) Γ
  -- (3) **la HI del PRIMER hijo**: aqui es donde la forma META no serviria
  have h3 : PrfH Γ (provFromCode (eqc
      (binT k (substfcT (tcFn v) (tcFn s) (tcFn a)) (substfcT (tcFn v) (tcFn s) (tcFn b)))
      (binT k (tcFn (substfc v s a)) (substfcT (tcFn v) (tcFn s) (tcFn b))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_1_code k (substfcT (tcFn v) (tcFn s) (tcFn b))
      (substfcT (tcFn v) (tcFn s) (tcFn a)) (tcFn (substfc v s a)) iSB iSA) Γ) hA
  -- (4) la HI del SEGUNDO hijo
  have h4 : PrfH Γ (provFromCode (eqc
      (binT k (tcFn (substfc v s a)) (substfcT (tcFn v) (tcFn s) (tcFn b)))
      (binT k (tcFn (substfc v s a)) (tcFn (substfc v s b))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code k (tcFn (substfc v s a))
      (substfcT (tcFn v) (tcFn s) (tcFn b)) (tcFn (substfc v s b))
      (substtc_inv_tcFn (substfc v s a)) iSB) Γ) hB
  have h5 : PrfH Γ (provFromCode (eqc (binT k (tcFn (substfc v s a)) (tcFn (substfc v s b)))
      (tcFn (cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil)))))) :=
    prf_to_prfH (pcc_dot_bin k (substfc v s a) (substfc v s b)) Γ
  have h6 : PrfH Γ (provFromCode (eqc
      (tcFn (cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil))))
      (tcFn (substfc v s C)))) :=
    prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm hobj))))
      (prf_provFromCode_eqCodeFn_refl
        (tcFn (cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil)))))) Γ
  exact PrfH_eq_trans_code _ _ _ iX0 h1
    (PrfH_eq_trans_code _ _ _ iX1 (prf_to_prfH hax Γ)
      (PrfH_eq_trans_code _ _ _ iX2 h3
        (PrfH_eq_trans_code _ _ _ iX3 h4
          (PrfH_eq_trans_code _ _ _ iX4 h5 h6))))

/-! ### E.2 · `cBinC` para los tres tags — el campo del consumidor, DESCARGADO -/

theorem cBinC_impl (Γ : List Formula) (v s a b : Term)
    (hA : PrfH Γ (targetSubstfc v s a)) (hB : PrfH Γ (targetSubstfc v s b)) :
    PrfH Γ (targetSubstfc v s (bnc 5 a b)) :=
  paso2_caso_bin_ctx 5 Γ v s a b (BIN_DOT_impl v s a b) (prf_substfc_impl v s a b) hA hB

theorem cBinC_and (Γ : List Formula) (v s a b : Term)
    (hA : PrfH Γ (targetSubstfc v s a)) (hB : PrfH Γ (targetSubstfc v s b)) :
    PrfH Γ (targetSubstfc v s (bnc 7 a b)) :=
  paso2_caso_bin_ctx 7 Γ v s a b (BIN_DOT_and v s a b) (prf_substfc_and v s a b) hA hB

theorem cBinC_or (Γ : List Formula) (v s a b : Term)
    (hA : PrfH Γ (targetSubstfc v s a)) (hB : PrfH Γ (targetSubstfc v s b)) :
    PrfH Γ (targetSubstfc v s (bnc 8 a b)) :=
  paso2_caso_bin_ctx 8 Γ v s a b (BIN_DOT_or v s a b) (prf_substfc_or v s a b) hA hB

/-- **El campo `cBinC` de `ENS3.CasesCtx` (`EnsamblajeTriple.lean:1254`), literal.** -/
theorem CASESCTX_cBinC : ∀ (k : Nat), (Or (k = 5) (Or (k = 7) (k = 8))) →
    ∀ (Γ : List Formula) (v s a b : Term),
    PrfH Γ (targetSubstfc v s a) → PrfH Γ (targetSubstfc v s b) →
    PrfH Γ (targetSubstfc v s (bnc k a b)) := by
  rintro k (rfl | rfl | rfl) Γ v s a b hA hB
  · exact cBinC_impl Γ v s a b hA hB
  · exact cBinC_and Γ v s a b hA hB
  · exact cBinC_or Γ v s a b hA hB

/-! ### E.3 · la version Γ es ESTRICTAMENTE MAS FUERTE que la del sondeo

`prf_to_prfH` va en un solo sentido (`Prf φ → ∀ Γ, PrfH Γ φ`); la vuelta solo existe con
`Γ = []` (`HilbertDeduction.prfH_nil_to_prf`). Por eso de la Γ-parametrica se recupera la META
del sondeo, y de la META **no** se recupera la Γ-parametrica. -/

/-- (E3) De la Γ-parametrica sale el enunciado META del sondeo (`paso2_caso_bin`, :457). -/
theorem META_de_ctx (k : Nat) (v s a b : Term)
    (hax : Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b)))
      (binT k (substfcT (tcFn v) (tcFn s) (tcFn a)) (substfcT (tcFn v) (tcFn s) (tcFn b))))))
    (hobj : Prf (substfc v s (bnc k a b)
      =eq cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil))))
    (hA : Prf (provFromCode (evalSubstfcCode v s a)))
    (hB : Prf (provFromCode (evalSubstfcCode v s b))) :
    Prf (provFromCode (evalSubstfcCode v s (bnc k a b))) :=
  ROBINSON_PlusPlus.Meta.HilbertDeduction.prfH_nil_to_prf
    (paso2_caso_bin_ctx k [] v s a b hax hobj (prf_to_prfH hA []) (prf_to_prfH hB [])) rfl

/-! ############################################################################
    ## §F · EL CONSUMIDOR — que queda DESCARGADO aguas abajo
    ############################################################################

    `ENS3.CasesCtx` tiene once campos. El sondeo toca DOS: `cBotC` y `cBinC`. -/

/-! ### F.1 · `cBotC` — este SI encaja TAL CUAL (no lleva HI) -/

def AXBOT_BODY : Formula := substfc (.var 1) (.var 0) botc =eq botc

theorem AXBOT_BODY_ok : ax_substfc_bottom = forall_2 AXBOT_BODY := rfl

theorem pcc_substfc_bottom_dot (v s : Term) :
    Prf (provFromCode (eqCodeFn (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2))) := by
  let W1 : Term := liftc zero (tcFn v)
  let W0 : Term := tcFn s
  have hin : Prf (substfc (numeral 1) W1 (formCode AXBOT_BODY)
      =eq eqCodeFn (substfcT W1 (varc (numeral 0)) (nulT 2)) (nulT 2)) :=
    prf_substfc_arith_open 1 W1 AXBOT_BODY
  have hA1 : Prf (W1 =eq tcFn v) := prf_liftc_tcFn v
  have hnorm : Prf (eqCodeFn (substfcT W1 (varc (numeral 0)) (nulT 2)) (nulT 2)
      =eq eqCodeFn (substfcT (tcFn v) (varc (numeral 0)) (nulT 2)) (nulT 2)) :=
    prf_congr_eqCodeFn (prf_congr_substfcT hA1 (prf_refl _) (prf_refl _)) (prf_refl _)
  have hout : Prf (substfc zero W0 (eqCodeFn (substfcT (tcFn v) (varc (numeral 0)) (nulT 2))
        (nulT 2))
      =eq eqCodeFn (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2)) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ (prf_substtc_nulT 2 W0)
    refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
    exact prf_congr_substfcT (prf_substtc_tcFn W0 v) (prf_substtc_varc0 W0)
      (prf_substtc_nulT 2 W0)
  have hchain : Prf (substfc zero W0 (substfc (numeral 1) W1 (formCode AXBOT_BODY))
      =eq eqCodeFn (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2)) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_axiom_inst2 AXBOT_BODY
      (show ax_substfc_bottom ∈ axioms by simp [axioms]) (tcFn v) (tcFn s))

/-- **El campo `cBotC` de `ENS3.CasesCtx`, DESCARGADO** — y con el enunciado `targetSubstfc`
    del ensamblaje, no con el `evalSubstfcCode` del sondeo (son `rfl`, §E1). -/
theorem CASESCTX_cBotC (v s : Term) : Prf (targetSubstfc v s botc) := by
  unfold targetSubstfc
  have iA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn botc))
      =eq substfcT (tcFn v) (tcFn s) (tcFn botc)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn botc)
  have iB : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (nulT 2))
      =eq substfcT (tcFn v) (tcFn s) (nulT 2)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_nulT 2)
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn botc))
      (substfcT (tcFn v) (tcFn s) (nulT 2)))) :=
    prf_mp (pcc_congr_substfcT_arg3_code (tcFn v) (tcFn s) (tcFn botc) (nulT 2)
      (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn botc)) (pcc_dot_nul_symm 2)
  have h2 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2))) :=
    pcc_substfc_bottom_dot v s
  have h3 : Prf (provFromCode (eqc (nulT 2) (tcFn botc))) := pcc_dot_nul 2
  have h4 : Prf (provFromCode (eqc (tcFn botc) (tcFn (substfc v s botc)))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_substfc_bottom v s)))))
      (prf_provFromCode_eqCodeFn_refl (tcFn botc))
  exact pcc_eq_trans_code _ _ _ iA h1
    (pcc_eq_trans_code _ _ _ iB h2
      (pcc_eq_trans_code _ _ _ (substtc_inv_nulT 2) h3 h4))

/-! ### F.2 · lo que NO queda descargado

`ENS3.CasesCtx` pide once campos. Con este sondeo promovido quedan cubiertos `cBotC` (F.1) y
`cBinC` (E.2) — **2 de 11**. Los otros nueve no los toca este sondeo:
`cAtomC`/`cEqC` (no existe lema de caso en ningun sitio, solo ingredientes), `cUnC` (`SubstfcEx`),
`cLiftC` (`Paso2Guardado`), y `cVarC`/`cFuncC`/`cNilC`/`cConsC` (`EvalSubsttc`). -/

/-- CONTROL: los dos campos descargados, con el tipo EXACTO que pide `CasesCtx`. -/
example : (∀ v s : Term, Prf (targetSubstfc v s botc)) ∧
    (∀ (k : Nat), (Or (k = 5) (Or (k = 7) (k = 8))) →
      ∀ (Γ : List Formula) (v s a b : Term),
      PrfH Γ (targetSubstfc v s a) → PrfH Γ (targetSubstfc v s b) →
      PrfH Γ (targetSubstfc v s (bnc k a b))) :=
  ⟨CASESCTX_cBotC, CASESCTX_cBinC⟩


/-! ############################################################################
    ## §G · CONTROLES NEGATIVOS (los del sondeo, re-corridos sobre el arbol de HOY)
    ############################################################################ -/

set_option linter.unusedVariables false in
/-- Ninguno de los enunciados es una reflexividad disfrazada. -/
example (v s a b : Term) : True := by
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn botc) = tcFn (substfc v s botc))
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn (implc a b)) = tcFn (substfc v s (implc a b)))
  fail_if_success
    exact (rfl : targetSubstfc v s (bnc 5 a b) = targetSubstfc v s botc)
  trivial

/-- Los tres tags binarios son DISTINTOS: el lema generico en `k` no los confunde. -/
example : bnc 5 zero zero ≠ bnc 7 zero zero := by
  intro h; exact absurd h (by decide)

/-- Y el generico en `k` NO es vacuo: `binT k` con `k` abstracto no colapsa a `nulT`. -/
example (k : Nat) (a b : Term) : True := by
  fail_if_success exact (rfl : binT k a b = nulT k)
  trivial

end B3Conexion

#print axioms B3Conexion.PUENTE_binK_binT
#print axioms B3Conexion.SUBSUME_binT_at
#print axioms B3Conexion.PROD_BASTA_binK_at
#print axioms B3Conexion.pcc_substfc_bin_dot_prod
#print axioms B3Conexion.paso2_caso_bin_ctx
#print axioms B3Conexion.CASESCTX_cBinC
#print axioms B3Conexion.CASESCTX_cBotC
#print axioms B3Conexion.META_de_ctx

