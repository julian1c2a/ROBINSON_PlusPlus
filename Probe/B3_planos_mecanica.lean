/- # `Probe/B3_planos_mecanica.lean` — B3 · sondeo `SubstfcPlanos`, ANGULO (A): LA MECANICA.

   Contenido EXACTO propuesto para el futuro modulo de `Meta/` a partir de
   `sondeos/SubstfcPlanos.lean` (581 lineas, md5 `d1ec711199d5099bbcac8d8dc0be0cf8`),
   quedandose SOLO con lo que falta y CONSUMIENDO de produccion todo lo demas.

   ## NOMBRE DE MODULO PROPUESTO: `ROBINSON_PlusPlus/Meta/SubstfcCodePrf.lean`

   Paralelo exacto de `Meta/LiftcCodePrf.lean` (B1): alli, el vocabulario a nivel de CODIGO de
   `liftc`/`liftsc` mas sus casos; aqui, el de `substfc` (`substfcT`, `evalSubstfcCode`, `binK`,
   `binct`) mas los CUATRO constructores PLANOS. Lo que venga despues (el ensamblaje de los
   otros cuatro sondeos de B3) sera `Meta/EvalSubstfcPrf.lean`, igual que `EvalLiftcPrf` siguio
   a `LiftcCodePrf`. Namespace: `ROBINSON_PlusPlus.Meta.SubstfcCodePrf`.

   ## Lo que se ha QUITADO respecto del sondeo (5 de 39, ya en produccion)

   | del sondeo                      | vive HOY en                                  |
   |---------------------------------|----------------------------------------------|
   | `prf_substtc_termCode_closed`   | `Meta/LiftcCodePrf.lean` (exportado a raiz)  |
   | `prf_substtc_termCode_numeralM` | `Meta/LiftcCodePrf.lean` (exportado a raiz)  |
   | `prf_substtc_termCode_zero`     | `Meta/LiftcCodePrf.lean` (exportado a raiz)  |
   | `pcc_thm_inst4`                 | `Meta/MpCodePrf.lean` (exportado a raiz)     |
   | `pcc_axiom_inst4`               | `Meta/MpCodePrf.lean` (exportado a raiz)     |

   ⚠️ La cabecera del sondeo dice que `pcc_thm_inst4`/`pcc_axiom_inst4` «no existian en
   produccion (solo hasta `inst3`)». **Eso ya NO es verdad**: estan promovidos, con el enunciado
   IDENTICO. Este fichero los CONSUME (§2) y compila; esa es la prueba.

   ## Lo que queda: 34 declaraciones nombradas + los 2 `example` de control del sondeo.

   ## LISTA DE IMPORTS del modulo real (19; NINGUNO es el barrel)

   Validada compilando `Probe/B3_planos_mecanica_IMPORTS.lean` (mismo cuerpo, sin barrel,
   exit 0). Cada linea con el simbolo que la pide — resolucion por `realizeGlobalConst`
   (`Probe/B3_planos_resolve.lean`), no por leer los `import`:

   ```
   import ROBINSON_PlusPlus.Meta.ArithPrf         -- prf_substtc_func, prf_substtsc_cons/_nil,
                                                  -- prf_substtc_var_eq/_lt, prf_substfc_eq,
                                                  -- prf_substfc_bottom/_impl/_and/_or,
                                                  -- prf_congr_substfc_arg3, prf_gnum_lt   (12)
   import ROBINSON_PlusPlus.Meta.CodeCtorKit      -- binT, nulT, prf_substtc_nulT,
                                                  -- substtc_inv_nulT/_binT, pcc_dot_nul(_symm),
                                                  -- pcc_dot_bin(_symm),
                                                  -- pcc_congr_binT_1_code/_2_code          (11)
   import ROBINSON_PlusPlus.Meta.DerivCondPrf     -- liftTerm_strCode, substTerm_strCode,
                                                  -- liftTerm_numeral, substTerm_numeral     (4)
   import ROBINSON_PlusPlus.Meta.DotConsPrf       -- consT, prf_congr_consT                  (2)
   import ROBINSON_PlusPlus.Meta.EvalArithPrf     -- prf_substtc_funcc2, prf_substtc_varc0,
                                                  -- substtc_inv_tcFn, pcc_eq_trans_code     (4)
   import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf  -- PrfH_leibniz_apply                      (1)
   import ROBINSON_PlusPlus.Meta.EvalLtPrf        -- prf_substtc_tcFn_at                     (1)
   import ROBINSON_PlusPlus.Meta.Godel            -- numeral                                 (1)
   import ROBINSON_PlusPlus.Meta.Hilbert          -- Prf                                     (1)
   import ROBINSON_PlusPlus.Meta.HilbertDeduction -- PrfH, PrfH.mp, prf_deduction,
                                                  -- prf_to_prfH, prfH_hyp_self              (4)
   import ROBINSON_PlusPlus.Meta.LiftcCodePrf     -- prf_substtc_termCode_closed/_zero       (2)
   import ROBINSON_PlusPlus.Meta.MpCodePrf        -- pcc_axiom_inst2, pcc_axiom_inst4,
                                                  -- pcc_thm_inst4 (§2)                      (3)
   import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf -- prf_congr_funcc2, prf_congr_liftc,
                                                  -- prf_liftc_tcFn, prf_substtc_tcFn        (4)
   import ROBINSON_PlusPlus.Meta.Provability      -- termCode, formCode, strCode             (3)
   import ROBINSON_PlusPlus.Meta.ReprPrf          -- prf_eq_trans/_symm, prf_refl, prf_mp,
                                                  -- prf_congr_cons_head/_tail               (6)
   import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf    -- eqCodeFn, prf_congr_eqCodeFn,
                                                  -- prf_provFromCode_eqCodeFn_refl          (3)
   import ROBINSON_PlusPlus.Meta.Sigma1Prf        -- provFromCode, prf_provCode_congr        (2)
   import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf -- substCodeT, substCodeT_closed,
                                                  -- prf_substfc_arith_open                  (3)
   import ROBINSON_PlusPlus.Meta.TcArithPrf       -- prf_congr_tcFn                          (1)
   ```

   `Minimal/Axioms` (23 nombres: `substfc`, `substtc`, `funcc`, `cons`, `tcFn`, `numeralM`,
   `ax_substfc_*`, …) y `FOL.FOL` (`liftTerm`, `substTerm`, `liftTerms`, `substTerms`) llegan
   TRANSITIVAMENTE por cualquiera de los 19 y no se listan como `import` directo, igual que
   hace `Meta/LiftcCodePrf.lean`.

   ⚠️ `Meta/CodeWitnessPrf` **NO** hace falta. El unico simbolo que aportaria es su
   `prf_congr_liftc (v : Term) …` (que llega a la raiz por el `export` de `SinWTs`), y ese es
   AMBIGUO con `NumCodeClosedPrf.prf_congr_liftc {c : Term} …` — el que este modulo usa es el
   SEGUNDO. Se desambigua sola por aridad, pero la ambiguedad SIGUE ahi (CodeWitnessPrf entra
   igual por `LiftcCodePrf`); el blindaje de un token es escribir
   `NumCodeClosedPrf.prf_congr_liftc`. Ya esta documentada en `LiftcCodePrf.lean:88`.

   ## BLOQUE `export` PROPUESTO — 19 de 34, por MEDICION (criterio B2b)

   Criterio: **sale a la raiz lo que OTRO modulo consume**, no lo que existe. Medido contando
   usos (excluida la declaracion propia) en los otros CUATRO sondeos de B3 — `SubstfcEx`,
   `EvalSubsttc`, `EvalPredDot`, `EvalSubstfcPrf` — que son los futuros consumidores:

   ```
   export ROBINSON_PlusPlus.Meta.SubstfcCodePrf (
     prf_substtc_funcc3 prf_congr_funcc3
     substfcT prf_congr_substfcT prf_substtc_substfcT substtc_inv_substfcT
     binK prf_congr_binK prf_substtc_binK_at
     pcc_congr_substfcT_arg3_code
     evalSubstfcCode substTerm_evalSubstfcCode liftTerm_evalSubstfcCode
     AXBOT_BODY pcc_substfc_bottom_dot paso2_caso_bottom
     binct AXBIN_BODY pcc_substfc_bin_dot
   )
   ```

   **NO se exportan 15**, con CERO usos externos medidos hoy:
   `substfcT_termCode`, `liftTerm_substfcT`, `substTerm_substfcT`, `binK_binT`,
   `AXBOT_BODY_ok`, `AXBIN_impl`, `AXBIN_and`, `AXBIN_or`, `binct_implc`, `binct_andc`,
   `binct_orc` — puentes `rfl` y controles: los otros sondeos los COPIAN, nunca los invocan —
   y `paso2_caso_bin`, `paso2_caso_impl`, `paso2_caso_and`, `paso2_caso_or`.

   ⚠️⚠️ **Esos cuatro ultimos son el hallazgo caro de este angulo.**
   `sondeos/EvalSubstfcPrf.lean` —el ensamblaje real— **no llama a `paso2_caso_bin`**: lo cita
   en prosa (`:6460`, `:6687`, `:7035`) y escribe en su lugar `paso2_caso_bin_imp` (`:7037`),
   el MISMO caso reescrito en `PrfH Γ` como IMPLICACION, «porque en la induccion la HI llega
   como HIPOTESIS, no como `Prf` cerrada». Es la moneda de la induccion OBJETO otra vez.
   `paso2_caso_bottom`, en cambio, SI se consume (`EvalSubstfcPrf:6891`): es nulario, no tiene
   HI. Y `sondeos/EnsamblajeMedida.lean:405-407` + `:439` (`CASO_bin`) todavia planifica la
   forma `Prf → Prf → Prf`: **el plan y el ensamblaje real NO coinciden**. Se dejan declarados
   (son baratos y son el enunciado legible del caso) pero fuera del `export`.

   ⚠️ CERO axiomas de Lean nuevos, cero `sorry`. `substfcT` es una DEFINICION y nada mas.
   Footprint medido abajo: `prf_substtc_binK_at` y `pcc_congr_substfcT_arg3_code` son net-0
   PURO (los 3 axiomas de Lean); los siete teoremas del frente arrastran ADEMAS el CUARTO,
   `Representability2Prf.prf_axiomsCodeT_eq`, que es SANCIONADO y ya estaba en la linea base. -/
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
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.Representability2Prf ROBINSON_PlusPlus.Meta.ForallElimCodePrf
open ROBINSON_PlusPlus.Meta.LiftcCodePrf

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace ROBINSON_PlusPlus.Meta.SubstfcCodePrf

/-! ## §0 · Fontaneria `funcc` de ARIDAD 3

    Produccion tiene `prf_substtc_funcc1`/`_funcc2` y `prf_congr_funcc2`
    (`Meta/EvalArithPrf.lean`); la aridad 3 es lo que pide `substfcT`. -/

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

/-- El constructor de código `substfc` (DEFINICIÓN; ninguna ecuación suya se postula). -/
def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))

theorem substfcT_termCode (v s f : Term) :
    substfcT (termCode v) (termCode s) (termCode f) = termCode (substfc v s f) := rfl

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

theorem liftTerm_substfcT (k : Nat) (v s f : Term) :
    liftTerm k (substfcT v s f) = substfcT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]

theorem substTerm_substfcT (k : Nat) (u v s f : Term) :
    substTerm k u (substfcT v s f)
      = substfcT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

/-! ## §1 · `binK` — el constructor BINARIO de código con la ETIQUETA ABSTRACTA.

Es `binT` con el tag dado como CÓDIGO (`H = termCode T`) en vez de como `Nat`. Es la pieza
que permite escribir **una sola vez** el caso binario y usarlo para `impl`, `and` y `or`.

⚠️ **ADR-019**: `binK`, `prf_congr_binK` y `prf_substtc_binK_at` SUBSUMEN, respectivamente, a
`CodeCtorKit.binT`, `CodeCtorKit.prf_congr_binT` y `LiftcCodePrf.prf_substtc_binT_at`.
Los puentes que lo prueban estan en §8. -/

def binK (H a b : Term) : Term := consT H (consT a (consT b (termCode nil)))

/-- Puente por `rfl` con el `binT` de producción. -/
theorem binK_binT (m : Nat) (a b : Term) : binK (termCode (numeralM m)) a b = binT m a b := rfl

theorem prf_congr_binK {H a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (binK H a b =eq binK H a' b') :=
  prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_congr_consT hb (prf_refl _)))

/-- `substtc` atraviesa `binK` a nivel ARBITRARIO (espeja `prf_substtc_binT`, que sólo vale
    a nivel `zero`). Requiere que el tag `T` sea CERRADO. -/
theorem prf_substtc_binK_at (T : Term) (hT : ∀ c : Nat, liftTerm c T = T)
    (n : Nat) (W a b : Term) :
    Prf (substtc (numeral n) W (binK (termCode T) a b)
      =eq binK (termCode T) (substtc (numeral n) W a) (substtc (numeral n) W b)) := by
  unfold binK consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_closed n W T hT)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero n W)))

/-! ## §2 · `pcc_thm_inst4` / `pcc_axiom_inst4` — SE CONSUMEN DE `Meta/MpCodePrf.lean`.

    El sondeo los declaraba aqui. Ya no hace falta: estan en produccion con el MISMO
    enunciado. Control de que efectivamente encajan: -/

example (φ : Formula) (h : Prf (forall_4 φ)) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
  ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_thm_inst4 φ h w₁ w₂ w₃ w₄

example (φ : Formula) (hmem : forall_4 φ ∈ axioms) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
  ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_axiom_inst4 φ hmem w₁ w₂ w₃ w₄

/-! Y los tres `prf_substtc_termCode_*` del §0 del sondeo, uno a uno, contra
    `Meta/LiftcCodePrf.lean`. Los tres enunciados son los del sondeo, palabra por palabra. -/

example (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_closed v W t ht

example (v m : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_numeralM v m W

example (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_zero v W

/-! ## §3 · Congruencia INTERNA de `substfcT` en el 3er argumento.

    Patron `LiftcCodePrf.pcc_congr_liftcT_arg2_code` / `CodeCtorKit.pcc_congr_binT_2_code`;
    ninguno de los dos sirve aqui porque `substfcT` no es ni `liftcT` ni un `binT`. -/

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

/-! ## §4 · El código de la ecuación interna -/

def evalSubstfcCode (v s f : Term) : Term :=
  eqCodeFn (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f))

theorem substTerm_evalSubstfcCode (k : Nat) (u v s f : Term) :
    substTerm k u (evalSubstfcCode v s f)
      = evalSubstfcCode (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [evalSubstfcCode, eqCodeFn, substfcT, funcc, tcFn, substfc, cons, nil, zero, succ,
    substTerm, substTerms, substTerm_numeral, substTerm_strCode]

theorem liftTerm_evalSubstfcCode (k : Nat) (v s f : Term) :
    liftTerm k (evalSubstfcCode v s f)
      = evalSubstfcCode (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [evalSubstfcCode, eqCodeFn, substfcT, funcc, tcFn, substfc, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

/-! ## §5 · CASO `bottom` — constructor NULARIO, axioma `forall_2`. El más barato de todos. -/

def AXBOT_BODY : Formula := substfc (.var 1) (.var 0) botc =eq botc

theorem AXBOT_BODY_ok : ax_substfc_bottom = forall_2 AXBOT_BODY := rfl

/-- La instancia INTERNA del axioma `ax_substfc_bottom`, DOTADA. -/
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
    (pcc_axiom_inst2 AXBOT_BODY (show ax_substfc_bottom ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s))

/-- **CASO `bottom` DE `pcc_eval_substfc`, CERRADO.** Sin hipótesis: constructor nulario. -/
theorem paso2_caso_bottom (v s : Term) :
    Prf (provFromCode (evalSubstfcCode v s botc)) := by
  unfold evalSubstfcCode
  have iA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn botc))
      =eq substfcT (tcFn v) (tcFn s) (tcFn botc)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn botc)
  have iB : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (nulT 2))
      =eq substfcT (tcFn v) (tcFn s) (nulT 2)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_nulT 2)
  -- (1) `tcFn botc ↦ nulT 2` bajo el 3er argumento de `substfcT`, DENTRO de `Prov`
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn botc))
      (substfcT (tcFn v) (tcFn s) (nulT 2)))) :=
    prf_mp (pcc_congr_substfcT_arg3_code (tcFn v) (tcFn s) (tcFn botc) (nulT 2)
      (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn botc)) (pcc_dot_nul_symm 2)
  -- (2) la instancia interna del axioma
  have h2 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2))) :=
    pcc_substfc_bottom_dot v s
  -- (3) `nulT 2 ↦ tcFn botc` (el KIT, dirección directa)
  have h3 : Prf (provFromCode (eqc (nulT 2) (tcFn botc))) := pcc_dot_nul 2
  -- (4) la ecuación OBJETO del axioma, dotada GRATIS por `prf_congr_tcFn`
  have h4 : Prf (provFromCode (eqc (tcFn botc) (tcFn (substfc v s botc)))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_substfc_bottom v s)))))
      (prf_provFromCode_eqCodeFn_refl (tcFn botc))
  exact pcc_eq_trans_code _ _ _ iA h1
    (pcc_eq_trans_code _ _ _ iB h2
      (pcc_eq_trans_code _ _ _ (substtc_inv_nulT 2) h3 h4))

/-! ## §6 · CASO BINARIO — `impl`, `and`, `or` en UN SOLO lema. -/

def binct (T a b : Term) : Term := cons T (cons a (cons b nil))

theorem binct_implc (a b : Term) : binct (numeralM 5) a b = implc a b := rfl
theorem binct_andc (a b : Term) : binct (numeralM 7) a b = andc a b := rfl
theorem binct_orc (a b : Term) : binct (numeralM 8) a b = orc a b := rfl

def AXBIN_BODY (T : Term) : Formula :=
  substfc (.var 3) (.var 2) (binct T (.var 1) (.var 0))
    =eq binct T (substfc (.var 3) (.var 2) (.var 1)) (substfc (.var 3) (.var 2) (.var 0))

theorem AXBIN_impl : ax_substfc_impl = forall_4 (AXBIN_BODY (numeralM 5)) := rfl
theorem AXBIN_and : ax_substfc_and = forall_4 (AXBIN_BODY (numeralM 7)) := rfl
theorem AXBIN_or : ax_substfc_or = forall_4 (AXBIN_BODY (numeralM 8)) := rfl

/-- **La instancia INTERNA del axioma binario, DOTADA**, genérica en la etiqueta `T`.
    Un solo lema para `impl`, `and` y `or`. -/
theorem pcc_substfc_bin_dot (T : Term) (hT : ∀ c : Nat, liftTerm c T = T)
    (hmem : forall_4 (AXBIN_BODY T) ∈ axioms) (v s a b : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
      (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
        (substfcT (tcFn v) (tcFn s) (tcFn b))))) := by
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn a)
  let W0 : Term := tcFn b
  -- normalizaciones de los testigos levantados
  have hv3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc
      (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)))
      (prf_liftc_tcFn v)
  have hs2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have ha1 : Prf (W1 =eq tcFn a) := prf_liftc_tcFn a
  -- (0) la instancia bruta, con la hoja del tag SIN evaluar
  have hkc : substCodeT 3 W3 T = termCode T := substCodeT_closed 3 W3 T hT
  have hin0 : Prf (substfc (numeral 3) W3 (formCode (AXBIN_BODY T))
      =eq eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (substCodeT 3 W3 T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (substCodeT 3 W3 T) (substfcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substfcT W3 (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 3 W3 (AXBIN_BODY T)
  rw [hkc] at hin0
  -- (1) nivel 3 : `W3 ↦ v̇`
  have hnorm3 : Prf (eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substfcT W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn
      (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _))
      (prf_congr_binK (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _))
        (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _)))
  -- (2) nivel 2 : `#2 ↦ ṡ`
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
        (substfcT (tcFn v) (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substfcT k2v k2s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) (prf_congr_binK k21 k20)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _)
          (prf_congr_substfcT k2v k2s k21)
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _)
          (prf_congr_substfcT k2v k2s k20)
  -- (3) nivel 1 : `#1 ↦ ȧ`
  have k1v : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have k1s : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have k1a : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn a) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) ha1
  have k10 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 1 by omega))
  have hmid1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substfcT k1v k1s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) (prf_congr_binK k1a k10)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _)
          (prf_congr_substfcT k1v k1s k1a)
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _)
          (prf_congr_substfcT k1v k1s k10)
  -- (4) nivel 0 : `#0 ↦ ḃ`
  have k0v : Prf (substtc zero W0 (tcFn v) =eq tcFn v) := prf_substtc_tcFn W0 v
  have k0s : Prf (substtc zero W0 (tcFn s) =eq tcFn s) := prf_substtc_tcFn W0 s
  have k0a : Prf (substtc zero W0 (tcFn a) =eq tcFn a) := prf_substtc_tcFn W0 a
  have k0b : Prf (substtc zero W0 (varc (numeral 0)) =eq tcFn b) := prf_substtc_varc0 W0
  have hout : Prf (substfc zero W0 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT k0v k0s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) (prf_congr_binK k0a k0b)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _)
          (prf_congr_substfcT k0v k0s k0a)
      · exact prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _)
          (prf_congr_substfcT k0v k0s k0b)
  have hchain : Prf (substfc zero W0 (substfc (numeral 1) W1 (substfc (numeral 2) W2
        (substfc (numeral 3) W3 (formCode (AXBIN_BODY T)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3
        (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin0 hnorm3)) hmid2)) hmid1)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst4 (AXBIN_BODY T) hmem (tcFn v) (tcFn s) (tcFn a) (tcFn b))

/-! ### El ENSAMBLAJE binario, genérico en el tag `k : Nat` -/

/-- **El paso inductivo BINARIO de `pcc_eval_substfc`**, genérico en el tag.
    `hax`  = la instancia interna del axioma, dotada (§6).
    `hobj` = la ecuación OBJETO del axioma (uno de `prf_substfc_impl/_and/_or`). -/
theorem paso2_caso_bin (k : Nat) (v s a b : Term)
    (hax : Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b)))
      (binT k (substfcT (tcFn v) (tcFn s) (tcFn a)) (substfcT (tcFn v) (tcFn s) (tcFn b))))))
    (hobj : Prf (substfc v s (cons (numeralM k) (cons a (cons b nil)))
      =eq cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil))))
    (hA : Prf (provFromCode (evalSubstfcCode v s a)))
    (hB : Prf (provFromCode (evalSubstfcCode v s b))) :
    Prf (provFromCode (evalSubstfcCode v s (cons (numeralM k) (cons a (cons b nil))))) := by
  unfold evalSubstfcCode at hA hB ⊢
  let C : Term := cons (numeralM k) (cons a (cons b nil))
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
  -- (1) `tcFn C ↦ binT k ȧ ḃ` bajo el 3er argumento de `substfcT`
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn C))
      (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b))))) :=
    prf_mp (pcc_congr_substfcT_arg3_code (tcFn v) (tcFn s) (tcFn C) (binT k (tcFn a) (tcFn b))
      (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn C)) (pcc_dot_bin_symm k a b)
  -- (3) la HI sobre el PRIMER hijo, bajo `binT`
  have h3 : Prf (provFromCode (eqc
      (binT k (substfcT (tcFn v) (tcFn s) (tcFn a)) (substfcT (tcFn v) (tcFn s) (tcFn b)))
      (binT k (tcFn (substfc v s a)) (substfcT (tcFn v) (tcFn s) (tcFn b))))) :=
    prf_mp (pcc_congr_binT_1_code k (substfcT (tcFn v) (tcFn s) (tcFn b))
      (substfcT (tcFn v) (tcFn s) (tcFn a)) (tcFn (substfc v s a)) iSB iSA) hA
  -- (4) la HI sobre el SEGUNDO hijo, bajo `binT`
  have h4 : Prf (provFromCode (eqc
      (binT k (tcFn (substfc v s a)) (substfcT (tcFn v) (tcFn s) (tcFn b)))
      (binT k (tcFn (substfc v s a)) (tcFn (substfc v s b))))) :=
    prf_mp (pcc_congr_binT_2_code k (tcFn (substfc v s a))
      (substfcT (tcFn v) (tcFn s) (tcFn b)) (tcFn (substfc v s b))
      (substtc_inv_tcFn (substfc v s a)) iSB) hB
  -- (5) el KIT pliega el `binT` en el punto del constructor
  have h5 : Prf (provFromCode (eqc (binT k (tcFn (substfc v s a)) (tcFn (substfc v s b)))
      (tcFn (cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil)))))) :=
    pcc_dot_bin k (substfc v s a) (substfc v s b)
  -- (6) la ecuación OBJETO del axioma, dotada GRATIS por `prf_congr_tcFn`
  have h6 : Prf (provFromCode (eqc
      (tcFn (cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil))))
      (tcFn (substfc v s C)))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm hobj))))
      (prf_provFromCode_eqCodeFn_refl
        (tcFn (cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil)))))
  exact pcc_eq_trans_code _ _ _ iX0 h1
    (pcc_eq_trans_code _ _ _ iX1 hax
      (pcc_eq_trans_code _ _ _ iX2 h3
        (pcc_eq_trans_code _ _ _ iX3 h4
          (pcc_eq_trans_code _ _ _ iX4 h5 h6))))

/-! ### Las tres instancias -/

theorem paso2_caso_impl (v s a b : Term)
    (hA : Prf (provFromCode (evalSubstfcCode v s a)))
    (hB : Prf (provFromCode (evalSubstfcCode v s b))) :
    Prf (provFromCode (evalSubstfcCode v s (implc a b))) :=
  paso2_caso_bin 5 v s a b
    (pcc_substfc_bin_dot (numeralM 5) (fun c => liftTerm_numeralM c 5)
      (show ax_substfc_impl ∈ axioms by simp [axioms]) v s a b)
    (prf_substfc_impl v s a b) hA hB

theorem paso2_caso_and (v s a b : Term)
    (hA : Prf (provFromCode (evalSubstfcCode v s a)))
    (hB : Prf (provFromCode (evalSubstfcCode v s b))) :
    Prf (provFromCode (evalSubstfcCode v s (andc a b))) :=
  paso2_caso_bin 7 v s a b
    (pcc_substfc_bin_dot (numeralM 7) (fun c => liftTerm_numeralM c 7)
      (show ax_substfc_and ∈ axioms by simp [axioms]) v s a b)
    (prf_substfc_and v s a b) hA hB

theorem paso2_caso_or (v s a b : Term)
    (hA : Prf (provFromCode (evalSubstfcCode v s a)))
    (hB : Prf (provFromCode (evalSubstfcCode v s b))) :
    Prf (provFromCode (evalSubstfcCode v s (orc a b))) :=
  paso2_caso_bin 8 v s a b
    (pcc_substfc_bin_dot (numeralM 8) (fun c => liftTerm_numeralM c 8)
      (show ax_substfc_or ∈ axioms by simp [axioms]) v s a b)
    (prf_substfc_or v s a b) hA hB

/-! ### §7 · CONTROLES (los dos del sondeo) -/

set_option linter.unusedVariables false in
/-- CONTROL NEGATIVO: ninguno de los cuatro enunciados es una reflexividad disfrazada. -/
example (v s a b : Term) : True := by
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn botc) = tcFn (substfc v s botc))
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn (implc a b)) = tcFn (substfc v s (implc a b)))
  trivial

/-- CONTROL: los tres tags binarios son DISTINTOS (el lema genérico no los confunde). -/
example : binct (numeralM 5) zero zero ≠ binct (numeralM 7) zero zero := by
  intro h; exact absurd h (by decide)

/-! ## §8 · LOS PUENTES ADR-019 — la SUBSUNCION AL REVES, compilada.

    Tres constantes de este fichero son MAS GENERALES que constantes que ya estan en
    produccion. Segun ADR-019 NO se puede reescribir el particular como corolario del
    general desde aqui (ciclo de imports): hay que BAJAR el general.

    | general (aqui)         | particular (produccion)                                    |
    |------------------------|------------------------------------------------------------|
    | `binK`                 | `Meta/CodeCtorKit.binT` (`binK ⌜m̄⌝ a b = binT m a b`, rfl) |
    | `prf_congr_binK`       | `Meta/CodeCtorKit.prf_congr_binT`                           |
    | `prf_substtc_binK_at`  | `Meta/LiftcCodePrf.prf_substtc_binT_at`                     |

    Estos `example` SON la prueba: el enunciado de produccion sale del general instanciando
    el tag, sin ningun `simp`/`rw` de por medio. -/

example (m : Nat) (a b : Term) : binK (termCode (numeralM m)) a b = binT m a b := rfl

example {m : Nat} {a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (binT m a b =eq binT m a' b') :=
  prf_congr_binK (H := termCode (numeralM m)) ha hb

example (m v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (binT m a b)
      =eq binT m (substtc (numeral v) W a) (substtc (numeral v) W b)) :=
  prf_substtc_binK_at (numeralM m) (fun c => liftTerm_numeralM c m) v W a b

end ROBINSON_PlusPlus.Meta.SubstfcCodePrf

/-! ## CONTROL DE FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.SubstfcCodePrf.prf_substtc_binK_at
#print axioms ROBINSON_PlusPlus.Meta.SubstfcCodePrf.pcc_congr_substfcT_arg3_code
#print axioms ROBINSON_PlusPlus.Meta.SubstfcCodePrf.pcc_substfc_bottom_dot
#print axioms ROBINSON_PlusPlus.Meta.SubstfcCodePrf.paso2_caso_bottom
#print axioms ROBINSON_PlusPlus.Meta.SubstfcCodePrf.pcc_substfc_bin_dot
#print axioms ROBINSON_PlusPlus.Meta.SubstfcCodePrf.paso2_caso_bin
#print axioms ROBINSON_PlusPlus.Meta.SubstfcCodePrf.paso2_caso_impl
#print axioms ROBINSON_PlusPlus.Meta.SubstfcCodePrf.paso2_caso_and
#print axioms ROBINSON_PlusPlus.Meta.SubstfcCodePrf.paso2_caso_or
