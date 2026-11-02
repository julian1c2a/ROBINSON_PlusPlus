/- # `Probe/B3_planos_dedup_kit.lean` — el TEST DE DESTINO (ADR-019) sobre `Meta/CodeCtorKit.lean`.

   Arnes 2 de 3 del angulo (B) sobre `sondeos/SubstfcPlanos.lean`.

   ⚠️ **LA LISTA DE `import` DE ESTE FICHERO ES, BYTE A BYTE, LA DE
   `ROBINSON_PlusPlus/Meta/CodeCtorKit.lean`**: dos modulos, `LineWFSchemaPrf` y
   `LineWFTrackedPrf`. NI `CodeCtorKit` mismo, NI el barrel, NI nada aguas abajo. Ese es el
   test: lo que compila AQUI cabe en `CodeCtorKit` sin ciclo de imports.

   Consecuencia deliberada: `binT`, `unT`, `prf_congr_binT`, `prf_substtc_binT`,
   `pcc_congr_binT_1_code`… NO estan visibles, porque `CodeCtorKit` es quien los DECLARA.
   Lo que hace falta de ellos se REDECLARA con prefijo `K_`, copiado verbatim del modulo.
   `consT`/`prf_congr_consT`/`prf_substtc_consT` si llegan (viven en `Meta/DotConsPrf.lean`,
   aguas arriba), asi que de esos se usa la constante REAL de produccion.

   Lo que se prueba aqui:
     §1 — `binK` (del sondeo) subsume a `binT`, y `prf_congr_binK` a `prf_congr_binT`.
          A `CodeCtorKit` no le falta ninguna constante para alojar el general.
     §2 — `pcc_congr_hole_code`: UN lema generico que subsume las SIETE copias del mismo
          patron de 12 lineas que produccion ya tiene, MAS la octava que trae el sondeo
          (`pcc_congr_substfcT_arg3_code`). Tambien cabe en `CodeCtorKit`.

   CERO axiomas de Lean nuevos, CERO `sorry`. -/
import ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
import ROBINSON_PlusPlus.Meta.LineWFTrackedPrf

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
open ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.BdAllIntroPrf

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace B3PlanosKit

/-! ## §0 · Lo que `CodeCtorKit` DECLARA (y por tanto aqui no llega), copiado verbatim.
     Prefijo `K_` para que no haya duda de que no es la constante de produccion. -/

def K_unT (m : Nat) (a : Term) : Term := consT (termCode (numeralM m)) (consT a (termCode nil))

def K_binT (m : Nat) (a b : Term) : Term :=
  consT (termCode (numeralM m)) (consT a (consT b (termCode nil)))

theorem K_prf_congr_unT {m : Nat} {a a' : Term} (ha : Prf (a =eq a')) :
    Prf (K_unT m a =eq K_unT m a') := by
  unfold K_unT; exact prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_refl _))

theorem K_prf_congr_binT {m : Nat} {a a' b b' : Term}
    (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) : Prf (K_binT m a b =eq K_binT m a' b') := by
  unfold K_binT
  exact prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_congr_consT hb (prf_refl _)))

theorem K_prf_substtc_unT (m : Nat) (W a : Term) :
    Prf (substtc zero W (K_unT m a) =eq K_unT m (substtc zero W a)) := by
  unfold K_unT
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  refine prf_congr_consT (substtc_inv_termCode_numeralM m W) ?_
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  exact prf_congr_consT (prf_refl _)
    (ROBINSON_PlusPlus.Meta.LineWFTrackedPrf.substtc_inv_termCode_of_tc prf_tc_zero W)

theorem K_prf_substtc_binT (m : Nat) (W a b : Term) :
    Prf (substtc zero W (K_binT m a b) =eq K_binT m (substtc zero W a) (substtc zero W b)) := by
  unfold K_binT
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  refine prf_congr_consT (substtc_inv_termCode_numeralM m W) ?_
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  refine prf_congr_consT (prf_refl _) ?_
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  exact prf_congr_consT (prf_refl _)
    (ROBINSON_PlusPlus.Meta.LineWFTrackedPrf.substtc_inv_termCode_of_tc prf_tc_zero W)

/-! ## §1 · SUBSUNCION AL REVES nº 1 — `binK` ⊐ `binT`, y cabe en `CodeCtorKit`.

    `binK` es `binT` con la ETIQUETA como `Term` abstracto en vez de como `Nat`. Todo su
    vocabulario (`consT`, `termCode`, `prf_congr_consT`, `prf_refl`) es EXACTAMENTE el de
    `prf_congr_binT`, que ya vive ahi. -/

def binK (H a b : Term) : Term := consT H (consT a (consT b (termCode nil)))

/-- El puente del sondeo, recompilado contra la copia verbatim de `binT`: `rfl`. -/
theorem binK_binT (m : Nat) (a b : Term) : binK (termCode (numeralM m)) a b = K_binT m a b := rfl

theorem prf_congr_binK {H a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (binK H a b =eq binK H a' b') :=
  prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_congr_consT hb (prf_refl _)))

/-- **CONTROL ADR-019 (a)** — el enunciado LITERAL de `CodeCtorKit.prf_congr_binT` sale del
    general en un paso, sin `unfold`. Esta seria la reescritura al BAJAR `binK`. -/
theorem CTRL_prf_congr_binT_desde_binK {m : Nat} {a a' b b' : Term}
    (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) : Prf (K_binT m a b =eq K_binT m a' b') :=
  prf_congr_binK ha hb

/-- **CONTROL (b)** — `substtc` sobre `binK` a nivel `zero` tambien subsume
    `CodeCtorKit.prf_substtc_binT`, con una hipotesis de clausura sobre la etiqueta.
    (La version a nivel `numeral n` es la del sondeo y su destino es `LiftcCodePrf`, que es
    donde vive `prf_substtc_termCode_closed`; aqui solo se comprueba el caso `zero`.) -/
theorem prf_substtc_binK (H : Term) (hH : ∀ W, Prf (substtc zero W H =eq H))
    (W a b : Term) :
    Prf (substtc zero W (binK H a b) =eq binK H (substtc zero W a) (substtc zero W b)) := by
  unfold binK
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  refine prf_congr_consT (hH W) ?_
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  refine prf_congr_consT (prf_refl _) ?_
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  exact prf_congr_consT (prf_refl _)
    (ROBINSON_PlusPlus.Meta.LineWFTrackedPrf.substtc_inv_termCode_of_tc prf_tc_zero W)

theorem CTRL_prf_substtc_binT_desde_binK (m : Nat) (W a b : Term) :
    Prf (substtc zero W (K_binT m a b) =eq K_binT m (substtc zero W a) (substtc zero W b)) :=
  prf_substtc_binK (termCode (numeralM m)) (substtc_inv_termCode_numeralM m) W a b

/-! ## §2 · CASI-DUPLICADO nº 1 — el patron `pcc_congr_*_code`, SIETE veces en produccion.

    `Meta/CodeCtorKit.lean` tiene `pcc_congr_binT_2_code`, `pcc_congr_binT_1_code` y
    `pcc_congr_unT_code`; `Meta/LiftcCodePrf.lean` tiene `pcc_congr_liftcT_arg2_code`,
    `pcc_congr_liftscT_arg2_code`, `pcc_congr_consT_arg2_code` y `pcc_congr_consT_arg1_code`.
    Las SIETE son la MISMA prueba de 12 lineas cambiando el contexto. El sondeo trae la
    OCTAVA (`pcc_congr_substfcT_arg3_code`).

    Este `pcc_congr_hole_code` las subsume: el contexto entra como `F : Term → Term` y las dos
    unicas obligaciones son las que en cada copia se descargan a mano. Cabe en `CodeCtorKit`
    (mismo vocabulario que `pcc_congr_binT_2_code`), luego las siete pueden ser corolarios
    de una linea SIN ciclo de imports. -/

theorem pcc_congr_hole_code (F : Term → Term) (X Y : Term)
    (hinv : ∀ W, Prf (substtc zero W (F X) =eq F X))
    (hhole : ∀ w, Prf (substtc zero w (F (varc (numeral 0))) =eq F w)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (F X) (F Y))) := by
  let Ac : Term := eqc (F X) (F (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (F X) (F w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (F X) (F (varc (numeral 0)))) ?_
    exact prf_congr_eqCodeFn (hinv w) (hhole w)
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (F X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-! ### Las TRES copias de `CodeCtorKit`, como corolarios (enunciados LITERALES) -/

theorem CTRL_pcc_congr_binT_2_code (m : Nat) (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (K_binT m A X) (K_binT m A Y))) :=
  pcc_congr_hole_code (fun s => K_binT m A s) X Y
    (fun W => prf_eq_trans (K_prf_substtc_binT m W A X) (K_prf_congr_binT (hA W) (hX W)))
    (fun w => prf_eq_trans (K_prf_substtc_binT m w A (varc (numeral 0)))
      (K_prf_congr_binT (hA w) (prf_substtc_varc0 w)))

theorem CTRL_pcc_congr_binT_1_code (m : Nat) (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (K_binT m X B) (K_binT m Y B))) :=
  pcc_congr_hole_code (fun s => K_binT m s B) X Y
    (fun W => prf_eq_trans (K_prf_substtc_binT m W X B) (K_prf_congr_binT (hX W) (hB W)))
    (fun w => prf_eq_trans (K_prf_substtc_binT m w (varc (numeral 0)) B)
      (K_prf_congr_binT (prf_substtc_varc0 w) (hB w)))

theorem CTRL_pcc_congr_unT_code (m : Nat) (X Y : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (K_unT m X) (K_unT m Y))) :=
  pcc_congr_hole_code (fun s => K_unT m s) X Y
    (fun W => prf_eq_trans (K_prf_substtc_unT m W X) (K_prf_congr_unT (hX W)))
    (fun w => prf_eq_trans (K_prf_substtc_unT m w (varc (numeral 0)))
      (K_prf_congr_unT (prf_substtc_varc0 w)))

/-! ### Y las DOS de `consT` de `LiftcCodePrf`, con el `consT` REAL de produccion.
     Salen ya AQUI, o sea aguas ARRIBA de donde hoy estan escritas: prueba de que esas dos
     tampoco necesitaban modulo propio. -/

theorem CTRL_pcc_congr_consT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT A X) (consT A Y))) :=
  pcc_congr_hole_code (fun s => consT A s) X Y
    (fun W => prf_eq_trans (prf_substtc_consT zero W A X) (prf_congr_consT (hA W) (hX W)))
    (fun w => prf_eq_trans (prf_substtc_consT zero w A (varc (numeral 0)))
      (prf_congr_consT (hA w) (prf_substtc_varc0 w)))

theorem CTRL_pcc_congr_consT_arg1_code (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT X B) (consT Y B))) :=
  pcc_congr_hole_code (fun s => consT s B) X Y
    (fun W => prf_eq_trans (prf_substtc_consT zero W X B) (prf_congr_consT (hX W) (hB W)))
    (fun w => prf_eq_trans (prf_substtc_consT zero w (varc (numeral 0)) B)
      (prf_congr_consT (prf_substtc_varc0 w) (hB w)))

/-! ## §3 · CONTROLES NEGATIVOS -/

set_option linter.unusedVariables false in
/-- `binK` con etiqueta ABSTRACTA no colapsa a `binT` de ningun tag concreto. -/
example (H a b : Term) : True := by
  fail_if_success exact (rfl : binK H a b = K_binT 5 a b)
  fail_if_success exact (rfl : binK H a b = K_binT 7 a b)
  trivial

/-- Y `binK` alcanza etiquetas fuera del rango de `binT` (p. ej. el codigo de una cadena). -/
example (a b : Term) : Term := binK (termCode (strCode "liftc")) a b

end B3PlanosKit

#print axioms B3PlanosKit.binK_binT
#print axioms B3PlanosKit.prf_congr_binK
#print axioms B3PlanosKit.CTRL_prf_congr_binT_desde_binK
#print axioms B3PlanosKit.CTRL_prf_substtc_binT_desde_binK
#print axioms B3PlanosKit.pcc_congr_hole_code
#print axioms B3PlanosKit.CTRL_pcc_congr_binT_2_code
#print axioms B3PlanosKit.CTRL_pcc_congr_binT_1_code
#print axioms B3PlanosKit.CTRL_pcc_congr_unT_code
#print axioms B3PlanosKit.CTRL_pcc_congr_consT_arg2_code
#print axioms B3PlanosKit.CTRL_pcc_congr_consT_arg1_code
