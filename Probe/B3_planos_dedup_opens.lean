/- # `Probe/B3_planos_dedup_opens.lean` — el MISMO texto, bajo los `open` DEL SONDEO.

   Arnes 3 de 3 del angulo (B) sobre `sondeos/SubstfcPlanos.lean`.
   Cabecera copiada LITERALMENTE de la del sondeo (import del barrel + las 13 lineas de
   `open`), porque el mismo texto con `open`s distintos elabora DISTINTO. Aqui se comprueba:

     (1) que las CINCO declaraciones que el sondeo duplica por NOMBRE tienen, bajo estos
         `open`, exactamente el tipo de la constante de PRODUCCION (o sea: borrarlas del
         sondeo es drop-in, no hay ambiguedad de resolucion ni otra constante homonima);
     (2) que los puentes `rfl` del sondeo siguen siendo `rfl` aqui;
     (3) que `binct` subsume SEIS constructores de codigo OBJETO de `Minimal/Axioms.lean`;
     (4) los controles negativos.

   CERO axiomas de Lean nuevos, CERO `sorry`. -/
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

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace B3PlanosOpens

/-! ## §1 · LOS CINCO DUPLICADOS EXACTOS POR NOMBRE

    El sondeo redeclara cinco lemas que YA estan en produccion, con el mismo nombre y (medido
    por md5 del texto de la declaracion) el mismo cuerpo:

      `prf_substtc_termCode_closed`   ← `Meta/LiftcCodePrf.lean`  (promovido en B1)
      `prf_substtc_termCode_numeralM` ← `Meta/LiftcCodePrf.lean`  (promovido en B1)
      `prf_substtc_termCode_zero`     ← `Meta/LiftcCodePrf.lean`  (promovido en B1)
      `pcc_thm_inst4`                 ← `Meta/MpCodePrf.lean`     (promovido 2026-08-31 DESDE
      `pcc_axiom_inst4`               ← `Meta/MpCodePrf.lean`      ESTE MISMO SONDEO)

    ⚠️ El docstring del sondeo («`pcc_thm_inst4`/`pcc_axiom_inst4` — no existian en produccion
    (solo hasta `inst3`)») es FALSO desde esa promocion; `Meta/MpCodePrf.lean` lo dice en su
    propio §N+1. Los cinco NO se promueven: se BORRAN del sondeo.

    Cada `example` de abajo tiene el enunciado LITERAL del sondeo y lo cierra con la constante
    de PRODUCCION. Si bajo estos `open` la resolucion fuera a otra constante, o el tipo no
    coincidiera, aqui falla. -/

example (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) :=
  prf_substtc_termCode_closed v W t ht

example (v m : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  prf_substtc_termCode_numeralM v m W

example (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  prf_substtc_termCode_zero v W

example (φ : Formula) (h : Prf (forall_4 φ)) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
  pcc_thm_inst4 φ h w₁ w₂ w₃ w₄

example (φ : Formula) (hmem : forall_4 φ ∈ axioms) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
  pcc_axiom_inst4 φ hmem w₁ w₂ w₃ w₄

/-- Y la CONSTANTE es la de produccion, no una homonima: se nombra con el `open` y con el
    nombre completo, y son la MISMA. -/
example : @pcc_thm_inst4 = @ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_thm_inst4 := rfl
example : @prf_substtc_termCode_closed
    = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_closed := rfl

/-! ### El SEXTO, que no es del sondeo pero lo toca: `pcc_thm_inst4` tiene HOY en produccion
     la prueba LARGA (42 lineas, la que salio de este sondeo). `sondeos/EvalSubsttc.lean`
     trae la MISMA proposicion con una prueba de 20 lineas, como corolario de `pcc_thm_inst3`
     (y escrita con `succ zero`/`succ (succ zero)` en vez de `numeral 1`/`numeral 2`, que es
     lo mismo por `rfl`). No es asunto de esta promocion, pero conviene no promover la version
     de `EvalSubsttc` como si fuera otra cosa: es un TERCER duplicado de la misma. -/

example : numeral 1 = succ zero := rfl
example : numeral 2 = succ (succ zero) := rfl
example : numeral 3 = succ (succ (succ zero)) := rfl

/-! ## §2 · Los puentes `rfl` del sondeo, bajo SUS `open` -/

def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))

theorem substfcT_termCode (v s f : Term) :
    substfcT (termCode v) (termCode s) (termCode f) = termCode (substfc v s f) := rfl

def binK (H a b : Term) : Term := consT H (consT a (consT b (termCode nil)))
theorem binK_binT (m : Nat) (a b : Term) : binK (termCode (numeralM m)) a b = binT m a b := rfl

def binct (T a b : Term) : Term := cons T (cons a (cons b nil))
theorem binct_implc (a b : Term) : binct (numeralM 5) a b = implc a b := rfl
theorem binct_andc (a b : Term) : binct (numeralM 7) a b = andc a b := rfl
theorem binct_orc (a b : Term) : binct (numeralM 8) a b = orc a b := rfl

def AXBOT_BODY : Formula := substfc (.var 1) (.var 0) botc =eq botc
theorem AXBOT_BODY_ok : ax_substfc_bottom = forall_2 AXBOT_BODY := rfl

def AXBIN_BODY (T : Term) : Formula :=
  substfc (.var 3) (.var 2) (binct T (.var 1) (.var 0))
    =eq binct T (substfc (.var 3) (.var 2) (.var 1)) (substfc (.var 3) (.var 2) (.var 0))

theorem AXBIN_impl : ax_substfc_impl = forall_4 (AXBIN_BODY (numeralM 5)) := rfl
theorem AXBIN_and : ax_substfc_and = forall_4 (AXBIN_BODY (numeralM 7)) := rfl
theorem AXBIN_or : ax_substfc_or = forall_4 (AXBIN_BODY (numeralM 8)) := rfl

/-! ## §3 · SUBSUNCION AL REVES (nivel OBJETO): `binct` cubre SEIS constructores de
     `Minimal/Axioms.lean`, no los tres que el sondeo declara.

     `funcc` (tag 1), `atomc` (3), `eqc` (4), `implc` (5), `andc` (7), `orc` (8) son todos
     `cons tag (cons a (cons b nil))`. Los seis puentes son `rfl`. Consecuencia practica:
     si `binct` se promueve, su sitio natural es `Minimal/Axioms.lean` (donde viven los seis),
     NO un modulo de `Meta/`; y entonces `binct_implc`/`_andc`/`_orc` no son tres puentes
     sueltos sino tres de una familia de seis. -/

theorem binct_funcc (sc tsc : Term) : binct (numeralM 1) sc tsc = funcc sc tsc := rfl
theorem binct_atomc (pc tsc : Term) : binct (numeralM 3) pc tsc = atomc pc tsc := rfl
theorem binct_eqc (a b : Term) : binct (numeralM 4) a b = eqc a b := rfl

/-! ## §4 · CONTROLES NEGATIVOS -/

/-- Los tags binarios son realmente distintos: el lema generico no los confunde. -/
example : binct (numeralM 5) zero zero ≠ binct (numeralM 7) zero zero := by
  intro h; exact absurd h (by decide)
example : binct (numeralM 4) zero zero ≠ binct (numeralM 5) zero zero := by
  intro h; exact absurd h (by decide)

set_option linter.unusedVariables false in
/-- `binK` con etiqueta ABSTRACTA no colapsa a ningun `binT`, y `binct` no es `binK`. -/
example (H a b : Term) : True := by
  fail_if_success exact (rfl : binK H a b = binT 5 a b)
  fail_if_success exact (rfl : binct H a b = binK H a b)
  trivial

set_option linter.unusedVariables false in
/-- Y los cuatro titulares del sondeo NO son reflexividades disfrazadas. -/
example (v s a b : Term) : True := by
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn botc) = tcFn (substfc v s botc))
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn (implc a b)) = tcFn (substfc v s (implc a b)))
  trivial

end B3PlanosOpens

#print axioms B3PlanosOpens.substfcT_termCode
#print axioms B3PlanosOpens.binK_binT
#print axioms B3PlanosOpens.binct_funcc
#print axioms B3PlanosOpens.binct_atomc
#print axioms B3PlanosOpens.binct_eqc
#print axioms B3PlanosOpens.AXBIN_impl
#print axioms B3PlanosOpens.AXBOT_BODY_ok
