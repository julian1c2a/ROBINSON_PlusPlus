/-
Probe/VER_extra.lean — VERIFICACION ADVERSARIAL de la tanda B2 (T2_higiene).

Sin barrel: se importan SOLO los dos modulos necesarios, para que nadie pueda decir
que la medida se apoya en algo aguas abajo de `CodeWitnessPrf`.
-/
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.RunFnBoundedPrf

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert

namespace VerExtra
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf

/-! ## HALLAZGO 1 · DOS duplicados por ENUNCIADO que el auditor NO listo, y que
    ADEMAS estan LOS CUATRO en su bloque `export`: `prf_shapeUn_str` / `prf_shapeUn_str'`
    y `prf_shapeBin_str` / `prf_shapeBin_str'`. No comparten NOMBRE (por eso su censo de
    homonimos no los vio) pero tienen el MISMO enunciado. -/

theorem extra_dup_shapeUn : @SinWTs.prf_shapeUn_str = @ENS.prf_shapeUn_str' := rfl
theorem extra_dup_shapeBin : @SinWTs.prf_shapeBin_str = @ENS.prf_shapeBin_str' := rfl

/-- CONTROL NEGATIVO: la tecnica discrimina — Un contra Bin NO pasa, en los dos sentidos. -/
example : True := by
  fail_if_success (exact (rfl : @SinWTs.prf_shapeUn_str = @ENS.prf_shapeBin_str'))
  fail_if_success (exact (rfl : @SinWTs.prf_shapeBin_str = @ENS.prf_shapeUn_str'))
  fail_if_success (exact (rfl : @SinWTs.prf_shapeUn_str = @ENS.prf_shapeNul_str))
  trivial

/-- Y son intercambiables de verdad: el de `ENS` prueba el enunciado del de `SinWTs`
    LITERALMENTE, sin puente ninguno. Eso es lo que hace redundante a uno de los dos. -/
theorem shapeUn_str'_es_redundante (X : Term) (k : Nat) :
    Prf (Formula.impl (SinWTs.shapeUn X k)
      (land (SinWTs.consOk X) (land (carc X =eq numeralM k) (lenc X =eq numeralM 2)))) :=
  ENS.prf_shapeUn_str' X k

theorem shapeUn_str_es_el_mismo (X : Term) (k : Nat) :
    Prf (Formula.impl (SinWTs.shapeUn X k)
      (land (SinWTs.consOk X) (land (carc X =eq numeralM k) (lenc X =eq numeralM 2)))) :=
  SinWTs.prf_shapeUn_str X k

/-! ## HALLAZGO 2 · un tercer redundante, este contra OTRO modulo de produccion:
    `SinWTs.prf_congr_lenc` tiene el mismo enunciado que
    `Meta/RunFnBoundedPrf.prf_eq_congr_lenc`. -/

theorem extra_dup_lenc :
    @SinWTs.prf_congr_lenc
      = @ROBINSON_PlusPlus.Meta.RunFnBoundedPrf.prf_eq_congr_lenc := rfl

end VerExtra

#print axioms VerExtra.extra_dup_shapeUn
#print axioms VerExtra.extra_dup_shapeBin
#print axioms VerExtra.extra_dup_lenc
