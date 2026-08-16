/-
PILOTO DE LA FASE 2 (PLAN-SORTES §4bis) — NO ES MÓDULO DE PRODUCCIÓN.

Re-prueba UN sitio de `InAxiomsCodePrf` por la ruta NUMERAL, y demuestra la independencia
de la lectura sintáctica de `tcFn` por **aislamiento de importaciones**:

  * `SubstCodeOpenPrf` y `DerivCondPrf` NO alcanzan `TcArithPrf` (verificado: 27 y 32 módulos).
  * Este fichero importa SÓLO esos dos.
  * ⟹ `prf_tc_form` / `prf_tc_of_cons` / `prf_tc_cons` NO EXISTEN en este entorno.
  * ⟹ si compila, no puede estar usándolos. Airtight a nivel de módulo.

Los `#noExiste` de abajo hacen el aislamiento comprobado por máquina: si alguien añade el
import, el fichero deja de compilar.
-/
import Lean
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.DerivCondPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open FOL

/-! ## 1 · El aislamiento, comprobado por máquina -/

open Lean Elab Command in
/-- Falla si `id` EXISTE en el entorno. Certifica que el piloto no puede usarlo. -/
elab "#noExiste " id:ident : command => do
  if ((← getEnv).find? id.getId).isSome then
    throwError "AISLAMIENTO ROTO: {id.getId} sí está en el entorno"
  else
    logInfo m!"ausente del entorno ✔  {id.getId}"

#noExiste ROBINSON_PlusPlus.Meta.TcArithPrf.prf_tc_form
#noExiste ROBINSON_PlusPlus.Meta.TcArithPrf.prf_tc_of_cons
#noExiste ROBINSON_PlusPlus.Meta.TcArithPrf.prf_tc_cons
#noExiste ROBINSON_PlusPlus.Meta.TcArithPrf.prf_tc_term
#noExiste ROBINSON_PlusPlus.Meta.InAxiomsCodePrf.prf_tc_listFormCodeM

/-! ## 2 · El piloto: la misma proposición, por la ruta numeral -/

namespace Piloto

/-- **PILOTO.** Tipo IDÉNTICO al de
    `ROBINSON_PlusPlus.Meta.InAxiomsCodePrf.substtc_inv_termCode_listFormCodeM`.

    Ruta: `prf_substtc_arith_open` computa `substtc` sobre `termCode` usando sólo las ecuaciones
    de variable de `substtc`; `substCodeT_closed` cierra el lado meta porque `listFormCodeM L`
    es un término cerrado (`liftTerm_listFormCodeM`). `tcFn` no interviene. -/
theorem substtc_inv_termCode_listFormCodeM (L : List Formula) (W : Term) :
    Prf (substtc zero W (termCode (listFormCodeM L)) =eq termCode (listFormCodeM L)) := by
  have h := prf_substtc_arith_open 0 W (listFormCodeM L)
  rw [substCodeT_closed 0 W _ (fun c => liftTerm_listFormCodeM c L)] at h
  exact h

/-- Mismo argumento para `formCode φ`. -/
theorem substtc_inv_termCode_formCode (φ : Formula) (W : Term) :
    Prf (substtc zero W (termCode (formCode φ)) =eq termCode (formCode φ)) := by
  have h := prf_substtc_arith_open 0 W (formCode φ)
  rw [substCodeT_closed 0 W _
    (fun c => ROBINSON_PlusPlus.Meta.DerivCondPrf.liftTerm_formCode c φ)] at h
  exact h

/-- **El caso general**, que SUSTITUYE a `substtc_inv_termCode_of_tc` eliminando su hipótesis
    `tcFn a =eq termCode a` — la hipótesis que obligaba a la lectura sintáctica. -/
theorem substtc_inv_termCode_closed (a : Term) (ha : ∀ c : Nat, liftTerm c a = a) (W : Term) :
    Prf (substtc zero W (termCode a) =eq termCode a) := by
  have h := prf_substtc_arith_open 0 W a
  rw [substCodeT_closed 0 W _ ha] at h
  exact h

end Piloto

/-! ## 3 · Auditoría de axiomas de Lean -/

#print axioms Piloto.substtc_inv_termCode_listFormCodeM
#print axioms Piloto.substtc_inv_termCode_formCode
#print axioms Piloto.substtc_inv_termCode_closed
