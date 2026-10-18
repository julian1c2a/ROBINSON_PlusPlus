import ROBINSON_PlusPlus

/-!
# Rosser, Etapa 0: la mitad BASURA — refutar en `Prf` la guarda de TÉRMINO sobre un numeral (ADR‑125/126)

✏️ **2026‑10‑18 (ADR‑160, T66): queda sólo §5**, el control con el modelo; §1–§4, que lo de abajo describe, se
retiraron (ver su lugar en el fichero). El resto de esta cabecera es el REGISTRO de lo que medía el 2026‑10‑05.

**Fecha**: 2026‑10‑05. Es la segunda pieza de la Etapa 0 del plan de Rosser (ADR‑122 §2; la primera, la reflexión,
en `sondeos/RosserReflexion.lean`): donde la guarda es FALSA, la reflexión no da nada y hay que REFUTARLA en `Prf`.

**Qué dice** (la guarda ENTERA, con su `∃` eliminado, y por primera vez sobre un NUMERAL):

    Prf (¬ hasWit 0̄)                                         -- el 0 (= nil) no es código de término
    Prf (¬ hasWit c)   para c cerrado con Prf (carc c = k̄), k ∉ {0, 1}
    Prf (¬ hasWit (consN k r)‾)   para todo k ∉ {0, 1} y todo r     -- un numeral, sin hipótesis
    Prf (¬ hasWit [1, s, [0]]‾)    para todo s                     -- la basura, en el ÚNICO argumento (ADR‑126)

`[1, s, [0]]` es la lista de TRES elementos `consN 1 (consN s (consN (consN 0 0) 0))`: etiqueta `1`, casilla de
símbolo `s` (que la guarda no mira) y una lista de UN argumento, el `0`. «Profundidad» cuenta aquí PROYECCIONES hasta
el dato que falla (0: el numeral es `0`; 1: su etiqueta; 2: un argumento); en el ÁRBOL del término, la basura de
`[1, s, [0]]` está a profundidad 1.

Y un control (`control_codigo_no_refutable`): sobre el numeral del código CANÓNICO de cualquier término, `¬ hasWit`
NO es demostrable en `Prf` por ningún método —la solidez en `MNV V₀` lo impide, porque allí esa guarda es verdadera—.
No mide el método sino la guarda: `¬ hasWit` no es demostrable en todas partes, así que lo refutado depende de la
basura. Sólo códigos canónicos; la forma general (`hasWitN c → ¬ Prf ¬hasWit c̄`) sale igual y no está escrita.

**Precedentes** (✏️ auditoría `wf_e04d70c1-e0c`): la guarda ENTERA ya se había refutado en `Prf` sobre términos
CERRADOS —no numerales— con la misma prueba que §2: `CRIT_hasWit_rejects` (`sondeos/MedirC_Deriva.lean`) y
`CRIT_hasWit_rejects_tag` (`sondeos/HasWitFCritica.lean`), y la de fórmula, `CRIT_hasWitF_rejects_tag` y
`CRIT_hasWitF_rejects_varc` (`sondeos/MedirC_Carga.lean`); ninguno compila hoy. Lo nuevo aquí es el NUMERAL, el `0`
y el caso del argumento.

**Cómo**: lo que había en `Meta/CodeWitnessPrf.lean` —el refutador de PROFUNDIDAD 1 con testigo abierto
(`prf_crit_In_rejects_open1`) y la forma de pertenencia de `wfAll1` (`prf_isTermCodeE1_of_In`)— más el `∃`‑elim
(`prf_ex_elim_imp`), el puente `∈ → índice` (`prf_boundedIn_of_In`), y, para el numeral, `carc ⟨k, r⟩‾ = k̄` por
`prf_cons_eval`. Lo nuevo: `0 ≠ cons a b` en `Prf` (por los axiomas de lista L1/L2) y la congruencia de `carc` en
`Prf` (la de `PrfH` ya estaba: `PrfH_eq_congr_carc`; ✏️ desde ADR‑150, con la etiqueta de `⟨k, r⟩‾` y
`prf_cons_evalM`, en el build: `Meta/RosserNumerales.lean`). A
profundidad 2 (§4): la forma `B1` (`prf_isTermCodeE1_str`); su rama de variable cae por la etiqueta
(`crit_cOk2_absurd`); la de función da `argsIn`, instanciado en `0` (`PrfH_inst_argsIn`), con `nthc`/`lenc`
evaluados sobre el numeral (`prf_nthc_c2`, `prf_lenc_c1`, `prf_nthc_zero`), y el `0` cae por §1.

⚠️ Lo que NO dice: la versión hereditaria GENERAL (por inducción sobre el numeral: aquí hay UN caso, con un
argumento); la etiqueta buena con forma mala (`[0]‾`, `[1, s]‾`: longitud distinta de 2 o 3), que ningún titular
cubre; nada de `hasWitF`; ni una línea `q1` basura.

## Medido (2026‑10‑05, RPP con ADR‑124)

Compila en 4 s (1,07 GB), 0 errores y 0 avisos; 217 líneas, 14 teoremas (`wc -l`). `#print axioms` de los
cuatro titulares: `[propext, Classical.choice, Quot.sound]`. La §4 compiló a la tercera; la §5, a la primera.

## Cómo re‑ejecutarlo

    lake env lean sondeos/RosserBasura.lean      # desde la raíz de RPP
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.RosserNumerales

namespace RosserBasura

/-! ## §1–§4 · ✏️ RETIRADOS el 2026‑10‑18 (ADR‑160, T66)

Las refutaciones a profundidad 0, 1 y 2 (`prf_neg_hasWit_zero`, `prf_neg_hasWit_tag`, `prf_neg_hasWit_num`,
`prf_neg_hasWit_prof2` y sus lemas) se retiraron: sus tres lemas de lista pasaron al build en ADR‑150
(`Meta/RosserNumerales.lean`), y la refutación de la guarda, GENERAL, en ADR‑153 (`Meta/RosserGuardNeg.lean`:
`prf_neg_hasWit`, para todo numeral cuya guarda es falsa en ℕ). Era el plan de ADR‑146 §4.6: «el sondeo se queda con
§5, su control con el modelo». La versión entera, en la etiqueta `archivo/t66-2026-10-18`. -/

/-! ## §5 · Control: sobre un código CANÓNICO, `¬ hasWit` no es demostrable

No mide el método sino la guarda: por la solidez (`prf_sound`) y la guarda que ya se demostraba
(`prf_hasWit_termCodeM`), `¬ hasWit` no es demostrable en `Prf` sobre el numeral del código de NINGÚN término; lo
refutado en §1–§4 depende, pues, de la basura. Sólo códigos canónicos. -/

theorem control_codigo_no_refutable (t : Term) : ¬ Prf (neg (hasWit (numeralM (codeNatTerm t)))) := by
  intro h
  have hs := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN h (fun _ => 0)
  have hw := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN
    (ROBINSON_PlusPlus.Meta.SubstTreeReflect.prf_hasWit_termCodeM t) (fun _ => 0)
  apply hs
  rw [ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_hasWit, ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM]
  rw [ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_hasWit, ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_termCodeM] at hw
  exact hw

end RosserBasura

#print axioms RosserBasura.control_codigo_no_refutable
