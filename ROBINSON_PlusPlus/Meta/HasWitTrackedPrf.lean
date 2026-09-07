import ROBINSON_PlusPlus.Meta.TrackedAtomsPrf
import ROBINSON_PlusPlus.Meta.LineWFGuardPrf
/-!
# `Meta/HasWitTrackedPrf.lean` — el descenso de `DEUDA_hGuardT` hasta UNA obligación

`Meta/LineWFGuardPrf.lean` dejó la deuda de ADR‑020 en **dos** lemas genéricos,
`DEUDA_hGuardT` y `DEUDA_hGuardF`. Este módulo baja el primero un escalón más y, sobre todo,
**mide dónde está el contenido**.

## El descenso

    hasWit c   =  ∃w. isTC1 w ↑c                            (`Minimal/Axioms.lean:1052`)
    isTC1 w c  =  wfAll1 w ∧ In c w                         (`Minimal/Axioms.lean:1049`)

⭐ Esa segunda línea es **exactamente** la forma `isFCB w c = wfAll w ∧ In c w` que
`sondeos/A3IsFCBTracked.lean` reflejó entera (`pcc_isFCB_tracked`), y por eso el escalón sale
en cuatro líneas apoyado en el kit genérico que ya está en producción
(`Meta/TrackedAtomsPrf.lean`): la mitad derecha es `pcc_In_atom_tracked`, con `c` y `w`
**abstractos**.

⇒ Queda **una** obligación de contenido para esta mitad: reflejar el `∀` acotado `wfAll1`.

## ⚠️ Dónde está la dificultad real, medida

`wfAll1 w = ∀i < lenc w. isTermCodeE1 w (nthc w i)`, y se ataca con `pcc_bdAll_intro`
(`Meta/BdAllIntroPrf.lean:313`), cuya aplicación completa está ejercitada en aquel sondeo
(`pcc_wfAll_tracked`, ocho obligaciones administrativas descargadas). Pero:

> ⛔ **aquel `nodeOk` estaba diseñado para NO tener binders dentro del `∀` acotado** — el
> sondeo eligió a propósito meter el `In` como **átomo** y no como su despliegue `∃`‑acotado,
> «así el cuerpo del `∀` acotado no tiene ningún binder y todo el descenso de `substfc` vive en
> nivel 0» (`sondeos/A3IsFCBTracked.lean` §2).
>
> `isTermCodeE1 wT X = shapeUn X 0 ∨ (shapeBin X 1 ∧ argsIn wT (nthc X 2))` **no tiene esa
> propiedad**: `argsIn` es un `∀` acotado **anidado**. Ése es el contenido que falta, y no lo
> cubre el kit.

La mitad `hasWitF` (`DEUDA_hGuardF`) es estrictamente peor: `isFormCodeE2` tiene **ocho**
cláusulas y **dos** listas testigo, y `hasWitF` lleva un `∃∃`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.TrackedAtomsPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.HasWitTrackedPrf

/-! ## §1 · LA FORMA, COMPROBADA CONTRA EL ORIGINAL

Regla de método de §3.41.4: una abstracción de una forma medida se acompaña de un `rfl` por
instancia real. Si `Minimal/Axioms.lean` cambiara la forma de la guarda, estos dos dejan de
compilar. -/

/-- `isTC1` **es** una conjunción `∀‑acotado ∧ átomo`: la forma que `pcc_isFCB_tracked` refleja. -/
example (w c : Term) : isTC1 w c = land (wfAll1 w) (In c w) := rfl

/-- Y `hasWit` es ese `isTC1` bajo un `∃` sin cota, con el código lifteado. -/
example (c : Term) : hasWit c = Formula.ex (isTC1 (.var 0) (liftTerm 0 c)) := rfl

/-! ## §2 · LA OBLIGACIÓN DE CONTENIDO, ENUNCIADA

Idioma de `Meta/Sigma1BoundedPrf.lean`, `Meta/LineWFGuardPrf.lean` y
`Meta/D3ChainDotPrf.lean`: la deuda **se enuncia, no se postula**. Cero `axiom`.

Se deja **genérica en la imagen punteada** `WD` en vez de fijar un `wfAll1Dot` concreto: quien
la pruebe elegirá la imagen que le salga natural del `pcc_bdAll_intro`, y este módulo no debe
prejuzgarla. -/

/-- **La obligación**: reflejar el `∀` acotado `wfAll1` con el testigo `w` **abstracto**,
    entregando alguna imagen punteada `WD w`. -/
abbrev DEUDA_wfAll1_tracked (WD : Term → Term) : Prop :=
  ∀ w : Term, Prf (wfAll1 w ⇒ provFromCode (WD w))

/-! ## §3 · EL ESCALÓN: `isTC1` REFLEJADO, MÓDULO ESA OBLIGACIÓN -/

/-- ⭐ **La plantilla `isFCB` de A3, portada a `isTC1`.**

    La mitad derecha —el átomo `In c w` con **los dos argumentos abstractos**— la paga
    `pcc_In_atom_tracked`, que ya está en producción. La izquierda es la obligación. -/
theorem pcc_isTC1_tracked_of {WD : Term → Term} (hwf : DEUDA_wfAll1_tracked WD) (w c : Term) :
    Prf (isTC1 w c ⇒ provFromCode (andc (WD w) (inFormCodeFn (tcFn c) (tcFn w)))) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (isTC1 w c)
  exact PrfH_and_intro_code _ _
    (PrfH.mp _ _ _ (prf_to_prfH (hwf w) _) (PrfH_and_elim_left h))
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked c w) _) (PrfH_and_elim_right h))

end ROBINSON_PlusPlus.Meta.HasWitTrackedPrf

/-! ## `export` — por PROPÓSITO DECLARADO

El consumidor previsto es **C3**: quien pruebe `DEUDA_wfAll1_tracked` obtiene el reflector de
`isTC1` sin una línea más, y de ahí sale la mitad `hasWit` de `DEUDA_hGuardT` con el paso `∃`
(`pcc_exIntro_code_open`) y la fontanería `condD`. Nada lo consume todavía, y se dice en vez de
fingir una medición de consumo. -/
export ROBINSON_PlusPlus.Meta.HasWitTrackedPrf (
  DEUDA_wfAll1_tracked pcc_isTC1_tracked_of
)

#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_isTC1_tracked_of
