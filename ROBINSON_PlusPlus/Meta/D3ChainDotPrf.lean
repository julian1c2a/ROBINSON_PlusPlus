import ROBINSON_PlusPlus.Meta.D3DottedPrf
import ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
import ROBINSON_PlusPlus.Meta.BdAllIntroPrf
import ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
/-!
# `Meta/D3ChainDotPrf.lean` — el CHASIS de `hC_dot`, y el puente ÁTOMO ↔ FORMA ACOTADA

**D3 está reducida a un solo lema** desde §3.19: `d3_prf_of_chainOkDot (φ) (hC)`
(`Meta/D3InDotPrf.lean:524`) sólo pide

    hC_dot : Prf (chainOk nil #0 ⇒ provFromCode chainOkDot)

y `hI_dot`, el otro átomo punteado, ya está cerrado. Este módulo ataca `hC_dot`.

## El hueco que A3 no tenía

La reflexión de un `∀` acotado con argumento **abstracto** ya está resuelta y ejercitada: es
`pcc_bdAll_intro` (`Meta/BdAllIntroPrf.lean:313`), la keystone de §3.20.7, y
`sondeos/A3IsFCBTracked.lean:819` la aplica entera (`pcc_wfAll_tracked`) descargando sus ocho
obligaciones administrativas.

⚠️ **Pero aquel caso no tenía el hueco que tiene éste.** Allí `wfAll` **es** un `∀` acotado, así
que lo que `pcc_bdAll_intro` entrega —el código de un `∀` acotado— *es* lo que se pedía. Aquí
no: `chainOk` es un **ÁTOMO** (`Minimal/Axioms.lean:790`, `Formula.atom "chainOk" [c,p]`), y su
forma acotada `chainOkB` es otra fórmula. `pcc_bdAll_intro` daría `Prov(⌜chainOkB nil ṗ⌝)`, y
`hC_dot` pide `Prov(⌜chainOk nil ṗ⌝)`.

**Hay que cruzar ese hueco DENTRO de `Prov`**, y ahí no vale `prf_chainOk_iff_chainOkB`
directamente: ése es un teorema del meta‑nivel sobre el `⇔` objeto, y lo que hace falta es que
la **teoría objeto** sepa la implicación sobre el código **punteado y abierto**. Eso es §1.

## Lo que trae

* **§1 `hC_dot_of_chainOkBDot`** — el puente, **probado**: dado el reflector de la forma
  acotada, sale el del átomo. Es independiente de C3 y de la rama C entera.
* **§2** la obligación que queda, enunciada (idioma de `Meta/Sigma1BoundedPrf.lean` y de
  `Meta/LineWFGuardPrf.lean`: la deuda **se enuncia, no se postula**), y el cierre condicional
  de **D3** a partir de ella.

## ⚠️ Lo que este módulo NO hace, y de qué depende lo que falta

No prueba `DEUDA_chainOkBDot`. Aplicarle `pcc_bdAll_intro` pide, como `hbody`, la reflexión de
`lineOkB nil q i` para cada índice — y `lineOkB` es
`lineWF (nthc p i) ∧ boundedPremsIn c p i (premsOf (nthc p i))`, o sea **dos** obligaciones:

1. la reflexión del átomo `lineWF`, que es exactamente **`pcc_lineWF_tracked`** — y ése no
   existe sin condicionar: sólo `pcc_lineWF_tracked_modulo_7`
   (`Meta/LineWFAssemblePrf.lean:104`), que pide los **7 reflectores de la rama C3**;
2. la reflexión de `boundedPremsIn`, que es un **segundo `∀` acotado anidado** — trabajo nuevo,
   pero de la misma forma que §1‑§2, luego otra aplicación de `pcc_bdAll_intro`.

⇒ **D3 está aguas abajo de C3 por la vía (1)**, y eso conviene tenerlo escrito: «ir a por D3»
sin cerrar antes los 7 reflectores sólo puede producir chasis, no el teorema.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.D3DottedPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf ROBINSON_PlusPlus.Meta.EvalListPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.D3ChainDotPrf

/-! ## §1 · EL PUENTE ÁTOMO ↔ FORMA ACOTADA, DENTRO DE `Prov` -/

/-- El código punteado de la **forma acotada**, en el mismo molde que `chainOkDot`
    (`Meta/D3DottedPrf.lean:87`), que es el del átomo. -/
abbrev chainOkBDot : Term :=
  substfc zero (tcFn (.var 0)) (formCode (chainOkB nil (.var 0)))

/-- La implicación `chainOkB → chainOk` **como teorema universalmente cuantificado**: es la
    dirección `⇐` de `prf_chainOk_iff_chainOkB`, generalizada. Es lo único que hay que meter
    dentro de `Prov` para cruzar el hueco. -/
theorem prf_forall_chainOkB_imp_chainOk :
    Prf (Formula.forall (Formula.impl (chainOkB nil (.var 0)) (chainOk nil (.var 0)))) :=
  Prf.gen _ (prf_and_elim_right (prf_chainOk_iff_chainOkB nil (.var 0)))

/-- **El puente, instanciado DENTRO de `Prov` en el testigo punteado `ṗ`.**

    `pcc_thm_inst` mete el teorema anterior en `Prov` y lo instancia en `tcFn #0`; `substfc`
    distribuye sobre `implc` (`prf_substfc_impl`), así que lo que sale es literalmente
    `Prov(⌜chainOkBDot ⇒ chainOkDot⌝)`. -/
theorem pcc_chainOkBDot_imp_chainOkDot :
    Prf (provFromCode (implc chainOkBDot chainOkDot)) := by
  have hinst :=
    pcc_thm_inst (Formula.impl (chainOkB nil (.var 0)) (chainOk nil (.var 0)))
      prf_forall_chainOkB_imp_chainOk (tcFn (.var 0)) (by hw_auto)
  have hdist : Prf (substfc zero (tcFn (.var 0))
      (formCode (Formula.impl (chainOkB nil (.var 0)) (chainOk nil (.var 0))))
        =eq implc chainOkBDot chainOkDot) :=
    prf_substfc_impl zero (tcFn (.var 0))
      (formCode (chainOkB nil (.var 0))) (formCode (chainOk nil (.var 0)))
  exact prf_mp (prf_provCode_congr hdist) hinst

/-- ⭐ **EL PUENTE.** Dado el reflector punteado de la forma **acotada**, sale el del **átomo**.

    Es la pieza que `sondeos/A3IsFCBTracked.lean` no necesitó —allí el predicado ya *era* un
    `∀` acotado—, y sin ella `pcc_bdAll_intro` no puede cerrar `hC_dot`: entrega el código
    equivocado. Independiente de la rama C. -/
theorem hC_dot_of_chainOkBDot
    (hB : Prf (chainOk nil (.var 0) ⇒ provFromCode chainOkBDot)) :
    Prf (chainOk nil (.var 0) ⇒ provFromCode chainOkDot) := by
  refine prf_deduction ?_
  have hb : PrfH [chainOk nil (.var 0)] (provFromCode chainOkBDot) :=
    PrfH.mp _ _ _ (prf_to_prfH hB _) (prfH_hyp_self _)
  exact PrfH.mp _ _ _
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_mp_code_open chainOkBDot chainOkDot) _)
      (prf_to_prfH pcc_chainOkBDot_imp_chainOkDot _)) hb

/-! ## §2 · LA OBLIGACIÓN QUE QUEDA, Y EL CIERRE CONDICIONAL DE D3

Idioma de `Meta/Sigma1BoundedPrf.lean` y `Meta/LineWFGuardPrf.lean`: la deuda **se enuncia, no
se postula**. No hay ningún `axiom` aquí. -/

/-- **La obligación** — el reflector punteado de la forma ACOTADA de `chainOk`. Es a lo que
    `pcc_bdAll_intro` se aplicaría, con `CF := chainOk nil`, `bndF := lenc` y `PsiF` el código
    de `lineOkB nil p #0`. -/
abbrev DEUDA_chainOkBDot : Prop :=
  Prf (chainOk nil (.var 0) ⇒ provFromCode chainOkBDot)

/-- ⭐ **D3 CERRADA A PARTIR DE UNA SOLA OBLIGACIÓN.**

    `d3_prf_of_chainOkDot` reducía D3 a `hC_dot`; §1 reduce `hC_dot` a la forma **acotada**.
    Componiendo: D3 sale de `DEUDA_chainOkBDot` y nada más. -/
theorem d3_prf_of_chainOkBDot (φ : Formula) (hB : DEUDA_chainOkBDot) :
    Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_chainOkDot φ (hC_dot_of_chainOkBDot hB)


/-! ## §3 · LA MEDICIÓN DEL DESTINO (2026‑09‑09f)

Regla de método de §3.44 y del 2º corolario de *medir la forma*: **antes de escribir la prueba,
desplegar el destino y casarlo con `rfl`**. `condD` costó un frente por saltársela. Aquí se
aplica primero, y el resultado reordena el trabajo.

### ⚠️ Lo primero que hay que saber: `chainOkBDot` **NO reduce**

`chainOkBDot = substfc zero ṗ (formCode (chainOkB nil #0))`, y `substfc` es un **símbolo de
función OBJETO**, no una función de Lean. Así que el destino es **sintácticamente opaco**: no
hay `rfl` que lo vea como un `bdAllCode`. Medido: `∃ B Psi, chainOkBDot = bdAllCode B Psi`
**no compila**.

Quien lo abre es `prf_substfc_arith_open`, que lo iguala —**dentro de la teoría objeto**— a
`substCodeF`, que sí es una función de Lean y sí computa. Ése es el puente, y es el mismo
mecanismo con el que se dotaron los `ax_liftfc_*` (§3.52). -/

/-- **[1] EL DESTINO, ABIERTO.** `substCodeF` computa; `chainOkBDot` no. Esto los iguala. -/
theorem chainOkBDot_eq_substCodeF :
    Prf (chainOkBDot =eq substCodeF 0 (tcFn (.var 0)) (chainOkB nil (.var 0))) :=
  prf_substfc_arith_open 0 (tcFn (.var 0)) (chainOkB nil (.var 0))

/-- **[2] Y LA FORMA COMPUTADA ES UN `bdAllCode`** — con la cota EXPLÍCITA, casada por `rfl`.

    ⭐⭐ **Aquí está el hueco real de `DEUDA_chainOkBDot`, y no es el que se esperaba.** La cota
    del destino es

        lencT (liftc zero ṗ)

    es decir, el **ACCESOR DOTADO** `lencT`, y además **pre‑`liftc`‑ado** porque vive dentro del
    binder del `∀`. Y lo que `pcc_bdAll_intro` entrega es

        tcFn (lenc p)

    o sea la **REFLEXIÓN PURA**, y sin `liftc`. Son códigos distintos.

    ⇒ **`DEUDA_chainOkBDot` no es «aplicar `pcc_bdAll_intro` y ya»**: son DOS puentes más,
    los dos ya conocidos en el árbol:
    * `tcFn (lenc p)` ↦ `lencT ṗ` — es exactamente `pcc_eval_lenc` (`Meta/EvalListPrf.lean`),
      que **ya está probado**; es la «desviación 2» que `HasWitTrackedPrf` §9 y
      `sondeos/ReflectorAtomoAllIn.lean` documentan.
    * el `liftc zero` de la cota, que sale del binder. -/
theorem chainOkBDot_computed :
    ∃ Psi, substCodeF 0 (tcFn (.var 0)) (chainOkB nil (.var 0))
      = bdAllCode (lencT (liftc zero (tcFn (.var 0)))) Psi := ⟨_, rfl⟩

/-! ### §3.1 · Lo que queda, con los tamaños medidos

| pieza | estado |
|---|---|
| `d3_prf_of_chainOkBDot` (§2) y todo lo de aguas abajo | ✅ **probado** |
| el destino, abierto y con su forma fijada por `rfl` | ✅ **[1] y [2], aquí** |
| puente de la COTA (`tcFn (lenc p)` ↦ `lencT ṗ`, y el `liftc`) | ⬜ `pcc_eval_lenc` ya existe |
| `hbody` (a) · reflexión de `lineWF` = `pcc_lineWF_tracked` | ⬜ **5 de 7** reflectores |
| `hbody` (b) · reflexión de `boundedPremsIn` | ⬜ 2º `∀` acotado ⇒ 2º `pcc_bdAll_intro` |

⚠️ **Y el orden importa**: (a) está aguas abajo de C3, así que «ir a por D3» sin cerrar los 7
reflectores sigue sin poder producir el teorema — lo que sí se puede hacer, y es lo que hace
esta sección, es **fijar el destino** para que cuando (a) llegue no haya que redescubrirlo. -/

end ROBINSON_PlusPlus.Meta.D3ChainDotPrf

/-! ## `export` — por PROPÓSITO DECLARADO

El consumidor previsto es la rama **D**: quien pruebe `DEUDA_chainOkBDot` obtiene D3 aplicando
`d3_prf_of_chainOkBDot`, sin una línea más. Nada consume todavía este módulo, y se dice en vez
de fingir una medición de consumo (mismo criterio que `Meta/EvalSubstfcPrf.lean`). -/
export ROBINSON_PlusPlus.Meta.D3ChainDotPrf (
  chainOkBDot prf_forall_chainOkB_imp_chainOk pcc_chainOkBDot_imp_chainOkDot
  hC_dot_of_chainOkBDot DEUDA_chainOkBDot d3_prf_of_chainOkBDot
  chainOkBDot_eq_substCodeF chainOkBDot_computed
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.pcc_chainOkBDot_imp_chainOkDot
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hC_dot_of_chainOkBDot
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_chainOkBDot
