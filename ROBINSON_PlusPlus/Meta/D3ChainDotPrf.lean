import ROBINSON_PlusPlus.Meta.D3DottedPrf
import ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
import ROBINSON_PlusPlus.Meta.BdAllIntroPrf
import ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
-- ⚠️ Añadido con el puente de la cota (§4, 2026‑09‑09f): de aquí sale
--    `PrfH_bdAllCode_congr_bnd`, que es el ÚNICO sitio donde el salto
--    `(lenc p)˙ ↦ lencT ṗ` es legal — dentro de `Prov`. Sin ciclo.
import ROBINSON_PlusPlus.Meta.TrackedAtomsPrf
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
open ROBINSON_PlusPlus.Meta.TrackedAtomsPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf ROBINSON_PlusPlus.Meta.NatOrderPrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf

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


/-! ## §4 · EL PUENTE DE LA COTA (2026‑09‑09f)

§3 midió el hueco: `pcc_bdAll_intro` entrega la cota como **reflexión pura** `(lenc p)˙`, y el
destino la pide como **accesor dotado pre‑`liftc`‑ado** `lencT (liftc 0 ṗ)`.

⚠️ **Y ese salto NO se puede dar fuera de `Prov`.** `(lenc p)˙` es el código del término
`lenc p`; `lencT ṗ` es el constructor de código aplicado a `ṗ`. Que sean iguales es
exactamente la ecuación de RASTREO, y postularla a nivel objeto es lo que hizo la teoría
inconsistente (ADR‑012/013, `ax_tc_cons`). Lo que sí vale es la **evaluación provable**:
`pcc_eval_lenc` da `Prov(⌜lencT L̇ = (lenc L)˙⌝)`, y el cambio de cota se hace **dentro** de
`Prov` con `PrfH_bdAllCode_congr_bnd` (`Meta/TrackedAtomsPrf.lean`), que existe y es genérico.

⭐ Es el mismo gesto que `pcc_argsIn_trackedC` y `pcc_wfAll1_trackedC` hacen con sus listas
(`HasWitTrackedPrf` §8 y §10). Aquí sólo se instancia. -/

/-- El `liftc zero` de la cota del destino **se colapsa**: `ṗ` es un código dotado. -/
theorem chainOkB_bnd_liftc (p : Term) :
    Prf (lencT (liftc zero (tcFn p)) =eq lencT (tcFn p)) :=
  prf_congr_lencT (prf_liftc_tcFn p)

/-- ⭐⭐ **EL PUENTE DE LA COTA.** De la forma que `pcc_bdAll_intro` produce —cota en reflexión
    pura— a la que el destino impone —accesor dotado—, **dentro de `Prov`**.

    La única obligación que traslada es `hPinv`: que el cuerpo sea invariante bajo `substfc` de
    NIVEL 1. Es la misma que pide `hPinv_wfAll1Psi`, y se paga recorriendo el cuerpo: el nivel
    exterior 1 no toca nada porque los códigos dotados (`ṗ`, `tcFn …`) son `substtc`‑invariantes
    y los huecos vivos están en `⌜v₀⌝` (nivel 0) y, bajo el binder interno, en `⌜v₀⌝`/`⌜v₁⌝`. -/
theorem PrfH_chainOkB_bnd_bridge {Γ : List Formula} (p Phic : Term)
    (hPinv : ∀ u : Term, Prf (substfc (succ zero) u Phic =eq Phic))
    (hwP : Prf (hasWitF (bdAllBndCtx Phic)))
    (h : PrfH Γ (provFromCode (bdAllCode (tcFn (lenc p)) Phic))) :
    PrfH Γ (provFromCode (bdAllCode (lencT (liftc zero (tcFn p))) Phic)) := by
  -- (1) primero al accesor SIN `liftc`, que es donde `pcc_eval_lenc` aterriza
  have hstep : PrfH Γ (provFromCode (bdAllCode (lencT (tcFn p)) Phic)) := by
    refine PrfH_bdAllCode_congr_bnd (tcFn (lenc p)) (lencT (tcFn p)) Phic hPinv
      (prf_liftc_tcFn (lenc p)) ?_ ?_ h (by hw_auto) (by hw_auto) hwP
    · exact prf_eq_trans (prf_liftc_lencT zero (tcFn p)) (prf_congr_lencT (prf_liftc_tcFn p))
    · -- `Prov(⌜(lenc p)˙ = lencT ṗ⌝)` — es `pcc_eval_lenc` al revés
      refine prf_to_prfH ?_ _
      -- `pcc_eval_lenc` da `Prov(⌈lencT L̇ = (lenc L)˙⌉); la cota la pide al revés.
      exact pcc_mp_code_apply
        (pcc_eq_symm_code_internal (lencT (tcFn p)) (tcFn (lenc p))
          (substtc_inv_lencT (substtc_inv_tcFn p)) (by hw_auto) (by hw_auto))
        (pcc_eval_lenc p)
  -- (2) y de ahí a la forma pre‑`liftc`‑ada del destino, que es congruencia META
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
    (prf_congr_bdAllCode (prf_eq_symm (chainOkB_bnd_liftc p)) (prf_refl Phic))) _) hstep

/-- ⭐⭐⭐ **`DEUDA_chainOkBDot` REDUCIDA A `hbody`** (y a la invariancia del cuerpo).

    Con esto, D3 queda a **una sola** obligación con enunciado explícito: producir la reflexión
    del cuerpo `lineOkB nil p i`. Todo lo demás —el puente átomo↔acotada de §1, la apertura del
    destino de §3, y el puente de la cota de §4— está probado. -/
theorem DEUDA_chainOkBDot_of (Phic : Term)
    (hPinv : ∀ u : Term, Prf (substfc (succ zero) u Phic =eq Phic))
    (hwP : Prf (hasWitF (bdAllBndCtx Phic)))
    (hmatch : Prf (bdAllCode (lencT (liftc zero (tcFn (.var 0)))) Phic =eq chainOkBDot))
    (hbdAll : Prf (chainOk nil (.var 0) ⇒
      provFromCode (bdAllCode (tcFn (lenc (.var 0))) Phic))) :
    DEUDA_chainOkBDot := by
  refine prf_deduction ?_
  have h : PrfH [chainOk nil (.var 0)]
      (provFromCode (bdAllCode (tcFn (lenc (.var 0))) Phic)) :=
    PrfH.mp _ _ _ (prf_to_prfH hbdAll _) (prfH_hyp_self _)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr hmatch) _)
    (PrfH_chainOkB_bnd_bridge (.var 0) Phic hPinv hwP h)

/-- Y **D3 entera**, a partir de lo mismo. -/
theorem d3_prf_of (φ : Formula) (Phic : Term)
    (hPinv : ∀ u : Term, Prf (substfc (succ zero) u Phic =eq Phic))
    (hwP : Prf (hasWitF (bdAllBndCtx Phic)))
    (hmatch : Prf (bdAllCode (lencT (liftc zero (tcFn (.var 0)))) Phic =eq chainOkBDot))
    (hbdAll : Prf (chainOk nil (.var 0) ⇒
      provFromCode (bdAllCode (tcFn (lenc (.var 0))) Phic))) :
    Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_chainOkBDot φ (DEUDA_chainOkBDot_of Phic hPinv hwP hmatch hbdAll)


/-! ## §5 · EL `∃` ACOTADO CON COTA ARBITRARIA — la pieza de `boundedPremsIn` (2026‑09‑09f)

`boundedPremsIn c p i L = ∀j < lenc L. (In (nthc L j) c ∨ boundedCarcLt (nthc L j) p i)`, y el
disyunto de la derecha es un `∃` **acotado por `i`**, no por `lenc p`. `D3InDotPrf` ya refleja el
caso `boundedCarcIn` (cota `lenc p`); esto lo generaliza.

⭐⭐ **Y la generalización sale MÁS BARATA que el caso especial** — la lección de A5 otra vez, pero
al revés de lo intuitivo. Los dos pasos caros del molde desaparecen:

| paso | en `pcc_bddCarcDot_reflect` (cota `lenc p`) | aquí (cota `b` abstracta) |
|---|---|---|
| COTA | `pcc_eval_lenc` + simetría interna + Leibniz (≈15 l.) | `pcc_lt_tracked` **directo** |
| CUERPO | cruza la frontera D1 (`prf_tc_form_numeral` + `pcc_to_formCode_imp`, ≈30 l.) | congruencia objeto |

La razón: la cota deja de ser un accesor que hay que **evaluar**, y el lado derecho deja de ser
`⌜φ⌝` de una fórmula META para ser `ẏ` de un término **abstracto**. Medido antes de escribir.

⚠️ **Lo que sí aparece, y es real**: `pcc_eval_carc_nthc` pide `k < lenc p`, y el testigo del `∃`
sólo da `k < b`. Hace falta `b ≤ lenc p`, que entra como antecedente `lt b (lenc p)` — y es
exactamente lo que el `hbody` exterior tiene a mano (`i < lenc p`). -/

/-- El CUERPO dotado del `∃` acotado, con `y` y `p` abstractos (bajo el binder ⇒ `liftc 0`). -/
noncomputable def bdCarcLtPhic (y p : Term) : Term :=
  eqCodeFn (carcT (nthcT (liftc zero (tcFn p)) (varc (numeral 0)))) (liftc zero (tcFn y))

/-- El código dotado de `boundedCarcLt y p b`, con TODO abstracto. -/
noncomputable def bdCarcLtDot (y p b : Term) : Term :=
  bdExCode (liftc zero (tcFn b)) (bdCarcLtPhic y p)

theorem liftTerm_bdCarcLtPhic (c : Nat) (y p : Term) :
    liftTerm c (bdCarcLtPhic y p) = bdCarcLtPhic (liftTerm c y) (liftTerm c p) := by
  simp only [bdCarcLtPhic, eqCodeFn, carcT, nthcT, liftc, varc, numeral, funcc, cons, nil, zero,
    succ, tcFn, liftTerm, liftTerms, liftTerm_strCode, liftTerm_numeral]

theorem liftTerm_bdCarcLtDot (c : Nat) (y p b : Term) :
    liftTerm c (bdCarcLtDot y p b) = bdCarcLtDot (liftTerm c y) (liftTerm c p) (liftTerm c b) := by
  simp only [bdCarcLtDot, bdExCode, exc, andc, ltCodeFn, atom2CodeFn, liftc, varc, numeral,
    funcc, cons, nil, zero, succ, tcFn, liftTerm, liftTerms, liftTerm_strCode, liftTerm_numeral,
    liftTerm_bdCarcLtPhic]

theorem substtc_inv_bdCarcLtB (b : Term) :
    ∀ W, Prf (substtc zero W (liftc zero (tcFn b)) =eq liftc zero (tcFn b)) :=
  substtc_inv_liftc_tcFn b

/-- ⭐⭐ **LA REFLEXIÓN DEL `∃` ACOTADO, CON COTA ARBITRARIA.** -/
theorem pcc_bdCarcLt_reflect (y p b : Term) :
    Prf (chainOk nil p ⇒ (lt b (lenc p) ⇒
      (boundedCarcLt y p b ⇒ provFromCode (bdCarcLtDot y p b)))) := by
  refine prf_deduction (deduction_aux (deduction_aux ?_ (boundedCarcLt y p b)
    [lt b (lenc p), chainOk nil p] rfl) (lt b (lenc p)) [chainOk nil p] rfl)
  have hex : PrfH [boundedCarcLt y p b, lt b (lenc p), chainOk nil p]
      (boundedCarcLt y p b) := PrfH.hyp _ _ (List.Mem.head _)
  refine PrfH_ex_elim hex ?_
  rw [liftFormula_provFromCode_open, liftTerm_bdCarcLtDot]
  let exBody : Formula := land (lt (.var 0) (liftTerm 0 b))
    (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 y))
  let Γ' : List Formula :=
    [exBody, liftFormula 0 (boundedCarcLt y p b), liftFormula 0 (lt b (lenc p)),
     liftFormula 0 (chainOk nil p)]
  show PrfH Γ' (provFromCode (bdCarcLtDot (liftTerm 0 y) (liftTerm 0 p) (liftTerm 0 b)))
  have hC : PrfH Γ' exBody := PrfH.hyp _ _ (List.Mem.head _)
  have hlt : PrfH Γ' (lt (.var 0) (liftTerm 0 b)) := PrfH_and_elim_left hC
  have hbody : PrfH Γ'
      (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 y)) :=
    PrfH_and_elim_right hC
  have hble : PrfH Γ' (lt (liftTerm 0 b) (lenc (liftTerm 0 p))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hchain : PrfH Γ' (chainOk nil (liftTerm 0 p)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  -- el testigo cae bajo `lenc p` por transitividad: es lo que `pcc_eval_carc_nthc` pide
  have hk : PrfH Γ' (lt (.var 0) (lenc (liftTerm 0 p))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_trans _ _ _) _) hlt) hble
  -- COTA: directa, sin evaluación (aquí está el ahorro)
  have hlt1 : PrfH Γ' (provFromCode (ltCodeFn (tcFn (.var 0)) (tcFn (liftTerm 0 b)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked (.var 0) (liftTerm 0 b)) _) hlt
  have hltB : PrfH Γ' (provFromCode
      (ltCodeFn (tcFn (.var 0)) (liftc zero (tcFn (liftTerm 0 b))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_atom2CodeFn (prf_refl _)
      (prf_eq_symm (prf_liftc_tcFn (liftTerm 0 b))))) _) hlt1
  -- CUERPO: evaluación + congruencia OBJETO, sin cruzar la frontera D1
  have hev : PrfH Γ' (provFromCode (eqCodeFn
      (carcT (nthcT (tcFn (liftTerm 0 p)) (tcFn (.var 0))))
      (tcFn (carc (nthc (liftTerm 0 p) (.var 0)))))) :=
    PrfH.mp _ _ _
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_carc_nthc (liftTerm 0 p) (.var 0)) _) hchain) hk
  have hcodeq : PrfH Γ' (eqCodeFn (carcT (nthcT (tcFn (liftTerm 0 p)) (tcFn (.var 0))))
        (tcFn (carc (nthc (liftTerm 0 p) (.var 0))))
      =eq eqCodeFn (carcT (nthcT (liftc zero (tcFn (liftTerm 0 p))) (tcFn (.var 0))))
        (liftc zero (tcFn (liftTerm 0 y)))) :=
    PrfH_congr_eqCodeFn
      (prf_to_prfH (prf_congr_carcT (prf_congr_nthcT
        (prf_eq_symm (prf_liftc_tcFn (liftTerm 0 p))) (prf_refl _))) _)
      (PrfH_eq_trans (PrfH_congr_tcFn hbody)
        (prf_to_prfH (prf_eq_symm (prf_liftc_tcFn (liftTerm 0 y))) _))
  have hphi : PrfH Γ' (provFromCode (eqCodeFn
      (carcT (nthcT (liftc zero (tcFn (liftTerm 0 p))) (tcFn (.var 0))))
      (liftc zero (tcFn (liftTerm 0 y))))) :=
    PrfH_provCode_congr hcodeq hev
  -- el hueco `⌜v₀⌝` del cuerpo recibe el testigo `ı̇`
  have hcompPhi : Prf (substfc zero (tcFn (.var 0))
      (bdCarcLtPhic (liftTerm 0 y) (liftTerm 0 p))
      =eq eqCodeFn (carcT (nthcT (liftc zero (tcFn (liftTerm 0 p))) (tcFn (.var 0))))
        (liftc zero (tcFn (liftTerm 0 y)))) := by
    unfold bdCarcLtPhic
    refine prf_eq_trans (prf_substfc_eq zero (tcFn (.var 0)) _ _) ?_
    refine prf_congr_eqCodeFn ?_ (substtc_inv_liftc_tcFn (liftTerm 0 y) (tcFn (.var 0)))
    refine prf_eq_trans (prf_substtc_carcT zero (tcFn (.var 0)) _) ?_
    refine prf_congr_carcT ?_
    exact prf_eq_trans (prf_substtc_nthcT zero (tcFn (.var 0)) _ _)
      (prf_congr_nthcT (substtc_inv_liftc_tcFn (liftTerm 0 p) (tcFn (.var 0)))
        (prf_substtc_varc0 (tcFn (.var 0))))
  have hphi' : PrfH Γ' (provFromCode (substfc zero (tcFn (.var 0))
      (bdCarcLtPhic (liftTerm 0 y) (liftTerm 0 p)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm hcompPhi)) _) hphi
  exact PrfH_bdEx_intro_open _ _ (tcFn (.var 0))
    (substtc_inv_bdCarcLtB (liftTerm 0 b)) hltB hphi'
    (by hw_auto) (by hw_auto) (by hw_auto)


/-! ## §6 · EL CUERPO DEL `∀` DE `boundedPremsIn`: la disyunción, reflejada (2026‑09‑09f)

El cuerpo es `In (nthc L j) c ∨ boundedCarcLt (nthc L j) p i`, y en D3 **`c := nil`** (la cadena
es `chainOk nil p`: sin hipótesis).

⭐⭐ **Y eso hace la mitad izquierda VACUA.** `In y nil` es refutable (`prf_not_in_nil`), así que
esa rama sale por EFQ — y, lo que importa para el ensamblaje, **el código del disyunto izquierdo
puede quedar ARBITRARIO**: no hay que calcularlo ni casarlo con nada. Es el único sitio de todo
D3 donde el destino **no** impone la imagen, y conviene decirlo porque contradice la regla
general (§3.44: «`condD` no admite elegir imagen»). Aquí sí, y por una razón concreta: la rama
no se recorre.

⇒ El parámetro `Ac` de abajo es exactamente eso: el código del disyunto izquierdo, sin
restricción. Cuando el `pcc_bdAll_intro` de §7 fije el `PsiF`, se instanciará con lo que
`substCodeF` produzca, y esta prueba no cambia. -/

/-- ⭐⭐ **EL CUERPO DEL `∀`, REFLEJADO.** La disyunción se elimina a nivel OBJETO y cada rama se
    refleja por separado: la izquierda por explosión, la derecha por `pcc_bdCarcLt_reflect`. -/
theorem pcc_premsBody_reflect (Ac y p i : Term) :
    Prf (chainOk nil p ⇒ (lt i (lenc p) ⇒
      (lor (In y nil) (boundedCarcLt y p i) ⇒
        provFromCode (orc Ac (bdCarcLtDot y p i))))) := by
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (lor (In y nil) (boundedCarcLt y p i)) [lt i (lenc p), chainOk nil p] rfl)
    (lt i (lenc p)) [chainOk nil p] rfl)
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
  · -- ⭐ RAMA IZQUIERDA: `In y nil` es refutable ⇒ explosión. El código `Ac` no se toca.
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_not_in_nil y) _) (PrfH.hyp _ _ (List.Mem.head _)))
  · -- RAMA DERECHA: el `∃` acotado de §5, con el contexto ya en su sitio
    refine PrfH_orR_code Ac _ ?_
    have hchain : PrfH [boundedCarcLt y p i, lor (In y nil) (boundedCarcLt y p i),
        lt i (lenc p), chainOk nil p] (chainOk nil p) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have hlt : PrfH [boundedCarcLt y p i, lor (In y nil) (boundedCarcLt y p i),
        lt i (lenc p), chainOk nil p] (lt i (lenc p)) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (pcc_bdCarcLt_reflect y p i) _) hchain) hlt)
      (PrfH.hyp _ _ (List.Mem.head _))

/-- La forma que el `hbody` del `pcc_bdAll_intro` de `boundedPremsIn` consumirá: el cuerpo ya
    instanciado en el índice `j` de la lista `L`. -/
theorem pcc_premsBody_reflect_at (Ac L j p i : Term) :
    Prf (chainOk nil p ⇒ (lt i (lenc p) ⇒
      (lor (In (nthc L j) nil) (boundedCarcLt (nthc L j) p i) ⇒
        provFromCode (orc Ac (bdCarcLtDot (nthc L j) p i))))) :=
  pcc_premsBody_reflect Ac (nthc L j) p i


/-! ## §7 · EL `pcc_bdAll_intro` DE `boundedPremsIn`: el EMPAQUETADO y sus obligaciones

⚠️ **La fricción administrativa conocida**, y aquí es peor que en `argsIn`: `pcc_bdAll_intro`
pide que la condición `CF` sea natural en **UN** parámetro, y `boundedPremsIn c p i L` tiene
**cuatro** términos libres. Con `c := nil` (D3 no tiene hipótesis) quedan **tres**, que se
empaquetan en uno con `cons` y se leen con `carc`/`cdrc` — naturales por construcción. Es
exactamente lo que `HasWitTrackedPrf` §4 hace con `argsInPair`, un nivel más de anidamiento.

    q = ⟨p, i, L⟩ = cons p (cons i L)
      p = carc q      i = carc (cdrc q)      L = cdrc (cdrc q) -/

/-- Los tres accesores del paquete. Se nombran para que las pruebas se lean. -/
abbrev pkP (q : Term) : Term := carc q
abbrev pkI (q : Term) : Term := carc (cdrc q)
abbrev pkL (q : Term) : Term := cdrc (cdrc q)

/-- `boundedPremsIn nil p i L` con sus tres argumentos EMPAQUETADOS en uno. -/
def premsPair (q : Term) : Formula := boundedPremsIn nil (pkP q) (pkI q) (pkL q)

/-- La cota del `∀`: la longitud de la lista de premisas. -/
abbrev premsBnd (q : Term) : Term := lenc (pkL q)

/-! ### Las obligaciones ADMINISTRATIVAS que no dependen de `PsiF` (4 de 8) -/

theorem hCl_premsPair (k : Nat) (q : Term) :
    liftFormula k (premsPair q) = premsPair (liftTerm k q) := by
  simp only [premsPair, pkP, pkI, pkL, liftFormula_boundedPremsIn, carc, cdrc, nil, zero,
    liftTerm, liftTerms]

theorem hCs_premsPair (v : Nat) (s q : Term) :
    substFormula v s (premsPair q) = premsPair (substTerm v s q) := by
  simp only [premsPair, pkP, pkI, pkL, substFormula_boundedPremsIn, carc, cdrc, nil, zero,
    substTerm, substTerms]

theorem hbl_premsBnd (k : Nat) (q : Term) :
    liftTerm k (premsBnd q) = premsBnd (liftTerm k q) := by
  simp only [premsBnd, pkL, lenc, carc, cdrc, liftTerm, liftTerms]

theorem hbs_premsBnd (v : Nat) (s q : Term) :
    substTerm v s (premsBnd q) = premsBnd (substTerm v s q) := by
  simp only [premsBnd, pkL, lenc, carc, cdrc, substTerm, substTerms]

/-! ### ⚠️ LA INSTANCIACIÓN DEL PAQUETE **NO ES `rfl`** — y conviene tenerlo escrito

El instinto dice que `premsPair (cons p (cons i L)) = boundedPremsIn nil p i L` por `rfl`.
**Es falso**, y por la misma razón que `chainOkBDot` no reduce (§3): `carc` y `cdrc` son
**símbolos de función OBJETO** (`Term.func "carc" […]`), no funciones de Lean. `carc (cons p X)`
se queda tal cual; que valga `p` es un **teorema de la teoría** (`prf_carc_cons`), no un cómputo.

⇒ El empaquetado de `pcc_bdAll_intro` **no es gratis** aquí, al revés de lo que sugiere leer
`argsInPair`: hay que arrastrar los puentes objeto al instanciar. Es exactamente para lo que el
kit trae `pcc_carcD_bridge_cons` / `pcc_cdrcD_bridge_cons`, que `HasWitTrackedPrf` §4 cita.

Se deja medido aquí en vez de descubrirlo dentro de la prueba del `hbody`. -/

end ROBINSON_PlusPlus.Meta.D3ChainDotPrf

/-! ## `export` — por PROPÓSITO DECLARADO

El consumidor previsto es la rama **D**: quien pruebe `DEUDA_chainOkBDot` obtiene D3 aplicando
`d3_prf_of_chainOkBDot`, sin una línea más. Nada consume todavía este módulo, y se dice en vez
de fingir una medición de consumo (mismo criterio que `Meta/EvalSubstfcPrf.lean`). -/
export ROBINSON_PlusPlus.Meta.D3ChainDotPrf (
  chainOkBDot prf_forall_chainOkB_imp_chainOk pcc_chainOkBDot_imp_chainOkDot
  hC_dot_of_chainOkBDot DEUDA_chainOkBDot d3_prf_of_chainOkBDot
  chainOkBDot_eq_substCodeF chainOkBDot_computed
  chainOkB_bnd_liftc PrfH_chainOkB_bnd_bridge DEUDA_chainOkBDot_of d3_prf_of
  bdCarcLtPhic bdCarcLtDot liftTerm_bdCarcLtPhic liftTerm_bdCarcLtDot
  substtc_inv_bdCarcLtB pcc_bdCarcLt_reflect
  pcc_premsBody_reflect pcc_premsBody_reflect_at
  pkP pkI pkL premsPair premsBnd
  hCl_premsPair hCs_premsPair hbl_premsBnd hbs_premsBnd
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.pcc_chainOkBDot_imp_chainOkDot
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hC_dot_of_chainOkBDot
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_chainOkBDot
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.PrfH_chainOkB_bnd_bridge
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.DEUDA_chainOkBDot_of
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.pcc_bdCarcLt_reflect
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.pcc_premsBody_reflect
