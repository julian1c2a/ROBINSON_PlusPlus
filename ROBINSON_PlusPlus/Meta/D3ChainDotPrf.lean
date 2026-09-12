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
theorem pcc_chainOkBDot_imp_chainOkDot [AnclaEq] :
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
theorem hC_dot_of_chainOkBDot [AnclaEq]
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
theorem d3_prf_of_chainOkBDot [AnclaEq] (φ : Formula) (hB : DEUDA_chainOkBDot) :
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
theorem PrfH_chainOkB_bnd_bridge [AnclaEq] {Γ : List Formula} (p Phic : Term)
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
theorem DEUDA_chainOkBDot_of [AnclaEq] (Phic : Term)
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
theorem d3_prf_of [AnclaEq] (φ : Formula) (Phic : Term)
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

/-! ### §5bis · LA MISMA, GENERALIZADA EN SU `Phic` (2026‑09‑10h)

⭐ **`pcc_bdCarcLt_reflect` no era el lema general: era una instancia.** Lo que la prueba de arriba
hace no depende de que el cuerpo del `∃` sea `bdCarcLtPhic`; sólo necesita que el cuerpo, **ya
instanciado en el testigo**, se pueda producir. Generalizarlo cuesta **dos parámetros** (`Phic` y su
liftado) y **una hipótesis extra `A`** que atraviese el `∃`‑elim.

⚠️ **La hipótesis extra no es capricho.** El consumidor real —el chasis interior de
`boundedPremsIn`, `Meta/PremsBdAllPrf.lean`— necesita la cota `j < lenc L` dentro de `hphi`, y por
las tres hipótesis de §5 **no viaja**. Es la clase de cosa que sólo se ve al instanciar.

⛔ **Y por qué hay que generalizar en el `Phic` y no reescribir después**: el hueco a cambiar vive
**bajo el binder del `exc`**, y `pcc_rw` —que reescribe con `substfc zero`— **no llega ahí**. El
único sitio donde el salto se puede dar es la obligación `hphi`, con el binder **ya abierto**.
⭐ `PrfH_bdEx_intro_open` era genérico en `Phic` **desde siempre**; lo único especializado era la
envoltura. -/

/-- Contracción: dos hipótesis iguales seguidas se funden en una. -/
theorem prf_contract {A B : Formula} (h : Prf (A ⇒ (A ⇒ B))) : Prf (A ⇒ B) :=
  prf_deduction (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH h _) (prfH_hyp_self _))
    (prfH_hyp_self _))

theorem pcc_bdEx_carc_reflect_gen [AnclaEq] (y p b Phic Phic' : Term) (A A' : Formula)
    (hPlift : liftTerm 0 Phic = Phic')
    (hAlift : liftFormula 0 A = A')
    (hwPhi : Prf (hasWitF (liftTerm 0 Phic')))
    (hphi : Prf (A' ⇒ (chainOk nil (liftTerm 0 p) ⇒ (lt (liftTerm 0 b) (lenc (liftTerm 0 p)) ⇒
        (land (lt (.var 0) (liftTerm 0 b))
              (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 y))
         ⇒ provFromCode (substfc zero (tcFn (.var 0)) Phic')))))) :
    Prf (A ⇒ (chainOk nil p ⇒ (lt b (lenc p) ⇒ (boundedCarcLt y p b ⇒
      provFromCode (bdExCode (liftc zero (tcFn b)) Phic))))) := by
  refine prf_deduction (deduction_aux (deduction_aux (deduction_aux ?_
    (boundedCarcLt y p b) [lt b (lenc p), chainOk nil p, A] rfl)
    (lt b (lenc p)) [chainOk nil p, A] rfl)
    (chainOk nil p) [A] rfl)
  have hex : PrfH [boundedCarcLt y p b, lt b (lenc p), chainOk nil p, A]
      (boundedCarcLt y p b) := PrfH.hyp _ _ (List.Mem.head _)
  refine PrfH_ex_elim hex ?_
  rw [liftFormula_provFromCode_open]
  have hLb : liftTerm 0 (bdExCode (liftc zero (tcFn b)) Phic)
      = bdExCode (liftc zero (tcFn (liftTerm 0 b))) Phic' := by
    simp only [bdExCode, exc, andc, ltCodeFn, atom2CodeFn, liftc, varc, numeral, funcc,
      cons, nil, zero, succ, tcFn, liftTerm, liftTerms, liftTerm_strCode, liftTerm_numeral,
      hPlift]
  rw [hLb]
  let exBody : Formula := land (lt (.var 0) (liftTerm 0 b))
    (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 y))
  let Gm : List Formula :=
    [exBody, liftFormula 0 (boundedCarcLt y p b), liftFormula 0 (lt b (lenc p)),
     liftFormula 0 (chainOk nil p), liftFormula 0 A]
  show PrfH Gm (provFromCode (bdExCode (liftc zero (tcFn (liftTerm 0 b))) Phic'))
  have hC : PrfH Gm exBody := PrfH.hyp _ _ (List.Mem.head _)
  have hlt : PrfH Gm (lt (.var 0) (liftTerm 0 b)) := PrfH_and_elim_left hC
  have hble : PrfH Gm (lt (liftTerm 0 b) (lenc (liftTerm 0 p))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hchain : PrfH Gm (chainOk nil (liftTerm 0 p)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hA : PrfH Gm A' := hAlift ▸ PrfH.hyp _ _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  -- COTA: directa, sin evaluación
  have hlt1 : PrfH Gm (provFromCode (ltCodeFn (tcFn (.var 0)) (tcFn (liftTerm 0 b)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked (.var 0) (liftTerm 0 b)) _) hlt
  have hltB : PrfH Gm (provFromCode
      (ltCodeFn (tcFn (.var 0)) (liftc zero (tcFn (liftTerm 0 b))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_atom2CodeFn (prf_refl _)
      (prf_eq_symm (prf_liftc_tcFn (liftTerm 0 b))))) _) hlt1
  -- CUERPO: la obligación genérica, ya con el binder ABIERTO
  have hphi' : PrfH Gm (provFromCode (substfc zero (tcFn (.var 0)) Phic')) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH hphi _) hA) hchain) hble) hC
  exact PrfH_bdEx_intro_open _ _ (tcFn (.var 0))
    (substtc_inv_bdCarcLtB (liftTerm 0 b)) hltB hphi'
    (by hw_auto) hwPhi (by hw_auto)



/-! ### §5ter · Y `pcc_bdCarcLt_reflect` COMO INSTANCIA (ADR‑019)

El `A` extra se instancia con `chainOk nil p` —redundante— y se contrae. La obligación `hphi` es
literalmente lo que la prueba de §5 hacía en su contexto interno, sacado a un `Prf`. -/

/-- La obligación `hphi` del caso `bdCarcLtPhic`. -/
theorem hphi_bdCarcLt [AnclaEq] (y p b : Term) :
    Prf (chainOk nil (liftTerm 0 p) ⇒
      (chainOk nil (liftTerm 0 p) ⇒ (lt (liftTerm 0 b) (lenc (liftTerm 0 p)) ⇒
        (land (lt (.var 0) (liftTerm 0 b))
              (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 y))
         ⇒ provFromCode (substfc zero (tcFn (.var 0))
             (bdCarcLtPhic (liftTerm 0 y) (liftTerm 0 p))))))) := by
  refine prf_deduction (deduction_aux (deduction_aux (deduction_aux ?_
    (land (lt (.var 0) (liftTerm 0 b))
          (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 y)))
    [lt (liftTerm 0 b) (lenc (liftTerm 0 p)), chainOk nil (liftTerm 0 p),
     chainOk nil (liftTerm 0 p)] rfl)
    (lt (liftTerm 0 b) (lenc (liftTerm 0 p)))
    [chainOk nil (liftTerm 0 p), chainOk nil (liftTerm 0 p)] rfl)
    (chainOk nil (liftTerm 0 p)) [chainOk nil (liftTerm 0 p)] rfl)
  let Gm : List Formula :=
    [land (lt (.var 0) (liftTerm 0 b))
          (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 y)),
     lt (liftTerm 0 b) (lenc (liftTerm 0 p)), chainOk nil (liftTerm 0 p),
     chainOk nil (liftTerm 0 p)]
  have hC : PrfH Gm (land (lt (.var 0) (liftTerm 0 b))
      (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 y))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hlt : PrfH Gm (lt (.var 0) (liftTerm 0 b)) := PrfH_and_elim_left hC
  have hbody : PrfH Gm
      (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 y)) :=
    PrfH_and_elim_right hC
  have hble : PrfH Gm (lt (liftTerm 0 b) (lenc (liftTerm 0 p))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hchain : PrfH Gm (chainOk nil (liftTerm 0 p)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hk : PrfH Gm (lt (.var 0) (lenc (liftTerm 0 p))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_trans _ _ _) _) hlt) hble
  have hev : PrfH Gm (provFromCode (eqCodeFn
      (carcT (nthcT (tcFn (liftTerm 0 p)) (tcFn (.var 0))))
      (tcFn (carc (nthc (liftTerm 0 p) (.var 0)))))) :=
    PrfH.mp _ _ _
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_carc_nthc (liftTerm 0 p) (.var 0)) _) hchain) hk
  have hcodeq : PrfH Gm (eqCodeFn (carcT (nthcT (tcFn (liftTerm 0 p)) (tcFn (.var 0))))
        (tcFn (carc (nthc (liftTerm 0 p) (.var 0))))
      =eq eqCodeFn (carcT (nthcT (liftc zero (tcFn (liftTerm 0 p))) (tcFn (.var 0))))
        (liftc zero (tcFn (liftTerm 0 y)))) :=
    PrfH_congr_eqCodeFn
      (prf_to_prfH (prf_congr_carcT (prf_congr_nthcT
        (prf_eq_symm (prf_liftc_tcFn (liftTerm 0 p))) (prf_refl _))) _)
      (PrfH_eq_trans (PrfH_congr_tcFn hbody)
        (prf_to_prfH (prf_eq_symm (prf_liftc_tcFn (liftTerm 0 y))) _))
  have hphi : PrfH Gm (provFromCode (eqCodeFn
      (carcT (nthcT (liftc zero (tcFn (liftTerm 0 p))) (tcFn (.var 0))))
      (liftc zero (tcFn (liftTerm 0 y))))) :=
    PrfH_provCode_congr hcodeq hev
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
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm hcompPhi)) _) hphi

/-- ⭐⭐ **LA REFLEXIÓN DEL `∃` ACOTADO, CON COTA ARBITRARIA** — hoy, **la instancia** de §5bis
    (ADR‑019, 2026‑09‑10h). El enunciado es el de siempre; la prueba dejó de estar duplicada. -/
theorem pcc_bdCarcLt_reflect [AnclaEq] (y p b : Term) :
    Prf (chainOk nil p ⇒ (lt b (lenc p) ⇒
      (boundedCarcLt y p b ⇒ provFromCode (bdCarcLtDot y p b)))) :=
  prf_contract
    (pcc_bdEx_carc_reflect_gen y p b (bdCarcLtPhic y p)
      (bdCarcLtPhic (liftTerm 0 y) (liftTerm 0 p))
      (chainOk nil p) (chainOk nil (liftTerm 0 p))
      (liftTerm_bdCarcLtPhic 0 y p) rfl (by hw_auto) (hphi_bdCarcLt y p b))

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
theorem pcc_premsBody_reflect [AnclaEq] (Ac y p i : Term) :
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
theorem pcc_premsBody_reflect_at [AnclaEq] (Ac L j p i : Term) :
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


/-! ### §7.1 · LA DESCOMPOSICIÓN DEL DESTINO, FIJADA POR `rfl`

Regla de §3: el destino se despliega y se casa con `rfl` **antes** de escribir la prueba. Aquí
no se adivina la forma: se **lee de la definición de `substCodeF`** (`SubstCodeOpenPrf:68`), y
las dos igualdades de abajo la certifican. Si `boundedPremsIn` o `substCodeF` cambiaran, dejan
de compilar. -/

/-- El cuerpo del `∀` de `boundedPremsIn`, como FÓRMULA (ya bajo el binder). -/
noncomputable def premsBody (p i L : Term) : Formula :=
  lor (In (nthc (liftTerm 0 L) (.var 0)) nil)
      (boundedCarcLt (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 p) (liftTerm 0 i))

/-- ⭐ **EL DESTINO, DESCOMPUESTO**: el código de `boundedPremsIn` ES un `bdAllCode`, con la cota
    y el cuerpo identificados. Correcto por construcción, no por conjetura. -/
theorem substCodeF_boundedPremsIn (W p i L : Term) :
    substCodeF 0 W (boundedPremsIn nil p i L)
      = bdAllCode (substCodeT 1 (liftc zero W) (liftTerm 0 (lenc L)))
          (substCodeF 1 (liftc zero W) (premsBody p i L)) := rfl

/-- Y el cuerpo se parte en el `orc` de sus dos disyuntos — que es lo que §6 refleja. -/
theorem substCodeF_premsBody (W p i L : Term) :
    substCodeF 1 (liftc zero W) (premsBody p i L)
      = orc (substCodeF 1 (liftc zero W) (In (nthc (liftTerm 0 L) (.var 0)) nil))
            (substCodeF 1 (liftc zero W)
              (boundedCarcLt (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 p) (liftTerm 0 i))) := rfl

/-! ### §7.2 · ⚠️ EL HALLAZGO QUE REORDENA EL RESTO DE `hbody`(b)

Intenté fijar el `PsiF` del `pcc_bdAll_intro` interior por separado, y **no se puede**. La razón
es estructural, no de esfuerzo:

* `pcc_bdAll_intro` entrega `bdAllCode (tcFn (bndF q)) (PsiF q)` con `PsiF` **a elección**;
* pero el código de `boundedPremsIn` que D3 necesita no es cualquiera: es el **sub‑término** del
  `PsiF` del `pcc_bdAll_intro` EXTERIOR (el de `chainOkB`, §3), porque `boundedPremsIn` vive
  dentro de `lineOkB`, que es el cuerpo de aquél;
* y ese sub‑término lleva las capas de `liftc`/`substCodeT` que le impone **su posición bajo los
  binders del exterior**, no las que salen de instanciar el interior por su cuenta.

Medido: `substCodeF 1 (liftc 0 ṗ) (lineOkB nil #1 #0)` **sí** computa a
`andc … (bdAllCode (lencT …) (orc … …))` —comprobado— pero sus capas de `liftc` no coinciden con
las que produce un `bdCarcLtDot` construido de cero (comprobado también, y falla).

⇒ **Los dos `PsiF` hay que diseñarlos JUNTOS**: primero el exterior, explícito y casado con el
destino por `rfl`, y el interior sale de él como sub‑término. Atacar `hbody`(b) aislado lleva a
un `PsiF` que compila pero que el ensamblaje exterior no puede consumir — el mismo modo de fallo
que `condD` (§3.44), y por la misma causa: **elegir la imagen cuando hay un destino fijo**.

⚠️ Y eso NO invalida nada de §5–§7: `pcc_bdCarcLt_reflect` y `pcc_premsBody_reflect` están
enunciados sobre argumentos **abstractos** (`y p b`, y el `Ac` libre del disyunto vacuo), así
que se instanciarán con las capas que el exterior imponga, sean las que sean. Es exactamente
para lo que se dejaron abstractos. -/


/-! ## §8 · EL `PsiF` EXTERIOR DE `chainOkB` — y con él, `hmatch` DESCARGADO (2026‑09‑09g)

§7.2 midió que los dos `PsiF` hay que diseñarlos juntos, y que el orden es **de fuera adentro**.
Esto hace el de fuera, con el mismo método que §7.1: **leer la definición de `substCodeF`**, no
adivinar la forma. Las tres igualdades de abajo son `rfl` y certifican la lectura. -/

/-- ⭐ **EL `PsiF` EXTERIOR**: el cuerpo del `∀` acotado de `chainOkB`, ya bajo el binder.
    Correcto por construcción — es literalmente lo que `substCodeF` produce en esa posición. -/
noncomputable def chainOkBPsi (W p : Term) : Term :=
  substCodeF 1 (liftc zero W) (lineOkB nil (liftTerm 0 p) (.var 0))

/-- La descomposición exterior, genérica en `W` y `p`. -/
theorem substCodeF_chainOkB (W p : Term) :
    substCodeF 0 W (chainOkB nil p)
      = bdAllCode (substCodeT 1 (liftc zero W) (liftTerm 0 (lenc p))) (chainOkBPsi W p) := rfl

/-- ⭐⭐ **LA CONEXIÓN CON §7**: el `PsiF` exterior se parte en el `andc` de las dos mitades de
    `lineOkB`, y la derecha **es** el código de `boundedPremsIn` que §7.1 descompuso — con las
    capas de `liftc` que le impone su posición, que era justo lo que §7.2 advertía. Los dos
    `PsiF` quedan así conectados por construcción, no por conjetura. -/
theorem chainOkBPsi_split (W p : Term) :
    chainOkBPsi W p
      = andc (substCodeF 1 (liftc zero W) (lineWF (nthc (liftTerm 0 p) (.var 0))))
             (substCodeF 1 (liftc zero W)
               (boundedPremsIn nil (liftTerm 0 p) (.var 0)
                 (premsOf (nthc (liftTerm 0 p) (.var 0))))) := rfl

/-- La instancia que el destino usa: `p := #0`, `W := ṗ`. ⭐ La cota sale **exactamente** la que
    §3 midió (`lencT (liftc 0 ṗ)`), sin ningún transporte. -/
theorem substCodeF_chainOkB_at :
    substCodeF 0 (tcFn (.var 0)) (chainOkB nil (.var 0))
      = bdAllCode (lencT (liftc zero (tcFn (.var 0))))
          (chainOkBPsi (tcFn (.var 0)) (.var 0)) := rfl

/-- ⭐⭐⭐ **`hmatch` DESCARGADO.** La hipótesis que §4 dejaba abierta —que el `bdAllCode` con la
    cota del destino sea el destino— es ahora un teorema: la igualdad de códigos la da §3
    (`prf_substfc_arith_open`) y la forma la da el `rfl` de arriba. -/
theorem hmatch_chainOkB :
    Prf (bdAllCode (lencT (liftc zero (tcFn (.var 0))))
        (chainOkBPsi (tcFn (.var 0)) (.var 0)) =eq chainOkBDot) :=
  prf_eq_symm chainOkBDot_eq_substCodeF

/-- ⭐⭐⭐ **D3 REDUCIDA A TRES OBLIGACIONES SOBRE UN `PsiF` YA FIJADO.** Comparado con
    `DEUDA_chainOkBDot_of` (§4), el cuerpo deja de ser un parámetro libre y `hmatch` desaparece:
    lo que queda es la invariancia del cuerpo, su testigo, y el `pcc_bdAll_intro`. -/
theorem DEUDA_chainOkBDot_of_hbdAll [AnclaEq]
    (hPinv : ∀ u : Term, Prf (substfc (succ zero) u (chainOkBPsi (tcFn (.var 0)) (.var 0))
      =eq chainOkBPsi (tcFn (.var 0)) (.var 0)))
    (hwP : Prf (hasWitF (bdAllBndCtx (chainOkBPsi (tcFn (.var 0)) (.var 0)))))
    (hbdAll : Prf (chainOk nil (.var 0) ⇒
      provFromCode (bdAllCode (tcFn (lenc (.var 0)))
        (chainOkBPsi (tcFn (.var 0)) (.var 0))))) :
    DEUDA_chainOkBDot :=
  DEUDA_chainOkBDot_of _ hPinv hwP hmatch_chainOkB hbdAll

/-- Y **D3 entera** desde las mismas tres. -/
theorem d3_prf_of_hbdAll [AnclaEq] (φ : Formula)
    (hPinv : ∀ u : Term, Prf (substfc (succ zero) u (chainOkBPsi (tcFn (.var 0)) (.var 0))
      =eq chainOkBPsi (tcFn (.var 0)) (.var 0)))
    (hwP : Prf (hasWitF (bdAllBndCtx (chainOkBPsi (tcFn (.var 0)) (.var 0)))))
    (hbdAll : Prf (chainOk nil (.var 0) ⇒
      provFromCode (bdAllCode (tcFn (lenc (.var 0)))
        (chainOkBPsi (tcFn (.var 0)) (.var 0))))) :
    Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_chainOkBDot φ (DEUDA_chainOkBDot_of_hbdAll hPinv hwP hbdAll)


/-! ## §9 · 🏁 `hPinv` PARA `chainOkBPsi`, PROBADO (2026‑09‑09h)

Con `substfc_inv_substCodeF_at` (`Meta/BdAllIntroPrf.lean`) la obligación sale en tres
hipótesis, todas baratas, porque el testigo es un **código punteado**:

* invariante a TODO nivel — `prf_substtc_tcFn_at` con el `liftc` colapsado;
* su `liftc zero` COLAPSA — `prf_liftc_tcFn`;
* el cuerpo no tiene variables libres ≥ 2 — `simp` sobre `liftFormula_lineOkB`.

⚠️ **Y el ÍNDICE importa**: `chainOkBPsi = substCodeF 1 …` y `hPinv` actúa al nivel **1**, no
al 2. Por eso hace falta la variante `_at` (nivel actuante = `v`) y no la de `v+1`. Con la otra
el enunciado también es cierto, pero **no es el que `pcc_bdAll_intro` consume**. -/

/-- ⭐ **GENÉRICA en `q`** (2026‑09‑10, ADR‑019): §11 la necesita con `q` abierto, y el
    enunciado no dependía de `#0` para nada. La instancia `q := #0` es la que consume
    `hPinv_chainOkBPsi`. -/
theorem hW_chainOkBPsi (q : Term) : ∀ (k : Nat) (u : Term),
    Prf (substtc (numeral k) u (liftc zero (tcFn q)) =eq liftc zero (tcFn q)) :=
  fun k u => prf_eq_trans (prf_congr_substtc3 (prf_liftc_tcFn q))
    (prf_eq_trans (prf_substtc_tcFn_at k u q)
      (prf_eq_symm (prf_liftc_tcFn q)))

theorem hL_chainOkBPsi (q : Term) :
    Prf (liftc zero (liftc zero (tcFn q)) =eq liftc zero (tcFn q)) :=
  prf_congr_liftc (prf_liftc_tcFn q)

/-- El cuerpo `lineOkB nil #1 #0` no tiene variables libres ≥ 2. -/
theorem hfv_chainOkBPsi : liftFormula 2 (lineOkB nil (.var 1) (.var 0))
    = lineOkB nil (.var 1) (.var 0) := by
  have h1 : (1 : Nat) < 2 := by omega
  have h0 : (0 : Nat) < 2 := by omega
  simp only [liftFormula_lineOkB, liftTerm, nil, zero, liftTerms, if_pos h1, if_pos h0]

/-- ⭐⭐⭐ **`hPinv` PARA `chainOkBPsi`.** Una de las tres obligaciones que §8 dejó abiertas,
    cerrada. -/
theorem hPinv_chainOkBPsi : ∀ u : Term,
    Prf (substfc (succ zero) u (chainOkBPsi (tcFn (.var 0)) (.var 0))
      =eq chainOkBPsi (tcFn (.var 0)) (.var 0)) :=
  fun u => substfc_inv_substCodeF_at 1 (liftc zero (tcFn (.var 0)))
    (hW_chainOkBPsi (.var 0)) (hL_chainOkBPsi (.var 0))
    (lineOkB nil (.var 1) (.var 0)) hfv_chainOkBPsi u

/-- Y D3 baja a **DOS** obligaciones. -/
theorem DEUDA_chainOkBDot_of_two [AnclaEq]
    (hwP : Prf (hasWitF (bdAllBndCtx (chainOkBPsi (tcFn (.var 0)) (.var 0)))))
    (hbdAll : Prf (chainOk nil (.var 0) ⇒
      provFromCode (bdAllCode (tcFn (lenc (.var 0)))
        (chainOkBPsi (tcFn (.var 0)) (.var 0))))) :
    DEUDA_chainOkBDot :=
  DEUDA_chainOkBDot_of_hbdAll hPinv_chainOkBPsi hwP hbdAll

theorem d3_prf_of_two [AnclaEq] (φ : Formula)
    (hwP : Prf (hasWitF (bdAllBndCtx (chainOkBPsi (tcFn (.var 0)) (.var 0)))))
    (hbdAll : Prf (chainOk nil (.var 0) ⇒
      provFromCode (bdAllCode (tcFn (lenc (.var 0)))
        (chainOkBPsi (tcFn (.var 0)) (.var 0))))) :
    Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_chainOkBDot φ (DEUDA_chainOkBDot_of_two hwP hbdAll)

/-! ## §10 · ⛔ EL `PsiF` DEL CHASIS **NO PUEDE SER** `chainOkBPsi` — y el que sí (2026‑09‑09i)

§8 fijó `chainOkBPsi` como el cuerpo del `bdAllCode` **del destino**, y lo hizo bien: es lo que
`hmatch` necesita, y sale por `rfl`. Pero al ir a aplicarle `pcc_bdAll_intro` aparece una
obstrucción que **no es de esfuerzo, es de enunciado**:

    hPl : ∀ k q, liftTerm k (PsiF q) = PsiF (liftTerm k q)

es **FALSA** para `PsiF q := chainOkBPsi (tcFn q) q`.

⚠️ Y no es una conjetura: el núcleo está medido en §10.1 y lo certifica el **compilador**.
`chainOkBPsi W p = substCodeF 1 (liftc 0 W) (lineOkB nil (liftTerm 0 p) #0)`, y `substCodeF`
manda las variables del argumento a **códigos cerrados** (`varc (numeral n)`) o al **hueco** `W`,
según su nivel. Un `liftTerm` en `q` mueve la variable **fuera del hueco**: donde antes salía el
testigo, ahora sale un `varc` cerrado. Los dos lados dejan de ser el mismo término.

🔑 **La regla que sale de aquí, y que el molde de `argsInPsi` ya cumplía sin decirlo:**

> El `PsiF` de `pcc_bdAll_intro` tiene que estar escrito con **símbolos de función OBJETO**
> (`substfc`, `liftc`, `tcFn`, `nthcT`…), **nunca con un `substCodeF` aplicado a una fórmula que
> contenga el parámetro**. Los símbolos objeto son `Term.func`: `liftTerm`/`substTerm` los
> atraviesan y la naturalidad es `simp`. `substCodeF` es una función de LEAN que **recursa sobre
> la fórmula**, y ahí la naturalidad es falsa.

⇒ Se construye el `PsiF` **dotado** —todo objeto, con el código de la fórmula **cerrado y sin
`q`**— y el paso a `chainOkBPsi` se hace **dentro de `Prov`** con `prf_substfc_arith_open`, que es
exactamente el puente de §3 usado al revés: allí se abría el destino opaco hacia el gemelo
computable; aquí se cierra el gemelo computable hacia el opaco, que es el que sabe ser natural. -/

/-! ### §10.1 · La medición, certificada por `rfl` -/

/-- El hueco (`n = v`) entrega el testigo… -/
theorem substCodeT_hole_lhs (w : Term) :
    liftTerm 0 (substCodeT 1 w (.var 1)) = liftTerm 0 w := rfl

/-- …pero tras el `liftTerm` la variable ya **no** cae en el hueco, y sale un `varc` CERRADO.
    ⇒ `liftTerm 0 w` frente a `varc (numeral 1)`: la naturalidad es falsa. -/
theorem substCodeT_hole_rhs (w : Term) :
    substCodeT 1 (liftTerm 0 w) (liftTerm 0 (.var 1)) = varc (numeral 1) := rfl

/-! ### §10.2 · El `PsiF` DOTADO, y su naturalidad -/

/-- ⭐⭐ **EL `PsiF` QUE EL CHASIS SÍ CONSUME.** Mismo contenido que `chainOkBPsi`, escrito con
    símbolos OBJETO: el parámetro `q` aparece sólo dentro de `tcFn`, y el código de la fórmula es
    **cerrado**. Por eso `liftTerm`/`substTerm` lo atraviesan. -/
noncomputable def chainOkBPsiDot (q : Term) : Term :=
  substfc (numeral 1) (liftc zero (tcFn q)) (formCode (lineOkB nil (.var 1) (.var 0)))

/-- La obligación `hPl`, ahora **verdadera** y `simp`. -/
theorem liftT_chainOkBPsiDot (k : Nat) (q : Term) :
    liftTerm k (chainOkBPsiDot q) = chainOkBPsiDot (liftTerm k q) := by
  simp only [chainOkBPsiDot, substfc, liftc, tcFn, zero, liftTerm, liftTerms,
    liftTerm_numeral, liftTerm_formCode]

/-- La obligación `hPs`. Consume `substTerm_formCode` (`Meta/LiftcCodePrf.lean`), el gemelo del
    `liftTerm_formCode` de `DerivCondPrf` que hasta hoy no existía. -/
theorem substT_chainOkBPsiDot (v : Nat) (s q : Term) :
    substTerm v s (chainOkBPsiDot q) = chainOkBPsiDot (substTerm v s q) := by
  simp only [chainOkBPsiDot, substfc, liftc, tcFn, zero, substTerm, substTerms,
    substTerm_numeral, substTerm_formCode]

/-- ⭐⭐ **EL PUENTE**, en la instancia del destino: `prf_substfc_arith_open` al nivel 1.
    ⚠️ El argumento fórmula es `lineOkB nil #1 #0` —cerrado— y a `q := #0` coincide con el
    `lineOkB nil (liftTerm 0 #0) #0` de `chainOkBPsi`, porque `liftTerm 0 #0 = #1`. -/
theorem chainOkBPsiDot_eq :
    Prf (chainOkBPsiDot (.var 0) =eq chainOkBPsi (tcFn (.var 0)) (.var 0)) :=
  prf_substfc_arith_open 1 (liftc zero (tcFn (.var 0))) (lineOkB nil (.var 1) (.var 0))

/-! ### §10.3 · Las cuatro obligaciones administrativas

`CF q := chainOk nil q` es un **átomo** (`Formula.atom "chainOk" [nil, q]`) y `bndF q := lenc q`
un símbolo de función objeto: las cuatro son `simp`. -/

theorem hCl_chainOk (k : Nat) (q : Term) :
    liftFormula k (chainOk nil q) = chainOk nil (liftTerm k q) := by
  simp only [chainOk, nil, zero, liftFormula, liftTerm, liftTerms]

theorem hCs_chainOk (v : Nat) (s q : Term) :
    substFormula v s (chainOk nil q) = chainOk nil (substTerm v s q) := by
  simp only [chainOk, nil, zero, substFormula, substTerm, substTerms]

theorem hbl_lenc (k : Nat) (q : Term) : liftTerm k (lenc q) = lenc (liftTerm k q) := by
  simp only [lenc, liftTerm, liftTerms]

theorem hbs_lenc (v : Nat) (s q : Term) :
    substTerm v s (lenc q) = lenc (substTerm v s q) := by
  simp only [lenc, substTerm, substTerms]

/-! ### §10.4 · `hwPsi`, DESCARGADA

⭐ El testigo del cuerpo sale de la rama C de ADR‑020 sin trabajo nuevo: `prf_hasWitF_substfc`
pide `hasWitF` del código y `hasWit` del sustituyente, y las dos están —el código es un `formCode`
(`prf_hasWitF_fc`) y el sustituyente un `liftc` de un punteado (`prf_hasWit_tcFn` +
`CRIT_hasWit_lift`)—. Es exactamente el dividendo de que el `PsiF` sea DOTADO: sobre el
`substCodeF` de §8 no había nada que aplicar. -/

theorem hwS_chainOkBPsiDot (q : Term) : Prf (hasWit (liftc zero (tcFn q))) :=
  prf_mp (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.CRIT_hasWit_lift (tcFn q))
    (ROBINSON_PlusPlus.Meta.HasWitTcFnPrf.prf_hasWit_tcFn q)

theorem hwPsi_chainOkBPsiDot (q : Term) : Prf (hasWitF (chainOkBPsiDot q)) :=
  prf_mp (prf_mp (prf_hasWitF_substfc (numeral 1) (liftc zero (tcFn q))
      (formCode (lineOkB nil (.var 1) (.var 0))))
    (ROBINSON_PlusPlus.Meta.Representability2.prf_hasWitF_fc _)) (hwS_chainOkBPsiDot q)

/-! ### §10.5 · EL ENSAMBLAJE -/

/-- El transporte del cuerpo dotado al que el destino pide, **dentro de `Prov`**. -/
theorem hbdAll_of_dotted
    (h : Prf (chainOk nil (.var 0) ⇒
      provFromCode (bdAllCode (tcFn (lenc (.var 0))) (chainOkBPsiDot (.var 0))))) :
    Prf (chainOk nil (.var 0) ⇒
      provFromCode (bdAllCode (tcFn (lenc (.var 0)))
        (chainOkBPsi (tcFn (.var 0)) (.var 0)))) :=
  prf_syll h (prf_provCode_congr (prf_congr_bdAllCode (prf_refl _) chainOkBPsiDot_eq))

/-- ⭐⭐⭐ **`pcc_bdAll_intro`, YA APLICABLE**: siete de sus nueve obligaciones descargadas.
    Antes de §10 no lo era en absoluto — `hPl` era falsa. -/
theorem hbdAllDot_of_body [AnclaEq]
    (hPsiId : ∀ q : Term,
      Prf (substfc zero (varc (numeral 0)) (chainOkBPsiDot q) =eq chainOkBPsiDot q))
    (hbody : ∀ q i : Term, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (substfc zero (tcFn i) (chainOkBPsiDot q))))) :
    Prf (chainOk nil (.var 0) ⇒
      provFromCode (bdAllCode (tcFn (lenc (.var 0))) (chainOkBPsiDot (.var 0)))) :=
  pcc_bdAll_intro (fun q => chainOk nil q) (fun q => lenc q) chainOkBPsiDot (.var 0)
    hCl_chainOk hCs_chainOk hbl_lenc hbs_lenc
    liftT_chainOkBPsiDot substT_chainOkBPsiDot hPsiId hwPsi_chainOkBPsiDot hbody

/-- ⭐⭐⭐ **D3 DESDE TRES OBLIGACIONES**, y las tres sobre el `PsiF` DOTADO. -/
theorem d3_prf_of_body [AnclaEq] (φ : Formula)
    (hwP : Prf (hasWitF (bdAllBndCtx (chainOkBPsi (tcFn (.var 0)) (.var 0)))))
    (hPsiId : ∀ q : Term,
      Prf (substfc zero (varc (numeral 0)) (chainOkBPsiDot q) =eq chainOkBPsiDot q))
    (hbody : ∀ q i : Term, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (substfc zero (tcFn i) (chainOkBPsiDot q))))) :
    Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_two φ hwP (hbdAll_of_dotted (hbdAllDot_of_body hPsiId hbody))

/-! ### §10.6 · Lo que queda, y por qué `hPsiId` **no** sale de §9

| obligación de `pcc_bdAll_intro` | estado |
|---|---|
| `hCl`, `hCs`, `hbl`, `hbs` | ✅ §10.3 |
| `hPl`, `hPs` | ✅ §10.2 — y eran **falsas** con el `PsiF` de §8 |
| `hwPsi` | ✅ §10.4 |
| **`hPsiId`** | ⬜ ver abajo |
| **`hbody`** | ⬜ el contenido real: (a) `pcc_lineWF_tracked` (5 de 7) + (b) `boundedPremsIn` |

⚠️ **`hPsiId` NO es `hPinv` con otro nombre, y la familia de §9 no la cubre.** Las dos variantes
de `substfc_inv_substCodeF` actúan al nivel del propio `substCodeF` (`v`) o uno por encima
(`v+1`); `hPsiId` actúa al nivel **0** sobre un `substCodeF 1 …`, o sea **por debajo**. Y por
debajo el enunciado cambia de carácter: `substfc` al nivel 0 **decrementa** las variables de
código de nivel > 0 (es la rama `n > v` de `substCodeT`), así que no basta con que el testigo sea
invariante.

⭐ **Pero el enunciado es cierto, y está medido por qué**: en `substCodeF 1 W (lineOkB nil #1 #0)`
los únicos huecos de nivel 0 son los que vienen de `#0`, que `substCodeF` ya mandó a
`varc (numeral 0)` —y sustituir `#0` por `varc 0̄` los deja igual—; y todo lo demás vive dentro de
`W = liftc 0 ṫq`, que es invariante **a todo nivel** (`hW_chainOkBPsi` de §9, probado justo con
esa fuerza: `∀ k u`). ⇒ falta la **tercera variante** de la familia, la de nivel actuante **por
debajo** del `substCodeF`, con testigo `varc (numeral w)`. Es la misma inducción de §9 con la
aritmética de índices corrida, no maquinaria nueva.

🔑 Y la lección de método: **el destino fija la IMAGEN, pero el chasis fija la FORMA en que hay
que escribirla**. `chainOkBPsi` es la imagen correcta y `chainOkBPsiDot` la escritura correcta;
hacen falta las dos, y el puente entre ellas vive dentro de `Prov`. -/

/-! ## §11 · 🏁 `hPsiId` PROBADO — D3 baja a DOS obligaciones (2026‑09‑10)

§10.6 dejó `hPsiId` medida y con el diagnóstico escrito: **no** es `hPinv` con otro nombre, hace
falta la **tercera variante** de la familia —nivel actuante **por debajo** del `substCodeF`—, y el
enunciado es cierto por dos razones concretas. Las dos se han convertido en las dos hipótesis del
lema genérico, que vive donde le corresponde:

* **`substtc_id_substCodeT` / `_Ts`** (`Meta/SubstCodeOpenPrf.lean` §5) — el sorte TÉRMINO;
* **`substfc_id_substCodeF`** (`Meta/BdAllIntroPrf.lean`) — el sorte FÓRMULA.

⚠️ **Lo que cambia respecto de `hPinv`, y por qué:** actuando por debajo del hueco, la casilla
`n = v` ya no es el testigo de código sino una `varc v̄` corriente, y `substtc` la sustituye **por
el testigo**. ⇒ **el testigo deja de ser libre**: hace falta `u ≐ varc v̄`, y como igualdad
OBJETO, porque bajo los binders lo que aparece es `liftc 0 u` y no la variable. El puente es
`prf_liftc_varc_numeral`, que de paso **absorbe** el `prf_liftc_varc0` de `TrackedAtomsPrf`
(ADR‑019: era su instancia `v := 0`).

⭐ Y el índice **no admite salto**: si el código se construyera a `v+2` o más, entre el nivel
actuante y el hueco quedarían variables que `substtc` **decrementaría**, y el enunciado sería
FALSO. Es exactamente «uno por debajo», ni más ni menos — la tercera vez que el índice resulta no
ser cosmético en este frente. -/

/-- ⭐⭐⭐ **`hPsiId` PARA `chainOkBPsiDot`.** La segunda de las tres obligaciones de §10, cerrada.

    La ruta es la de siempre: **abrir el dotado hacia su gemelo computable** con
    `prf_substfc_arith_open`, aplicar el genérico allí, y volver. Las tres hipótesis son las de
    §9 —el testigo es un código punteado— más `hfv_chainOkBPsi`, que ya estaba probada con el
    índice correcto (`liftFormula 2`, que es justo el `v+2` con `v := 0`). -/
theorem hPsiId_chainOkBPsiDot (q : Term) :
    Prf (substfc zero (varc (numeral 0)) (chainOkBPsiDot q) =eq chainOkBPsiDot q) :=
  prf_eq_trans
    (prf_congr_substfc3
      (prf_substfc_arith_open 1 (liftc zero (tcFn q)) (lineOkB nil (.var 1) (.var 0))))
    (prf_eq_trans
      (substfc_id_substCodeF 0 (liftc zero (tcFn q))
        (hW_chainOkBPsi q) (hL_chainOkBPsi q)
        (lineOkB nil (.var 1) (.var 0)) hfv_chainOkBPsi (varc (numeral 0)) (prf_refl _))
      (prf_eq_symm
        (prf_substfc_arith_open 1 (liftc zero (tcFn q)) (lineOkB nil (.var 1) (.var 0)))))

/-- `pcc_bdAll_intro` con **OCHO de sus nueve** obligaciones descargadas. -/
theorem hbdAllDot_of_hbody [AnclaEq]
    (hbody : ∀ q i : Term, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (substfc zero (tcFn i) (chainOkBPsiDot q))))) :
    Prf (chainOk nil (.var 0) ⇒
      provFromCode (bdAllCode (tcFn (lenc (.var 0))) (chainOkBPsiDot (.var 0)))) :=
  hbdAllDot_of_body hPsiId_chainOkBPsiDot hbody

/-- ⭐⭐⭐ **D3 DESDE DOS OBLIGACIONES**: el testigo del cuerpo y el cuerpo. -/
theorem DEUDA_chainOkBDot_of_hbody [AnclaEq]
    (hwP : Prf (hasWitF (bdAllBndCtx (chainOkBPsi (tcFn (.var 0)) (.var 0)))))
    (hbody : ∀ q i : Term, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (substfc zero (tcFn i) (chainOkBPsiDot q))))) :
    DEUDA_chainOkBDot :=
  DEUDA_chainOkBDot_of_two hwP (hbdAll_of_dotted (hbdAllDot_of_hbody hbody))

/-- Y **D3 entera** desde esas dos. -/
theorem d3_prf_of_hbody [AnclaEq] (φ : Formula)
    (hwP : Prf (hasWitF (bdAllBndCtx (chainOkBPsi (tcFn (.var 0)) (.var 0)))))
    (hbody : ∀ q i : Term, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (substfc zero (tcFn i) (chainOkBPsiDot q))))) :
    Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_chainOkBDot φ (DEUDA_chainOkBDot_of_hbody hwP hbody)

/-! ### §11.1 · Lo que queda de D3

| pieza | estado |
|---|---|
| §3–§10 y las **ocho** obligaciones administrativas del chasis | ✅ |
| **`hwP`** — `hasWitF (bdAllBndCtx (chainOkBPsi …))` | ⬜ **no depende de C3** |
| **`hbody`**(a) — reflexión de `lineWF` = `pcc_lineWF_tracked` | ⬜ **5 de 7** (`modulo_2`) |
| **`hbody`**(b) — reflexión de `boundedPremsIn` | ⬜ núcleo probado (§5, §6), falta ensamblar |

⇒ Sólo `hbody`(a) sigue aguas abajo de C3, y su desbloqueo es `prf_hasWitF_liftfc`. -/

/-! ## §12 · 🏁🏁 `hwP` PROBADO — **D3 queda en UNA sola obligación** (2026‑09‑10)

⭐⭐ **Y sale en cuatro líneas, como dividendo directo de §10.** `hwP` pide el testigo del cuerpo
**bajo el contexto del `bdAll`**:

    hasWitF (bdAllBndCtx (chainOkBPsi ṗ #0))
      = hasWitF (forallc (implc (ltCodeFn ⌜v₀⌝ ⌜v₁⌝) (chainOkBPsi ṗ #0)))

y se parte en dos por el KIT de ADR‑020 (`prf_hasWitF_forallc` + `prf_hasWitF_implc`):

* la **cota** —un átomo de `lt` entre dos variables de código— la cierra `hw_auto` sola;
* el **cuerpo** es donde §10 cobra: el testigo está probado para el `PsiF` **dotado**
  (`hwPsi_chainOkBPsiDot`, que salió gratis de la rama C), y **se transporta** al computable por
  el mismo puente `chainOkBPsiDot_eq`, esta vez con **Leibniz OBJETO** (`prf_congr_hasWitF`).

🔑 Es la **tercera vez** que el par «cuerpo dotado + cuerpo computable, puenteados dentro de la
teoría» paga: `hmatch` (§8) casó el destino, `hbdAll_of_dotted` (§10.5) transportó la prueba, y
aquí transporta el **testigo**. La regla de §10 —*el destino fija la imagen, el chasis fija la
forma*— no era una molestia administrativa: es lo que hace que las tres cosas viajen. -/

/-- ⭐⭐⭐ **`hwP`, PROBADO.** La última obligación no‑`hbody` de D3. -/
theorem hwP_chainOkBPsi :
    Prf (hasWitF (bdAllBndCtx (chainOkBPsi (tcFn (.var 0)) (.var 0)))) := by
  have hPsi : Prf (hasWitF (chainOkBPsi (tcFn (.var 0)) (.var 0))) :=
    prf_congr_hasWitF chainOkBPsiDot_eq (hwPsi_chainOkBPsiDot (.var 0))
  unfold bdAllBndCtx bdAllCode
  exact prf_hasWitF_forallc _ (prf_hasWitF_implc _ _ (by hw_auto) hPsi)

/-- ⭐⭐⭐ **`DEUDA_chainOkBDot` DESDE `hbody` Y NADA MÁS.** -/
theorem DEUDA_chainOkBDot_of_body_only [AnclaEq]
    (hbody : ∀ q i : Term, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (substfc zero (tcFn i) (chainOkBPsiDot q))))) :
    DEUDA_chainOkBDot :=
  DEUDA_chainOkBDot_of_hbody hwP_chainOkBPsi hbody

/-- ⭐⭐⭐ **D3 DESDE `hbody` Y NADA MÁS.**

    Todo lo demás —el puente átomo↔forma acotada, la cota, el `∃` acotado, el cuerpo del `∀`, el
    empaquetado, los dos `PsiF`, `hmatch`, `hPinv`, `hPsiId` y `hwP`— está **probado**, y con
    footprint igual a la base sancionada. -/
theorem d3_prf_of_body_only [AnclaEq] (φ : Formula)
    (hbody : ∀ q i : Term, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (substfc zero (tcFn i) (chainOkBPsiDot q))))) :
    Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_chainOkBDot φ (DEUDA_chainOkBDot_of_body_only hbody)

/-! ### §12.1 · Lo que queda de D3: **`hbody`, y sólo `hbody`**

    hbody : ∀ q i, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
              provFromCode (substfc 0 (tcFn i) (chainOkBPsiDot q))))

Y se parte —por `chainOkBPsi_split` (§8), que conecta los dos `PsiF` **por construcción**— en:

| mitad | estado |
|---|---|
| **(a)** reflexión de `lineWF` = `pcc_lineWF_tracked` | ⬜ **5 de 7** reflectores (`modulo_2`); faltan `ind` (18) y `listInd` (20) |
| **(b)** reflexión de `boundedPremsIn` | ⬜ núcleo probado sobre argumentos ABSTRACTOS (§5, §6); falta ensamblar |

⇒ **(a) es lo único de D3 que sigue aguas abajo de C3**, y su desbloqueo es `prf_hasWitF_liftfc`.
**(b) no depende de C3 en absoluto**: sus piezas se dejaron abstractas en §5–§6 exactamente para
que se instancien con las capas de `liftc`/`substCodeT` que el exterior imponga. -/

/-! ## §13 · `hbody` PARTIDO EN SUS DOS MITADES — y una corrección de §12.1 (2026‑09‑10)

§12 dejó D3 en `hbody`. Para partirlo hay que **componer los dos `substfc`**: el que el chasis
aplica (`substfc 0̄ (tcFn i)`) y el que el propio `PsiF` dotado ES (ADR‑021). Esa composición es
`substfc_comp_substCodeF` (`Meta/BdAllIntroPrf.lean`), y con ella el cuerpo se abre y **se parte
por `rfl`** en las dos mitades de `lineOkB`.

⚠️⚠️ **Y aquí hay que corregir §12.1 y §3.58.3.** Allí se dijo que la mitad **(b)** «no depende de
C3» y que era «ensamblaje, no maquinaria nueva». **Es FALSO**, y la medición está abajo (§13.1).
La causa: `lineOkB` mete `premsOf (nthc p i)` en el código, y `premsOf` **no es evaluable
uniformemente**. -/

/-- El código de la mitad **(a)** del cuerpo: la reflexión de `lineWF`. -/
noncomputable def lineWFDotAt (q i : Term) : Term :=
  substCodeF2 0 (tcFn i) (liftc zero (tcFn q)) (lineWF (nthc (.var 1) (.var 0)))

/-- El código de la mitad **(b)**: la reflexión de `boundedPremsIn`. -/
noncomputable def premsDotAt (q i : Term) : Term :=
  substCodeF2 0 (tcFn i) (liftc zero (tcFn q))
    (boundedPremsIn nil (.var 1) (.var 0) (premsOf (nthc (.var 1) (.var 0))))

/-- ⭐⭐ **EL CUERPO DEL CHASIS, ABIERTO.** Los dos `substfc` compuestos en uno de dos huecos.
    Las tres hipótesis ya estaban: `hW`/`hL` de §9 (genéricas en `q`) y `hfv_chainOkBPsi`, que
    tiene justo el índice que pide la composición (`liftFormula 2` = el `v+2` con `v := 0`). -/
theorem substfc_chainOkBPsiDot (q i : Term) :
    Prf (substfc zero (tcFn i) (chainOkBPsiDot q)
      =eq substCodeF2 0 (tcFn i) (liftc zero (tcFn q)) (lineOkB nil (.var 1) (.var 0))) :=
  prf_eq_trans
    (prf_congr_substfc3
      (prf_substfc_arith_open 1 (liftc zero (tcFn q)) (lineOkB nil (.var 1) (.var 0))))
    (substfc_comp_substCodeF 0 (tcFn i) (liftc zero (tcFn q))
      (hW_chainOkBPsi q) (hL_chainOkBPsi q)
      (lineOkB nil (.var 1) (.var 0)) hfv_chainOkBPsi)

/-- Y el cuerpo abierto **se parte por `rfl`**: `lineOkB` es un `land`. -/
theorem substCodeF2_lineOkB_split (u W : Term) :
    substCodeF2 0 u W (lineOkB nil (.var 1) (.var 0))
      = andc (substCodeF2 0 u W (lineWF (nthc (.var 1) (.var 0))))
             (substCodeF2 0 u W (boundedPremsIn nil (.var 1) (.var 0)
               (premsOf (nthc (.var 1) (.var 0))))) := rfl

/-- La igualdad completa, con los dos códigos ya nombrados. -/
theorem substfc_chainOkBPsiDot_split (q i : Term) :
    Prf (substfc zero (tcFn i) (chainOkBPsiDot q)
      =eq andc (lineWFDotAt q i) (premsDotAt q i)) :=
  substfc_chainOkBPsiDot q i

/-- ⭐⭐⭐ **`hbody` DESDE SUS DOS MITADES.** -/
theorem hbody_of_halves
    (hA : ∀ q i : Term, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (lineWFDotAt q i))))
    (hB : ∀ q i : Term, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (premsDotAt q i)))) :
    ∀ q i : Term, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (substfc zero (tcFn i) (chainOkBPsiDot q)))) := by
  intro q i
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [chainOk nil q] rfl)
  have hch : PrfH [lt i (lenc q), chainOk nil q] (chainOk nil q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [lt i (lenc q), chainOk nil q] (lt i (lenc q)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have ha : PrfH [lt i (lenc q), chainOk nil q] (provFromCode (lineWFDotAt q i)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (hA q i) _) hch) hlt
  have hb : PrfH [lt i (lenc q), chainOk nil q] (provFromCode (premsDotAt q i)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (hB q i) _) hch) hlt
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (substfc_chainOkBPsiDot_split q i))) _)
    (PrfH_and_intro_code _ _ ha hb)

/-- ⭐⭐⭐ **D3 DESDE LAS DOS MITADES DEL CUERPO, y nada más.** -/
theorem d3_prf_of_halves [AnclaEq] (φ : Formula)
    (hA : ∀ q i : Term, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (lineWFDotAt q i))))
    (hB : ∀ q i : Term, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (premsDotAt q i)))) :
    Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_hbody φ hwP_chainOkBPsi (hbody_of_halves hA hB)

/-! ### §13.1 · ⛔ LA CORRECCIÓN: la mitad (b) **SÍ** depende del análisis por tags

§12.1 y §3.58.3 afirmaron que `hbody`(b) «no depende de C3» y era «ensamblaje». **Medido, y es
falso.** El destino de (b), desplegado capa a capa por `rfl`, es un `bdAllCode` cuya **cota** es

    lencT (premsOfT (nthcT (liftc 0 W) (varc 1̄)))

es decir, con el símbolo **`premsOf` DOTADO**. Y `pcc_bdAll_intro` entrega la cota como reflexión
pura `tcFn (bndF p)`, así que hay que cruzar —dentro de `Prov`— la cadena

    nthcT q̇ i̇     ↦ (nthc q i)˙          ✅ `pcc_eval_nthc`
    premsOfT Ẋ     ↦ (premsOf X)˙          ⛔ **NO EXISTE, y no puede existir uniformemente**
    lencT L̇        ↦ (lenc L)˙             ✅ `pcc_eval_lenc`

⛔ **Por qué el eslabón de en medio no existe**: `premsOf` **no está definido por recursión**, como
`lenc` o `nthc`, sino por **21 axiomas `ax_premsOf_*`, uno por TAG de regla**, y cada uno hace
*pattern‑matching sobre la FORMA de la línea*:

    ax_premsOf_mp  : premsOf (cons c (cons 16̄ (cons a nil))) ≐ cons (implc a c) (cons a nil)
    ax_premsOf_gen : premsOf (cons c (cons 17̄ (cons b nil))) ≐ cons b nil
    …

⇒ Para un `X` **abstracto**, `premsOf X` está **sin restringir**: no hay nada que evaluar. Sólo se
puede evaluar tras **saber el tag**, y saber el tag es exactamente el análisis de casos de
`lineWF` — o sea, la mitad **(a)**.

🏁🏁 **LEVANTADA el 2026‑09‑10** (`Meta/PremsOfTagPrf.lean`, §3.63). ⚠️ **A este diagnóstico le
faltaba una frase**: «no hay nada que evaluar» vale *mientras no se sepa la **LONGITUD***. Y la
longitud **sí** sale, del bicondicional del `ax_lineWF_*` del **mismo** tag (todos llevan la
cláusula canónica `lenc #0 ≐ n̄`). Con ella, la η de listas (`Meta/ListEtaPrf.lean`,
`prf_eta_lenc`) reconstruye la línea entera y `ax_premsOf_k` se aplica:

    lineWF t + lineTag t ≐ k̄ → lenc t ≐ n̄ → t ≐ ⟨carc t, carc (cdrc t), …⟩ → premsOf t ≐ R_k

⭐⭐ Y el coste, medido, salió **a la baja**: no son 21 pruebas sino **dos lemas genéricos**, dos
envoltorios y **ocho líneas por tag**. La dependencia que este párrafo señala —que (b) consume el
análisis por tags— **sigue siendo cierta y sigue mandando el orden**; lo que ya no es cierto es que
sea cara.

🔑 ⇒ **Las dos mitades no son independientes: (b) consume el análisis por tags de (a).** Son
hermanas del mismo tamaño (21 tags frente a 23 esquemas `ax_lineWF_*`), no una barata y otra cara.

⚠️ **Y la lección de método, que es sobre MÍ, no sobre el árbol**: en §12.1 estimé el coste de (b)
**por su enunciado** —«el núcleo ya está probado sobre argumentos abstractos, sólo falta
instanciar»— sin haber desplegado el destino. Es exactamente el error que
[[feedback-medir-la-forma]] viene a evitar, y el mismo que ADR‑021 documenta un nivel más arriba:
**que las piezas estén enunciadas sobre argumentos abstractos no garantiza que el destino se deje
instanciar con ellas.** `pcc_bdCarcLt_reflect` y `pcc_premsBody_reflect` siguen siendo correctos y
seguirán haciendo falta; lo que no vale es la estimación de que bastaban.

### §13.2 · Lo que queda, con la dependencia REAL

| pieza | estado | depende de |
|---|---|---|
| `hbody` partido en (a) y (b), con los dos `substfc` compuestos | ✅ §13 | — |
| **(a)** `lineWFDotAt` = `pcc_lineWF_tracked` | 🏁 **PROBADA** (`Meta/D3BodyPrf.lean`), incondicional | — |
| **(b)** `premsDotAt` | ⬜ **tres** piezas nombradas, abajo | (a) ✅ |

⇒ El orden era **(a) primero**, y se cumplió: (a) está cerrada desde §3.62.4.

### §13.3 · Lo que queda de (b), con nombre (2026‑09‑10)

| pieza | qué es | apoyo |
|---|---|---|
| **B1** | `Prov(premsOfT ṫ ≐ (premsOf t)˙)` — la reflexión **punteada** de `premsOf` | nivel OBJETO ✅ (§3.63); la ruta es la de `pcc_eval_carc` (axioma **codificado** + `pcc_dot_cons`) |
| **B2** | el puente de la **cota** dentro de `Prov` | `pcc_eval_nthc` ✅ · **B1** ⬜ · `pcc_eval_lenc` ✅ |
| **B3** | el `pcc_bdAll_intro` **interior** (9 obligaciones, triple empaquetado) | el `PsiF` exterior (§8) y `chainOkBPsi_split`; el núcleo abstracto de §5–§6 |

⇒ Con B1+B2+B3, `hbody_of_halves` cierra `hbody` y `d3_prf_of_halves` cierra **D3**. -/

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
  bdCarcLtPhic bdCarcLtDot
  prf_contract pcc_bdEx_carc_reflect_gen hphi_bdCarcLt liftTerm_bdCarcLtPhic liftTerm_bdCarcLtDot
  substtc_inv_bdCarcLtB pcc_bdCarcLt_reflect
  pcc_premsBody_reflect pcc_premsBody_reflect_at
  pkP pkI pkL premsPair premsBnd
  hCl_premsPair hCs_premsPair hbl_premsBnd hbs_premsBnd
  premsBody substCodeF_boundedPremsIn substCodeF_premsBody
  chainOkBPsi substCodeF_chainOkB chainOkBPsi_split substCodeF_chainOkB_at
  hmatch_chainOkB DEUDA_chainOkBDot_of_hbdAll d3_prf_of_hbdAll
  hW_chainOkBPsi hL_chainOkBPsi hfv_chainOkBPsi hPinv_chainOkBPsi
  DEUDA_chainOkBDot_of_two d3_prf_of_two
  substCodeT_hole_lhs substCodeT_hole_rhs
  chainOkBPsiDot liftT_chainOkBPsiDot substT_chainOkBPsiDot chainOkBPsiDot_eq
  hCl_chainOk hCs_chainOk hbl_lenc hbs_lenc
  hwS_chainOkBPsiDot hwPsi_chainOkBPsiDot
  hbdAll_of_dotted hbdAllDot_of_body d3_prf_of_body
  hPsiId_chainOkBPsiDot hbdAllDot_of_hbody DEUDA_chainOkBDot_of_hbody d3_prf_of_hbody
  hwP_chainOkBPsi DEUDA_chainOkBDot_of_body_only d3_prf_of_body_only
  lineWFDotAt premsDotAt substfc_chainOkBPsiDot substCodeF2_lineOkB_split
  substfc_chainOkBPsiDot_split hbody_of_halves d3_prf_of_halves
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
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hPinv_chainOkBPsi
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_two
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.chainOkBPsiDot_eq
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hwPsi_chainOkBPsiDot
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_body
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hPsiId_chainOkBPsiDot
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_hbody
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hwP_chainOkBPsi
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_body_only
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.substfc_chainOkBPsiDot
#print axioms ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_halves
