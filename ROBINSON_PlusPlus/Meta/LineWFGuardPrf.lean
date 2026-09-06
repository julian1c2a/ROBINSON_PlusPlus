import ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
import ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
/-!
# `Meta/LineWFGuardPrf.lean` — el CHASIS del conjunto extra de ADR-020 (`hGuard`)

ADR-020 metió la guarda de buena formación **DENTRO** del `⇔` de los 7 esquemas
`ax_lineWF_*` de sustitución. Eso compra que el reflector de cada tag reciba la guarda como
**conjunto objeto** —y por eso `pcc_lineWF_tracked_modulo_7` conservó su firma exacta—, y
**debe** el reflector de ese conjunto: `hGuard`.

Este módulo es el chasis de esa deuda. Todo lo de aquí está compilado y es **net-0 puro**
(`[propext, Classical.choice, Quot.sound]`).

## Lo que trae

* **§1 `hcond_absorbe_extra`** — el lema que ENSAMBLA: con el reflector del conjunto extra
  `P` y el de la condición de siempre `C`, sale el de `P ∧ C`, que es la `hcond` que pide
  `pcc_lineWF_tracked_of_schema`. Es la pieza sobre la que se aceptó ADR-020 y vivía en
  **cinco copias fuera del build** (`sondeos/SegundoMuro.lean`, `sondeos/MedirC_Carga.lean`,
  `sondeos/MedirC_Enmienda.lean` y dos de `Probe/`). Entra **una vez**.
* **§2** la forma REAL de la enmienda: una **cascada anidada a la derecha** de guardas
  (`guardedCond`), no un par — y **verificada con `rfl` contra los siete axiomas de
  `Minimal/Axioms.lean`** (§2.1). Los siete tienen entre 1 y 3 guardas: 7 `hasWitF` + 4
  `hasWit` = los **11 conjuntos nuevos** que declara ADR-020.
* **§3 `hcond_absorbe_cascade`** — el chasis absorbe la cascada **entera** por inducción
  sobre la lista de casillas. Con esto la deuda de los 7 tags son **DOS** lemas genéricos
  (uno por constructor de `GuardSlot`), no siete ni once.
* **§4** las dos obligaciones, **enunciadas** (idioma de `Meta/Sigma1BoundedPrf.lean`: la
  deuda se enuncia, no se postula) y el cierre condicional `hGuard_of_deudas`.

## ⚠️ Lo que este módulo NO hace, y lo que está medido de lo que falta

No prueba `DEUDA_hGuardT`/`DEUDA_hGuardF`. Medido, lo que ya existe para atacarlas:

* los **átomos**, con términos **abstractos**: `pcc_lt_tracked` y `pcc_eq_tracked`
  (`s = t ⊢ Prov(⌜ṡ = ṫ⌝)` sale por congruencia dotada, no hace falta numeral);
* el **cuantificador acotado**: `pcc_bdAll_intro` (`Meta/BdAllIntroPrf.lean:313`), que es la
  keystone de `hC_dot` y ya lleva la guarda `hasWitF` de ADR-020 en sus hipótesis;
* el **`∃` sin cota**: `pcc_exIntro_code_open` (`Meta/Delta0ReflectPrf.lean:74`).

Lo que falta es el **recorrido** de `isTC1` / `isFC1` bajo el `∃`: la disyunción de formas
(`isTermCodeE1`, y las **ocho** cláusulas de `isFormCodeE2`) y el `argsIn` interno, que es un
segundo `∀` acotado anidado.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.LineWFGuardPrf

/-! ## §1 · EL CHASIS ABSORBE UN CONJUNTO EXTRA

Es el lema sobre el que se aceptó ADR-020, y hasta hoy sólo existía en `sondeos/`. -/

/-- **El chasis absorbe el conjunto extra.** Dado el reflector del conjunto extra `P` y el de
    la condición de siempre `C`, sale el reflector de `P ∧ C` — que es exactamente la `hcond`
    que pide `pcc_lineWF_tracked_of_schema`. Genérico en `P` y en `C`; net-0.

    El transporte final es lo único con contenido: `substfc` **distribuye sobre `andc`**
    (`prf_substfc_and`), así que `condD P t ∧̇ condD C t` ES `condD (P ∧ C) t`. -/
theorem hcond_absorbe_extra (P C : Formula) (t : Term) (n : Nat)
    (hP : Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒
      (substFormula 0 t P ⇒ provFromCode (condD P t)))))
    (hC : Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒
      (substFormula 0 t C ⇒ provFromCode (condD C t))))) :
    Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒
      (substFormula 0 t (Formula.and P C) ⇒ provFromCode (condD (Formula.and P C) t)))) := by
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (substFormula 0 t (Formula.and P C))
    [lenc t =eq numeralM n, lineWF t] rfl)
    (lenc t =eq numeralM n) [lineWF t] rfl)
  let Γ : List Formula :=
    [substFormula 0 t (Formula.and P C), lenc t =eq numeralM n, lineWF t]
  have hlw : PrfH Γ (lineWF t) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hln : PrfH Γ (lenc t =eq numeralM n) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hand : PrfH Γ (Formula.and (substFormula 0 t P) (substFormula 0 t C)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hPt : PrfH Γ (substFormula 0 t P) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hand
  have hCt : PrfH Γ (substFormula 0 t C) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hand
  have hPd : PrfH Γ (provFromCode (condD P t)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hP _) hlw) hln) hPt
  have hCd : PrfH Γ (provFromCode (condD C t)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hC _) hlw) hln) hCt
  have hcomp : Prf (andc (condD P t) (condD C t) =eq condD (Formula.and P C) t) :=
    prf_eq_symm (prf_substfc_and zero (tcFn t) (formCode P) (formCode C))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr hcomp) _)
    (PrfH_and_intro_code _ _ hPd hCd)

/-! ## §2 · LA FORMA REAL DE LA ENMIENDA: UNA CASCADA, NO UN PAR

⚠️ La enmienda **no** añade una guarda ni un par de guardas: añade entre **una y tres**
guardas por tag, **anidadas a la derecha**, delante de la condición estructural de siempre.
Escribirla como un par sería un lema correcto sobre la fórmula equivocada. -/

/-- Una casilla guardada: o la casilla `i` lleva código de TÉRMINO (`hasWit`), o lleva código
    de FÓRMULA (`hasWitF`). Es todo el vocabulario que necesitan los 7 tags. -/
inductive GuardSlot
  | wit  (i : Nat)
  | witF (i : Nat)
  deriving DecidableEq, Repr

/-- La fórmula objeto de una casilla, sobre la línea `#0`. -/
def GuardSlot.toF : GuardSlot → Formula
  | .wit  i => hasWit  (nthc (.var 0) (numeralM i))
  | .witF i => hasWitF (nthc (.var 0) (numeralM i))

/-- **La condición ENMENDADA**: la cascada de guardas anidada a la derecha, y al final la
    condición estructural `C` de siempre. `guardedCond [] C = C` es el caso de los 14 tags
    que la enmienda no toca. -/
def guardedCond : List GuardSlot → Formula → Formula
  | [],      C => C
  | g :: gs, C => Formula.and g.toF (guardedCond gs C)

/-! ### §2.1 · Los SIETE, verificados con `rfl` contra `Minimal/Axioms.lean`

No es una descripción de la forma: es la forma, comprobada. El `rfl` casa el orden de las
guardas, el índice de cada casilla y el anidamiento — si `Minimal/Axioms.lean` cambiara
cualquiera de las tres, estos siete dejarían de compilar. -/

example : ∃ C, ax_lineWF_q1 =
    forall_ (Formula.impl (tagF 9) (lwfVar ⇔ Formula.and (lencF 4)
      (guardedCond [.witF 2, .wit 3] C))) := ⟨_, rfl⟩

example : ∃ C, ax_lineWF_q2 =
    forall_ (Formula.impl (tagF 10) (lwfVar ⇔ Formula.and (lencF 4)
      (guardedCond [.witF 2, .wit 3] C))) := ⟨_, rfl⟩

example : ∃ C, ax_lineWF_q3 =
    forall_ (Formula.impl (tagF 11) (lwfVar ⇔ Formula.and (lencF 4)
      (guardedCond [.witF 3] C))) := ⟨_, rfl⟩

example : ∃ C, ax_lineWF_leibniz =
    forall_ (Formula.impl (tagF 13) (lwfVar ⇔ Formula.and (lencF 5)
      (guardedCond [.witF 2, .wit 3, .wit 4] C))) := ⟨_, rfl⟩

example : ∃ C, ax_lineWF_ind =
    forall_ (Formula.impl (tagF 18) (lwfVar ⇔ Formula.and (lencF 3)
      (guardedCond [.witF 2] C))) := ⟨_, rfl⟩

example : ∃ C, ax_lineWF_qconf =
    forall_ (Formula.impl (tagF 19) (lwfVar ⇔ Formula.and (lencF 4)
      (guardedCond [.witF 2] C))) := ⟨_, rfl⟩

example : ∃ C, ax_lineWF_listInd =
    forall_ (Formula.impl (tagF 20) (lwfVar ⇔ Formula.and (lencF 3)
      (guardedCond [.witF 2] C))) := ⟨_, rfl⟩

/-- **El recuento de ADR-020, comprobado**: 7 `hasWitF` + 4 `hasWit` = 11 conjuntos nuevos. -/
def slotsOfTags : List (List GuardSlot) :=
  [ [.witF 2, .wit 3], [.witF 2, .wit 3], [.witF 3]
  , [.witF 2, .wit 3, .wit 4], [.witF 2], [.witF 2], [.witF 2] ]

example : (slotsOfTags.map List.length).sum = 11 := rfl
example : ((slotsOfTags.flatten).filter (fun g => match g with | .witF _ => true | _ => false)).length
    = 7 := rfl
example : ((slotsOfTags.flatten).filter (fun g => match g with | .wit _ => true | _ => false)).length
    = 4 := rfl

/-! ## §3 · EL CHASIS ABSORBE LA CASCADA ENTERA -/

/-- El reflector `hcond` que pide `pcc_lineWF_tracked_of_schema`, abreviado. -/
abbrev Hcond (n : Nat) (t : Term) (C : Formula) : Prop :=
  Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒
    (substFormula 0 t C ⇒ provFromCode (condD C t))))

/-- ⭐ **El chasis absorbe la cascada ENTERA**, por inducción sobre la lista de casillas.

    Es lo que convierte la deuda de ADR-020 en **dos** lemas genéricos: cada tag aporta su
    lista, y el índice de casilla es un parámetro. No hay que reflejar ninguna conjunción:
    `substfc` distribuye sobre `andc` y §1 la recompone paso a paso. -/
theorem hcond_absorbe_cascade (t : Term) (n : Nat) (C : Formula)
    (hC : Hcond n t C) :
    ∀ gs : List GuardSlot, (∀ g ∈ gs, Hcond n t g.toF) → Hcond n t (guardedCond gs C)
  | [],      _ => hC
  | g :: gs, h =>
      hcond_absorbe_extra g.toF (guardedCond gs C) t n
        (h g (List.Mem.head _))
        (hcond_absorbe_cascade t n C hC gs (fun q hq => h q (List.Mem.tail _ hq)))

/-! ## §4 · LAS DOS OBLIGACIONES QUE QUEDAN

Idioma de `Meta/Sigma1BoundedPrf.lean`: la deuda **se enuncia**, no se postula. Ninguna de
las dos es un `axiom`; son `abbrev`s de `Prop` que un consumidor tiene que probar. -/

/-- **Obligación T** — el reflector Σ₁ de `hasWit` sobre la casilla `i` de la línea `t`. -/
abbrev DEUDA_hGuardT (i n : Nat) (t : Term) : Prop := Hcond n t (GuardSlot.wit i).toF

/-- **Obligación F** — el reflector Σ₁ de `hasWitF` sobre la casilla `i` de la línea `t`. -/
abbrev DEUDA_hGuardF (i n : Nat) (t : Term) : Prop := Hcond n t (GuardSlot.witF i).toF

/-- ⭐ **`hGuard` CERRADA A PARTIR DE LAS DOS DEUDAS, y para los siete tags a la vez.**

    Esto es *todo* lo que ADR-020 dejó abierto en el chasis: probadas `DEUDA_hGuardT` y
    `DEUDA_hGuardF` genéricas en la casilla, cualquier tag —con la lista que sea— recupera su
    `hcond` sin una línea más. -/
theorem hGuard_of_deudas (t : Term) (n : Nat) (C : Formula) (hC : Hcond n t C)
    (hT : ∀ i, DEUDA_hGuardT i n t) (hF : ∀ i, DEUDA_hGuardF i n t)
    (gs : List GuardSlot) :
    Hcond n t (guardedCond gs C) :=
  hcond_absorbe_cascade t n C hC gs
    (fun g _ => by cases g with | wit i => exact hT i | witF i => exact hF i)

end ROBINSON_PlusPlus.Meta.LineWFGuardPrf

export ROBINSON_PlusPlus.Meta.LineWFGuardPrf (
  hcond_absorbe_extra GuardSlot guardedCond Hcond
  hcond_absorbe_cascade DEUDA_hGuardT DEUDA_hGuardF hGuard_of_deudas
)

#print axioms ROBINSON_PlusPlus.Meta.LineWFGuardPrf.hcond_absorbe_extra
#print axioms ROBINSON_PlusPlus.Meta.LineWFGuardPrf.hcond_absorbe_cascade
#print axioms ROBINSON_PlusPlus.Meta.LineWFGuardPrf.hGuard_of_deudas
