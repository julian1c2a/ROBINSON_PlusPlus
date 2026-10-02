/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ChainDecode
import ROBINSON_PlusPlus.Meta.OmegaReflect

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`. Los nombres de esa capa que cite el texto de abajo
> (`NegVerifier`, `formCode_ne`, `termCode_ne`, `OmegaConsistent`) **ya no existen**: lo que se lea sobre ellos es REGISTRO, no estado.
> Tampoco las dos deudas de §4 (`DEUDA_chainNeg`, `DEUDA_inNeg`) ni `negVerifier_of_deudas`, que las juntaba.
> Lo que queda en el módulo no depende de `⊢`.
-/

/-!
# MÓDULO E · SOLIDEZ ESTRUCTURAL DEL VERIFICADOR

`PLAN-NEGVERIFIER.md` §8 llamaba a este módulo **«el corazón»** y le ponía **riesgo ALTO** y
300‑500 líneas, con una **acción obligatoria**: sondear antes de codificar, por si el verificador
objeto aceptara cadenas basura que «prueban» `⌜φ⌝` sin `Prf φ`.

## ⭐⭐ El sondeo se hizo (2026‑09‑10h) y el módulo sale en DIEZ líneas

`sondeos/NegVerifierModE.lean`, cinco mediciones, todas verdes entonces (hoy es registro y no
compila: cita lo retirado con ADR‑115). Dos resultados:

1. ✅ **No hay bug de solidez.**
2. ⭐⭐ **Y el corazón no hacía falta construirlo**, porque el decisor que este módulo necesita
   **NO tiene que ser el verificador OBJETO**: basta el **decodificador META**, y entonces la
   solidez **ya estaba probada** desde `Meta/ChainDecode.lean`.

🔑 **La pieza que lo hace gratis** es `decodeForm_inj` (`Meta/CodeDecode.lean`):

    decodeForm c = some φ  →  c = formCodeM φ

es decir, **el decodificador es una SECCIÓN**: «si decodifica, el código era real». Y eso **ES** la
*realidad hereditaria* que §8 pedía demostrar caso por caso —«si la conclusión es un `formCode`
real, la ecuación estructural fuerza a que los args sean `formCode` reales»—, ya empaquetada.

## ⛔ Dónde está el riesgo de verdad (y el plan lo tenía al revés)

Este módulo cubre la mitad **(a)**: *el decisor acepta ⟹ `Prf φ`*. `NegVerifier` necesitaba también
la mitad **(b)**, la **completitud negativa**: *el decisor rechaza ⟹ la teoría REFUTA `chainOk`*.
Y ahí sí hay discrepancia **medida**: los esquemas objeto cuantifican sobre códigos **cualesquiera**
y aceptan cadenas que el decodificador rechaza —

    axioms ⊢ lineWF ⟨implc basura (implc basura basura), 0̄, basura, basura⟩
    decodeForm (implc basura (implc basura basura)) = none

⇒ El par **(C, D)** era lo que había que rediseñar, no éste; se rediseñó (ADR‑022) y se construyó en
`Meta/ChainNegPrf.lean`, cuyo resultado, sobre `⊢`, se retiró con ADR‑115. Detalle en
`sondeos/NegVerifierModE.lean`.

**Footprint**: el de `decodeChain_prf`.
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertSeq
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.Representability2
open ROBINSON_PlusPlus.Meta.CodeDecode
open ROBINSON_PlusPlus.Meta.ChainDecode
open ROBINSON_PlusPlus.Meta.OmegaReflect

namespace ROBINSON_PlusPlus.Meta.VerifierSound

/-! ## §1 · EL DECISOR META

⚠️ **No es el verificador objeto, y ésa es toda la gracia.** El objeto acepta más (§0); el META
acepta **exactamente** lo que es el código de una derivación real, porque su decodificador es una
sección. -/

/-- El decisor META de cadenas: ¿es `objList l` el código de una derivación decodificable? -/
def chainOkDec (l : List Term) : Bool := (decodeChain (objList l)).isSome

/-- Las conclusiones que el decisor extrae, cuando acepta. -/
noncomputable def conclsDec (l : List Term) : Option (List Formula) :=
  (decodeChain (objList l)).bind checkProof

/-! ## §2 · 🏁 LA SOLIDEZ ESTRUCTURAL -/

/-- 🏁 **MÓDULO E.** Si el decisor META acepta la cadena y `φ` está entre sus conclusiones,
    entonces `φ` es **demostrable**. Es `decodeChain_prf`: no hay nada que probar aquí, y ése es
    exactamente el hallazgo del sondeo. -/
theorem verifier_sound {l : List Term} {rs : List Rule} {φ : Formula}
    (h : decodeChain (objList l) = some rs)
    (hmem : ∀ L, checkProof rs = some L → φ ∈ L) : Prf φ :=
  decodeChain_prf h hmem

/-- La misma, leída sobre `conclsDec`. -/
theorem verifier_sound_concls {l : List Term} {L : List Formula} {φ : Formula}
    (h : conclsDec l = some L) (hmem : φ ∈ L) : Prf φ := by
  unfold conclsDec at h
  rcases hd : decodeChain (objList l) with _ | rs
  · rw [hd] at h; simp at h
  · rw [hd] at h; simp only [Option.bind] at h
    exact verifier_sound hd (fun L' hL' => by rw [h] at hL'; injection hL' with hL'; exact hL' ▸ hmem)

/-! ## §3 · LA FORMA DE CONSUMO — la CONTRAPOSITIVA

Era lo que pedía el ensamblaje (`negVerifier_of_deudas`, aquí, y `negVerifier_proved`, en
`Meta/ChainNegPrf.lean`): de `¬ Prf φ` sale que el decisor **no puede** aceptar una cadena que
concluya `φ`. ⇒ en aquel `by_cases`, **la rama «aceptada» era imposible**, y todo el trabajo caía
en la otra: refutar en la teoría (módulos C+D). 🗑️ El ensamblaje era sobre `⊢` y se retiró con
ADR‑115: las dos contrapositivas de abajo siguen probadas, pero hoy **no tienen consumidor**. -/

/-- 🏁 **La contrapositiva.** `φ` indemostrable ⟹ ninguna cadena estándar la concluye para el
    decisor META.

    ⚠️ El `∧` va como **`And` explícito**: en este proyecto `∧` en un enunciado se parsea como
    `Formula.and` (trampa §12 de las notaciones). -/
theorem not_decodes_of_not_prf {φ : Formula} (hnp : ¬ Prf φ) (l : List Term) :
    ¬ ∃ rs, And (decodeChain (objList l) = some rs)
      (∀ L, checkProof rs = some L → φ ∈ L) :=
  fun ⟨_, h, hmem⟩ => hnp (verifier_sound h hmem)

/-- Y sobre `conclsDec`, la forma en que se comparaba con `runFn` (en `DEUDA_inNeg` y
    `negVerifier_of_deudas`, sobre `⊢`, retirados con ADR‑115). -/
theorem not_mem_conclsDec_of_not_prf {φ : Formula} (hnp : ¬ Prf φ)
    (l : List Term) (L : List Formula) (h : conclsDec l = some L) : φ ∉ L :=
  fun hmem => hnp (verifier_sound_concls h hmem)

/-! ## §4 · 🗑️ (Aquí se enunciaban `DEUDA_chainNeg`/`DEUDA_inNeg` y `negVerifier_of_deudas`, sobre `⊢`;
retirados con ADR‑115. La mitad `⊬¬G` no tiene hoy formulación sobre `Prf`: ADR‑115 §7.) -/

end ROBINSON_PlusPlus.Meta.VerifierSound

/-! ## `export` — por CONSUMO

Sin consumidor tras ADR‑115, salvo `chainOkDec` (lo usa `dispatcher`, en `Meta/ChainNegPrf.lean`,
que tampoco tiene consumidor). El previsto era el módulo F (`NegVerifierPrf`, que no llegó a
existir), para descargar las dos deudas de §4, retiradas con `⊢`. -/
export ROBINSON_PlusPlus.Meta.VerifierSound (
  chainOkDec
  conclsDec
  verifier_sound
  verifier_sound_concls
  not_decodes_of_not_prf
  not_mem_conclsDec_of_not_prf
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.VerifierSound.verifier_sound
