/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ChainDecode
import ROBINSON_PlusPlus.Meta.OmegaReflect

/-!
# MÓDULO E · SOLIDEZ ESTRUCTURAL DEL VERIFICADOR

`PLAN-NEGVERIFIER.md` §8 llamaba a este módulo **«el corazón»** y le ponía **riesgo ALTO** y
300‑500 líneas, con una **acción obligatoria**: sondear antes de codificar, por si el verificador
objeto aceptara cadenas basura que «prueban» `⌜φ⌝` sin `Prf φ`.

## ⭐⭐ El sondeo se hizo (2026‑09‑10h) y el módulo sale en DIEZ líneas

`sondeos/NegVerifierModE.lean`, cinco mediciones, todas verdes. Dos resultados:

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

Este módulo cubre la mitad **(a)**: *el decisor acepta ⟹ `Prf φ`*. `NegVerifier` necesita también
la mitad **(b)**, la **completitud negativa**: *el decisor rechaza ⟹ la teoría REFUTA `chainOk`*.
Y ahí sí hay discrepancia **medida**: los esquemas objeto cuantifican sobre códigos **cualesquiera**
y aceptan cadenas que el decodificador rechaza —

    axioms ⊢ lineWF ⟨implc basura (implc basura basura), 0̄, basura, basura⟩
    decodeForm (implc basura (implc basura basura)) = none

⇒ El par **(C, D)** es lo que hay que rediseñar, no éste. Detalle en `sondeos/NegVerifierModE.lean`.

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

Es lo que el ensamblaje (módulo F) pide: de `¬ Prf φ` sale que el decisor **no puede** aceptar una
cadena que concluya `φ`. ⇒ en el `by_cases` de F, **la rama «aceptada» es imposible**, y todo el
trabajo que queda cae en la otra: refutar en la teoría (módulos C+D). -/

/-- 🏁 **La contrapositiva.** `φ` indemostrable ⟹ ninguna cadena estándar la concluye para el
    decisor META.

    ⚠️ El `∧` va como **`And` explícito**: en este proyecto `∧` en un enunciado se parsea como
    `Formula.and` (trampa §12 de las notaciones). -/
theorem not_decodes_of_not_prf {φ : Formula} (hnp : ¬ Prf φ) (l : List Term) :
    ¬ ∃ rs, And (decodeChain (objList l) = some rs)
      (∀ L, checkProof rs = some L → φ ∈ L) :=
  fun ⟨_, h, hmem⟩ => hnp (verifier_sound h hmem)

/-- Y sobre `conclsDec`, que es la forma en que `runFn` se comparará. -/
theorem not_mem_conclsDec_of_not_prf {φ : Formula} (hnp : ¬ Prf φ)
    (l : List Term) (L : List Formula) (h : conclsDec l = some L) : φ ∉ L :=
  fun hmem => hnp (verifier_sound_concls h hmem)

/-! ## §4 · LO QUE FALTA, **ENUNCIADO** (no postulado)

La otra mitad de `NegVerifier`: la **completitud negativa**. Se enuncia aquí para que el frente
tenga su obligación con nombre y firma, como manda el idioma del proyecto (§2 de
`Meta/D3ChainDotPrf.lean`: *la deuda se enuncia, no se postula*).

⚠️ **Y no se puede consumir todavía**: depende del ADR de `StdChain` (ver §0 y
`sondeos/NegVerifierModE.lean` §4). Con `StdChain = IsCodeShaped` la clase **no separa**
(`cons nil nil ≐ numeralM 2` es provable) y la refutación exigiría evaluar Cantor. -/

/-- **La mitad (b) de `NegVerifier`**: si el decisor META rechaza, la teoría REFUTA la cadena. -/
abbrev DEUDA_chainNeg : Prop :=
  ∀ l : List Term, StdChain l → chainOkDec l = false →
    axioms ⊢ neg (chainOk nil (objList l))

/-- **La mitad (b′)**: si el decisor acepta pero `φ` **no** está entre las conclusiones, la teoría
    refuta la pertenencia. -/
abbrev DEUDA_inNeg : Prop :=
  ∀ (φ : Formula) (l : List Term) (L : List Formula), StdChain l →
    conclsDec l = some L → φ ∉ L →
      axioms ⊢ neg (In (formCode φ) (runFn nil (objList l)))

/-- ⭐ **`NegVerifier` DESDE LAS DOS DEUDAS Y NADA MÁS.** La rama «aceptada y concluye `φ`» la
    cierra §3 —es **imposible**—, así que el ensamblaje sólo tiene que repartir entre las otras
    dos. Es el análogo de `d3_prf_of_halves` para este frente. -/
theorem negVerifier_of_deudas (hchain : DEUDA_chainNeg) (hin : DEUDA_inNeg) : NegVerifier := by
  intro φ hnp l hl
  rcases hdec : chainOkDec l with _ | _
  · -- el decisor RECHAZA ⇒ se refuta `chainOk`, y con él la conjunción
    exact FOL.MetaRules.imp_intro (fun hv =>
      FOL.MetaRules.mp (hchain l hl hdec) (Minimal.Axioms.and_elim_left hv))
  · -- el decisor ACEPTA ⇒ `φ` **no** puede estar entre las conclusiones (§3) ⇒ se refuta el `In`
    have hsome : (decodeChain (objList l)).isSome = true := hdec
    rcases hd : decodeChain (objList l) with _ | rs
    · rw [hd] at hsome; simp at hsome
    · rcases hc : checkProof rs with _ | L
      · -- no puede pasar: `decodeChain` acepta ⇒ `checkProof` acepta
        obtain ⟨L', hL'⟩ := decodeChain_checkProof hd
        rw [hc] at hL'; simp at hL'
      · have hcd : conclsDec l = some L := by
          unfold conclsDec; rw [hd]; simpa only [Option.bind] using hc
        have hnm : φ ∉ L := not_mem_conclsDec_of_not_prf hnp l L hcd
        exact FOL.MetaRules.imp_intro (fun hv =>
          FOL.MetaRules.mp (hin φ l L hl hcd hnm) (Minimal.Axioms.and_elim_right hv))

end ROBINSON_PlusPlus.Meta.VerifierSound

/-! ## `export` — por CONSUMO

Consumidor previsto: el módulo F (`NegVerifierPrf`), que sólo tiene que descargar las dos deudas
de §4. -/
export ROBINSON_PlusPlus.Meta.VerifierSound (
  chainOkDec conclsDec
  verifier_sound verifier_sound_concls
  not_decodes_of_not_prf not_mem_conclsDec_of_not_prf
  DEUDA_chainNeg DEUDA_inNeg negVerifier_of_deudas
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.VerifierSound.verifier_sound
#print axioms ROBINSON_PlusPlus.Meta.VerifierSound.negVerifier_of_deudas
