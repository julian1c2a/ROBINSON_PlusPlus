/-
⛔ SONDEO NEGATIVO (2026-08-23) — `canon_ne` es FALSO y **reintroduciría la inconsistencia**.

`PLAN-NEGVERIFIER.md` §6 pide, como paso **1.1** y base de los módulos **C** y **D**:

    canon_ne {a b} (ha : IsCanon a) (hb : IsCanon b) (h : a ≠ b) : axioms |- neg (a =eq b)

«Términos canónicos DISTINTOS son provablemente distintos», ~80 líneas, riesgo BAJO.

## El plan es del 2026-07-14 — ANTERIOR al descubrimiento de la inconsistencia (2026-08-18)

Y arrastra **exactamente el mismo error de categoría**: confundir distinción **sintáctica** (en Lean)
con distinción **provable** (en la teoría objeto), en una teoría donde los árboles `cons` **SON**
números.

La clase de testigos —hoy `IsCodeShaped`— incluye a la vez `numeralM n` y `cons h t`. Y:

    cons nil nil  =  pair 0 (σ0)  =  div2 (cantor_poly 0 1)  =  div2 4  =  2  =  numeralM 2

Son **distintos como términos de Lean** (cabezas `::` y `σ`) y **provablemente iguales en la teoría**
(`prf_cons_eval`, net-0). Con `canon_ne` sale `⊥` — verificado abajo, en el compilador.

## ⇒ Consecuencia para el frente `NegVerifier`

**El paso 1.1 del plan no se puede hacer**, y con él caen los casos 3 y 4 del módulo C, que es donde
`canon_ne` se usaba. Los casos 1 y 2 (refutar por `ax_lineWF_cons` / `ax_lineWF_inv`) **no dependen
de él** y siguen en pie.

**La salida natural es la misma que la de ADR-012: pasar a NUMERALES.** La distinción entre
`numeralM m` y `numeralM n` con `m ≠ n` **sí** es provable (`prf_succ_inj` / `prf_succ_ne_zero`), y
`prf_formCode_numeral` puentea las dos representaciones. El sustituto sería del tipo

    codeNat_ne : codeNat φ ≠ codeNat ψ -> axioms |- neg (numeral (codeNat φ) =eq numeral (codeNat ψ))

que además exige probar la **inyectividad de `codeNat`** (plausible: se construye con `consN`, que es
el emparejamiento de Cantor). **Sin medir.**
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.OmegaReflect
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf

namespace CanonNeDev

/-- Los dos términos son AMBOS `IsCodeShaped`. -/
example : IsCodeShaped (cons nil nil) := IsCodeShaped.cons IsCodeShaped.nil IsCodeShaped.nil
example : IsCodeShaped (numeralM 2) := IsCodeShaped.numeral 2

/-- Y son DISTINTOS como términos de Lean (cabezas `::` y `σ`). -/
theorem distintos : cons nil nil ≠ numeralM 2 := by decide

/-- ⚠️ **PERO SON PROVABLEMENTE IGUALES.** `consN 0 0 = 2`. -/
theorem iguales_en_la_teoria : Prf (cons nil nil =eq numeralM 2) := by
  have h := prf_cons_eval 0 0
  simpa only [numeral, numeralM, nil, consN, triN] using h

/-- ⇒ **`canon_ne` reintroduciría la INCONSISTENCIA.** Si existiera, de él y de la igualdad
    provable sale `⊥`. Se enuncia como hipótesis para que el compilador lo verifique. -/
theorem canon_ne_es_INCONSISTENTE
    (canon_ne : ∀ {a b : Term}, IsCodeShaped a → IsCodeShaped b → a ≠ b → Prf (neg (a =eq b))) :
    Prf Formula.bottom :=
  prf_mp (canon_ne (IsCodeShaped.cons IsCodeShaped.nil IsCodeShaped.nil)
    (IsCodeShaped.numeral 2) distintos) iguales_en_la_teoria

end CanonNeDev

#print axioms CanonNeDev.iguales_en_la_teoria
#print axioms CanonNeDev.canon_ne_es_INCONSISTENTE
