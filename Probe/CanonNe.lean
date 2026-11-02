/- ¿Sigue siendo cierto `canon_ne` (PLAN-NEGVERIFIER §6, paso 1.1)?

   El plan es del 2026-07-14, ANTERIOR al descubrimiento de la inconsistencia. Pide:

     canon_ne {a b} (ha : IsCanon a) (hb : IsCanon b) (h : a ≠ b) : axioms ⊢ neg (a =eq b)

   con la clase de testigos, hoy `IsCodeShaped`. Pero esa clase incluye a la vez `numeralM n`
   y `cons h t`... y `cons` ES un número. -/
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
