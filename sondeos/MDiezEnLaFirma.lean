import ROBINSON_PlusPlus

-- ══════════════════════════════════════════════════════════════════════════
-- SONDEO (5b·1) — ¿puede M-10 salir del script y entrar en la FIRMA?
--
-- La tesis de `Sugerencias.md`: declarar una clase `EsREnumerable P` (verificador ·
-- decidible · adecuado), enunciar Gödel I sobre `[EsREnumerable P]`, y que entonces el
-- TIPO impida enunciarlo sobre `⊢` — porque `axioms ⊢` es sintácticamente COMPLETO y
-- por tanto NO r.e. (M-10, ADR-024).
--
-- ⛔ EL CONTROL ADVERSARIAL QUE PIDIÓ EL PROPIETARIO: «que la instancia para `⊢` no
-- compile, y por qué. Si compila, la idea está muerta.»
--
-- 🏁 VEREDICTO: **compila**, y §2 dice exactamente por qué — la clase no caracteriza
-- «ser r.e.», caracteriza «factorizar por la codificación», que es una trivialidad.
--
-- ⚠️ Trampa §12 en vivo: aquí `∧` es `Formula.and` y `¬` es `neg`. Se usan `And` y `Not`.
-- ══════════════════════════════════════════════════════════════════════════

namespace ProbeM10

/-- La clase tal como `Sugerencias.md` la propone: `P` es r.e. si hay un verificador
`Bool`-valuado y una equivalencia de adecuación. -/
class EsREnumerable (P : Formula → Prop) (code : Formula → Nat) where
  verifier : Nat → Nat → Bool
  adecuado : ∀ f, Iff (P f) (∃ c, verifier c (code f) = true)

-- ══════════════════════════════════════════════════════════════════════════
-- §1 · ⛔⛔ La instancia CLÁSICA: existe siempre que `P` factorice por el código
-- ══════════════════════════════════════════════════════════════════════════

/-- El verificador clásico: pregunta directamente si el código viene de algo que cumple `P`.
⚠️ Es `noncomputable` —lo rellena `Classical.propDecidable`—, y **Lean lo acepta**: el campo
`verifier` es **DATO**, y Lean permite construir dato clásicamente. El sistema de tipos **no
puede expresar «esta función `Bool`-valuada es COMPUTABLE»**. Ahí muere la idea. -/
noncomputable def verificadorClasico (P : Formula → Prop) (code : Formula → Nat) :
    Nat → Nat → Bool :=
  fun _ n => @decide (∃ g, And (code g = n) (P g)) (Classical.propDecidable _)

/-- ⛔⛔⛔ **SI ESTO COMPILA, LA IDEA ESTÁ MUERTA.** Y compila.

La única hipótesis es que `P` **factorice por la codificación** —si dos fórmulas tienen el mismo
código, `P` no las distingue—, que es más débil que la inyectividad del código y que **toda**
`P` razonable cumple. Ni una palabra sobre ser r.e. -/
@[reducible] noncomputable def instanciaClasica (P : Formula → Prop) (code : Formula → Nat)
    (hfac : ∀ f g, code f = code g → P g → P f) : EsREnumerable P code where
  verifier := verificadorClasico P code
  adecuado := by
    intro f
    constructor
    · intro hp
      refine ⟨0, ?_⟩
      show @decide (∃ g, And (code g = code f) (P g)) (Classical.propDecidable _) = true
      exact @decide_eq_true _ (Classical.propDecidable _) ⟨f, rfl, hp⟩
    · rintro ⟨_, hc⟩
      have h : ∃ g, And (code g = code f) (P g) :=
        @of_decide_eq_true _ (Classical.propDecidable _) hc
      obtain ⟨g, hg, hpg⟩ := h
      exact hfac f g hg.symm hpg

-- ══════════════════════════════════════════════════════════════════════════
-- §2 · ⭐⭐ LA CARACTERIZACIÓN EXACTA, que es el hallazgo de verdad
-- ══════════════════════════════════════════════════════════════════════════

/-- El recíproco: **la adecuación IMPLICA la factorización.** El verificador sólo recibe
`code f`, luego no puede distinguir dos fórmulas con el mismo código. -/
theorem factoriza_de_instancia (P : Formula → Prop) (code : Formula → Nat)
    [inst : EsREnumerable P code] : ∀ f g, code f = code g → P g → P f := by
  intro f g h hpg
  have h1 := (inst.adecuado g).mp hpg
  rw [← h] at h1
  exact (inst.adecuado f).mpr h1

/-- 🏁🏁 **EL VEREDICTO, y es exacto**: `EsREnumerable P code` **es equivalente** a que `P`
factorice por la codificación. No dice nada sobre computabilidad, ni sobre enumerabilidad, ni
sobre `P`. Es una propiedad de la CODIFICACIÓN, no del CÁLCULO.
⇒ poner `[EsREnumerable P]` en la firma de Gödel I **no excluye ningún `P`** que el proyecto
pudiera querer excluir. La hipótesis es **decorativa**. -/
theorem caracterizacion_exacta (P : Formula → Prop) (code : Formula → Nat) :
    Iff (Nonempty (EsREnumerable P code)) (∀ f g, code f = code g → P g → P f) := by
  constructor
  · rintro ⟨inst⟩
    exact factoriza_de_instancia P code (inst := inst)
  · intro hfac
    exact ⟨instanciaClasica P code hfac⟩

-- ══════════════════════════════════════════════════════════════════════════
-- §3 · Y el caso concreto que M-10 prohíbe: `⊢`
-- ══════════════════════════════════════════════════════════════════════════

open ROBINSON_PlusPlus.Minimal.Axioms in
/-- ⛔⛔ **La instancia para `⊢` COMPILA**, en cuanto la codificación sea inyectiva — y si no lo
fuera, la gödelización entera estaría rota. Es exactamente el caso que M-10 prohíbe y que la
firma debía impedir. -/
@[reducible] noncomputable def instanciaParaDerives (code : Formula → Nat)
    (hinj : ∀ f g, code f = code g → f = g) :
    EsREnumerable (fun f => Derives axioms f) code :=
  instanciaClasica _ code (fun f g h hpg => hinj g f h.symm ▸ hpg)

/-- ⭐ Y para que no quede duda de que el problema **no** es la inyectividad: basta la
factorización, y `Derives axioms` la cumple **trivialmente** en cuanto el código lo haga. Este
enunciado es el mismo control sin ninguna hipótesis sobre el cálculo. -/
theorem derives_factoriza_si_el_codigo_inyecta (code : Formula → Nat)
    (hinj : ∀ f g, code f = code g → f = g) :
    ∀ f g, code f = code g → Derives axioms g → Derives axioms f :=
  fun f g h hpg => hinj g f h.symm ▸ hpg

end ProbeM10

#print axioms ProbeM10.instanciaClasica
#print axioms ProbeM10.factoriza_de_instancia
#print axioms ProbeM10.caracterizacion_exacta
#print axioms ProbeM10.instanciaParaDerives
