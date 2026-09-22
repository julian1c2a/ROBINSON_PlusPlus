import ROBINSON_PlusPlus

/-!
# ⛔⛔ SONDEO · **ℕ NO ES MODELO DE `Prf`** — y el frente del modelo cambia de forma

**Fecha**: 2026‑09‑22. Se midió **antes** de escribir la capa de listas, y menos mal.

## La pregunta

La capa aritmética del modelo está cerrada (**25 de los 34**, ADR‑087). Antes de interpretar
`cons`/`In`/`concat` había que comprobar una cosa: **¿el dominio ℕ tiene BASURA?** Es decir,
¿hay números que no sean ni `nil` ni un `cons`?

## El dato

`ax_L0_cons_def` **obliga** a interpretar `cons a b` como `pair a (σb) = cantor_func a (b+1)`, y
`nil` es `zero = 0`. Con la interpretación estándar de `+`, `*` y `div2` —que los otros axiomas
core también fuerzan— eso es exactamente `consN a b = triN (a + (b+1)) + (b+1)`, que es la
función que **ya está en producción** (`Meta/CodeNumeralPrf.lean:65`).

⇒ La imagen de `cons` es `{cantor(x,y) : y ≥ 1}`, y **se deja fuera los números triangulares**
`T(1)=1`, `T(2)=3`, `T(3)=6`, … **El 1 no es ni `nil` ni un `cons`**, y abajo está compilado.

## ⛔⛔ La consecuencia, y es grande

`Prf` tiene el constructor `listInd (A) : Prf (listInductionFormula A)`, y

    listInductionFormula Φ  =  Φ[nil] ⇒ ((∀h∀t. Φ[t] ⇒ Φ[cons h t]) ⇒ ∀L. Φ[L])

Tómese **Φ := «es `nil` o es un `cons`»**, que es una fórmula del lenguaje. Su base vale, su paso
vale, y su conclusión **es falsa en ℕ** (falla en `1`). ⇒ `listInductionFormula Φ` es **FALSA en
el modelo estándar**, y `Prf` la demuestra.

## 🔑 Lo que esto significa — y lo que NO

* **`Prf` no es sólido respecto del modelo estándar de la aritmética.** ⇒ la ruta «modelo en ℕ ⇒
  `¬ Prf ⊥` ⇒ `ConsistentH`» **no funciona tal cual**.
* ⚠️ **NO significa que `Prf` sea inconsistente.** Significa que **ℕ, con esta interpretación, no
  es uno de sus modelos**. Un cálculo puede ser consistente y no tener a ℕ por modelo.
* ⚠️ Y **no es un fallo de la aritmetización**: `listInd` está ahí para razonar sobre **códigos**,
  y sobre códigos la inducción es legítima. Lo que falla es que el lenguaje **no distingue** los
  códigos del resto de ℕ: el esquema cuantifica sobre **todo** el dominio.

🔑 **Un esquema de inducción sobre una clase que el lenguaje no sabe separar, cuantifica sobre
todo el dominio — y entonces habla de lo que no debería.**

## ⬜ Las salidas, y ninguna es gratis

1. **Dominio distinto**: tomar `D` = los códigos bien formados. ⛔ Pero `D` tendría que ser
   cerrado bajo `+` y `*`, y no lo es.
2. **Relativizar `listInd`**: que el esquema lleve una guarda `EsLista L ⇒ …`. Cambia `Prf`, y con
   él todo lo que se apoya en `listInd` — hay que medir qué.
3. **Renunciar al modelo estándar** y buscar la consistencia por otra vía (p. ej. un modelo
   sintáctico/término, o relativa a un fragmento).
4. **Comprobar si `listInd` se usa de verdad**: si toda instancia consumida en el árbol lleva ya
   una guarda de buena formación, (2) es barata.

⇒ **(4) primero**: es una medición, y las otras tres son decisiones que dependen de ella.

## Cómo re‑ejecutarlo

    lake env lean sondeos/ModeloBasura.lean      # desde la raíz de RPP
-/

open ROBINSON_PlusPlus.Meta.CodeNumeralPrf

namespace ModeloBasura

/-- La interpretación que `ax_L0_cons_def` fuerza, y que ya estaba en producción. -/
example (h t : Nat) : consN h t = triN (h + (t + 1)) + (t + 1) := rfl

/-- ⛔⛔ **EL 1 NO ES UN `cons`.** -/
theorem uno_no_es_cons : ∀ h t : Nat, consN h t ≠ 1 := by
  intro h t hc
  simp only [consN] at hc
  have : triN (h + (t + 1)) ≥ 1 := by
    cases hs : h + (t + 1) with
    | zero => omega
    | succ n => simp only [triN]; omega
  omega

/-- «Es `nil` o es un `cons`» — la Φ del contraejemplo.
    ⚠️ `Or` explícito: con `Minimal.Axioms` en contexto, `∨` se parsea como `Formula.or`. -/
def EsLista (n : Nat) : Prop := Or (n = 0) (∃ h t, consN h t = n)

theorem base : EsLista 0 := Or.inl rfl

theorem paso : ∀ h t, EsLista t → EsLista (consN h t) :=
  fun h t _ => Or.inr ⟨h, t, rfl⟩

/-- ⛔⛔ **Y sin embargo NO vale para todo el dominio.** Base + paso + esto es exactamente la
    premisa del esquema de inducción de listas y la negación de su conclusión. -/
theorem falla : ¬ EsLista 1 := by
  intro hc
  rcases hc with h0 | ⟨h, t, ht⟩
  · exact absurd h0 (by decide)
  · exact uno_no_es_cons h t ht

end ModeloBasura

#print axioms ModeloBasura.uno_no_es_cons
#print axioms ModeloBasura.base
#print axioms ModeloBasura.paso
#print axioms ModeloBasura.falla
