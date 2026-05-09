# Thoughts — ProjectName

**Last updated:** 2026-04-20 00:00
**Author**: Julián Calderón Almendros

> This is an informal design journal. Record ideas, alternatives considered,
> open questions, and future directions here. Not normative — purely exploratory.
> Useful for AI context on "why" decisions were made.

---

## Design Philosophy

[Record the core design philosophy of the project here. Examples:

- Why no Mathlib dependency?
- What mathematical system is being formalized?
- What pedagogical or research goals does this serve?]

---

## Ideas and Alternatives

## ¿Es necesario el axioma 22?

El verdadero axioma 22 es $a < b ⟹ σ(a) ≤ b$.

(A) Hipótesis: $a < b$
(B) Tricotomía (Ax): $a < b ∨ a = b ∨ b < a$
(C) $σ(a) < b ∨ σ(a) = b ∨ b < σ(a)$ Axioma de Tricotomía reescrito con $σ(a)$
(D) $σ(a) ≤ b ∨ b < σ(a)$ Por la Definición de ≤

De (A) y (D) demostramos que si $¬ (b < σ(a))$ entonces $σ(a) ≤ b$, lo que es exactamente el axioma 22.

Vamos a suponer que (WH) $b < σ(a)$ y nuestra hipótesis inicial (IA) $a < b$.

(IA) $a < b ⟺ ∃ c, a + σ(c) = b$ Por la Definición de <
(B) $a + σ(c) = b$ Por (A)
(C) $σ(a + σ(c)) = σ(b)$ Por la Definición de σ
(D) $σ(a) + σ(c) = σ(b)$ Por la Definición de +
(E) $a + σ(σ(c)) = σ(b)$ Por la Definición de σ y +

Ahora desde (WH)
(WH) $σ(b) < a$
(K) $∃ e, σ(b) + σ(e) = a$ Por la Definición de <
(L) $σ(b) = a + σ(σ(c))$ por (E).Symmetry de la igualdad
(M) $(a + σ(σ(c))) + σ(e) = a$ por (L) y (K) Transistividad de la igualdad
(N) $a + (σ(σ(c)) + σ(e)) = a$ por la Asociatividad de +
(N) $a + σ(σ(c) + e) = a$ por la Definición de +
(O) $a < a$ por la Definición de <
(P) Contradicción con la irreflexividad de <.

¬ WH ⇒ $σ(b) ≥ a$

Pero una vez tenemos en 6. $σ(a) = a + σ(σ(k) + j)$, suponiendo $k=0$ y $j=0$, nos queda $suc(a) = a + suc(suc(0))$, y de aquí $suc(a) = suc(a + suc(0))$, y de ahí $a = a + suc(0)$, $a = suc (a + 0) = suc(a)$ contradictorio. Con $suc$ si podemos usar inducción. A lo que si hemos llegado es a $suc(a) = suc(a + (suc(k) + j))$. Y sabemos que el caso $j=0$ y $k=0$ no puede ser.  Sea $j \neq 0$, esto es, sea $j = suc(j')$. Entonces $suc(a) = suc(a + (suc(k) + suc(j'))) = suc(a + suc(suc(k+j')))$, $a = a + suc(suc(k+j'))$, de dónde $a < a$. Supongamos que $j=0$, y $k \neq 0$, esto es $k = suc(k')$

$suc(a) = suc(a + (suc(k) + j))$ y $j=0$ y $k = suc(k')$

Esto nos da $suc(a) = suc(a + (suc(suc(k')) + 0))$ y $a = a + suc(suc(k'))$, de dónde $a < a$.

Ahora, suponiendo que k = suc(k') y j = suc(j') nos da $suc(a) = suc(a + (suc(suc(k')) + suc(j')))$, $a = a + (suc(suc(k')) + suc(j'))$, de dónde $a < a$.


### 2026-04-21 — Automatización de Tácticas (Fase 4)

**Identidad y Debilitamiento**:
- Se ha implementado con éxito la táctica `derive_hyp` (basada en recursión sobre `List.Mem.head` y `List.Mem.tail` mediante `MetaM`) para cerrar automáticamente cualquier objetivo de la forma `Γ ⊢ f` siempre que `f ∈ Γ`. Esto cubre completamente la regla de identidad.
- Para el debilitamiento (`weakening`), un enfoque similar con una macro/táctica `derive_weaken T` puede tomar un teorema `T : Γ ⊢ f`, aplicar `Derives.weakening`, y luego descargar la submeta de inclusión de listas iterando sobre los elementos de `Γ` (usando `prove_mem` internamente para cada uno). Debido a que las listas `Γ` en nuestras pruebas suelen ser concretas (ej. `[A, B]`), este enfoque sintáctico funcionará bien.

**Automatización de `rewrite_at`**:
- El problema central de `rewrite_at` es que aplicar una regla local en Deducción Natural (`LocalRule`) en una posición `p` arbitraria requiere especificar explícitamente esa posición y las subfórmulas exactas (`sub` y `sub'`), lo que hace que las pruebas sean largas y propensas a errores de índice.
- *Investigación de enfoque*: En lugar de forzar al usuario a proporcionar la posición `p`, podemos crear una táctica en Lean 4 (`derive_rewrite`) que haga lo siguiente:
  1. Tome como argumento la fórmula original (o busque en `Γ` si se aplica hacia adelante) y la regla a aplicar (ej. `LocalRule.doubleNegElim`).
  2. Implemente una función `MetaM` que recorra el AST de la fórmula (`Formula`) construyendo la lista de todas las posiciones válidas (`getAllPositions`).
  3. En cada posición `p`, extraiga la subfórmula con `getAt?` e intente unificarla con el lado izquierdo de la regla dada.
  4. Si unifica, aplique `Derives.rewrite_at` con esa `p` y verifique si el resultado (`replaceAt`) coincide con el objetivo esperado.
- *Desafío*: `LocalRule` en Lean está definido como un `Prop`, lo que significa que no podemos "ejecutarlo" para extraer el patrón directamente en código de nivel de término fácilmente sin usar `Expr` unificators de `Lean.Meta`. 
- *Alternativa más simple*: En lugar de recibir un `LocalRule`, la táctica podría recibir la subfórmula a buscar y la subfórmula de reemplazo explícitamente, y la táctica simplemente encuentra la posición `p` donde ocurre esa subfórmula por primera vez y delega al usuario la prueba de que `LocalRule sub sub'` es válida.

---

## Open Questions

- [ ] [Question 1 — e.g., "Should we use hierarchical partition keys?"]
- [ ] [Question 2 — e.g., "Is the current axiom ordering optimal?"]

---

## Lessons Learned

### Naming Conventions

- Mathlib naming conventions (NAMING-CONVENTIONS.md) significantly improve searchability
- The `mem_X_iff` pattern is more discoverable than `X_is_specified`
- Predicates as prefix (`isNat_zero`) are more consistent than suffix (`zero_is_nat`)

### Module Organization

- Subdirectories should mirror sub-namespaces
- Each subdirectory benefits from a `Basic.lean` for foundational definitions
- Extension modules (`FooExt.lean`) are preferable to modifying frozen modules

### Documentation

- REFERENCE.md must be self-sufficient for AI assistants
- The "project" protocol (AI-GUIDE.md §12) prevents documentation drift
- Annotations (`@importance`, `@axiom_system`) help AI prioritize context loading

---

## Future Directions

[Record long-term goals and aspirations for the project.]
