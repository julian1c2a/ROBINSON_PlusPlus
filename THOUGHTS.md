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

## 3.4. Signos que no aparecen en los alfabetos de FOL⁼ pero sí en los axiomas de `Minimal`

- `+`, `*`, `σ`, `τ`, `div2`, `mod2`, `cantor_func` (o `pair`), `π₁`, `π₂`, `Nil`, `Cons`, `In`, `⊕`, `√` .

- `tau_symb` podría cambiarse por `pred_symb` para ser más descriptivo.

- De hecho, el sistema `Minimal`, debería de incluir también símbolos subíndices y superíndices, como $\{ \quad {}^1 , \quad {}^2, \quad {}^{-1}, \quad {}^{-2}, \quad {}_1, \quad {}_2, \ldots\quad \}$. De esta forma no nos haría falta un símbolo como `π₁` o `π₂`, directamente en el alfabeto, sino que tendríamos `π`, y los anteriores subíndices y superíndices para componer nombres de funciones, por ejemplo, o `i-ésimo` elemento de una lista o de un conjunto ordenado.

- El símbolo `In` soy partidario de cambiarlo por `∈` infijo, y `⊕` por `##`. `Cons` podría sustituirse por `::` y `Nil` por `[]`.

- De esta forma, el alfabeto de `Minimal` se mantendría más cercano a la notación  matemática estándar, aunque esto es una cuestión de estilo y no afecta a la fundamentación.

- La función `div2` podría pasar a representarse como $/_2$, igual que `mod2` como `%_2`, para mantener la notación más cercana a la matemática estándar.

## ¿Es necesario el axioma 22?

El verdadero axioma 22 es $a < b ⟹ σ(a) ≤ b$.

(A) Hipótesis: $a < b$
(B) Tricotomía (Ax): $a < b ∨ a = b ∨ b < a$
(C) $σ(a) < b ∨ σ(a) = b ∨ b < σ(a)$ Axioma de Tricotomía reescrito con $σ(a)$
(D) $σ(a) ≤ b ∨ b < σ(a)$ Por la Definición de ≤

De (A) y (D) demostramos que si $¬ (b < σ(a))$ entonces $σ(a) ≤ b$, lo que es exactamente el axioma 22.

Vamos a suponer que (WH) $b < σ(a)$ y nuestra hipótesis inicial (IA) $a < b$.

(IA) $a < b$

(A) ∃ c, a + σ(c) = b$ Por (IA) + la Definición de <

(B) $a + σ(c) = b$ Por (A)

(C) $σ(a + σ(c)) = σ(b)$ Por ser σ función (aplicación de σ a ambos lados de la igualdad)

(D) $a + σ(σ(c)) = σ(b)$ Por la Definición de +

(E) $σ(b) = a + σ(σ(c))$ Por (D) y Simetría de la igualdad

(F) $σ(b) = σ(a + σ(c))$ Por (E) y la Definición de +

(G) $b = a + σ(c)$ Por (F) y la Inyectividad de σ

(H) $b = a + (c + σ(0))$ Por (F) y la Inyectividad de σ

Ahora desde (WH)

Por el axioma de tricotomías $b < σ(a) ∨ b = σ(a) ∨ σ(a) < b$
De las tres posibilidades supondremos la primera, será nuestra hipótesis de trabajo (WH) para llegar a una contradicción:

(WH) $b < σ(a)$

(I) $∃ d, b + σ(d) = σ(a)$ Por WH y la Definición de <

(J) $b + σ(d) = a + σ(0)$ Por (I) y la Definición de +

Ahora desde (H) e (J) tenemos:

(K) $a + (c + σ(0)) = b$ Por (H) Simetría de la igualdad

(L) $b + σ(d) = a + σ(0)$ Por (J)

(N) $a + (σ(0) + c) = b$ Por (K) y Conmutatividad de la suma

(M) $(a + σ(0)) + c = b$ Por (N) y Asociatividad de la suma

(O) $(b + σ(d)) + c = b$ Por (M) y la Sustiotución de (J) en (M)

(P) $b + (σ(d) + c) = b$ Por (O) y Asociatividad de la suma

(Q) $b + σ(d + c) = b$ Por (P) y Conmutatividad de la suma

(R) $b < b$ Por (Q) y la Definición de <

(S) Contradicción, por lo tanto $¬ (b < σ(a))$ y entonces $σ(a) ≤ b$.




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
