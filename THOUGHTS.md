# Thoughts — ProjectName

**Last updated:** 2026-05-11
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

### Decisiones de nomenclatura tomadas (2026-05-11)

- **`pred_sym = "τ"` se mantiene** como símbolo de display (caracter Unicode habitual para
  el predecesor en aritmética de Robinson). Los nombres de axioma pasan de `ax25_tau_*`
  a `ax25_pred_*` / `ax26_pred_*` para ser más legibles en el código Lean. Ejecutado.

- **`Cons` → `cons` y `Nil` → `nil`** (NC-4: constructores term-level en lowerCamelCase).
  Todos los demás constructores (`succ`, `add`, `mul`, `pred`, `concat`...) ya son
  lowerCamelCase; `Cons` y `Nil` son la excepción sin justificación. `cons` y `nil`
  no son keywords en Lean 4 (el namespace los aúsla de `List.cons`/`List.nil`).
  **Pendiente de ejecutar** (requiere actualizar Block6.lean y REFERENCE.md §3.11.3).

- **Símbolo `In`** se mantiene temporalmente (`in` es keyword reservada en Lean 4).
  A largo plazo, podría usarse notación infija `∈` sobreescribiendo la notación de FOL.

- **Símbolos subindice/superindice**: La idea de usar `π` + subíndice en lugar de `π₁`/`π₂`
  es interesante pero requiere soporte en FOL. No prioritario.

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

## ¿Son necesarios los axiomas 25 / 26 sobre el predecesor?

**Decisión (2026-05-11): Sí, son necesarios.** Razón model-teórica: `pred` usa el
símbolo opaco `τ` (pred_sym). Sin ax25/ax26, cualquier función f : N → N satisface el
sistema (el símbolo no queda fijado por los axiomas de σ, +, *). En Block4_C5.lean,
`spec (ax ax26_pred_succ)` se invoca activamente en dos puntos de la prueba de
`lemma_C5`. El argumento por casos de abajo usa inducción implícita y no elimina
la necesidad de los axiomas.

---

*(Borrador original del análisis, conservado para referencia:)*

El axioma 25 establece que `τ(0) = 0`, y el axioma 26 establece que `∀ n, τ(σ(n)) = n`. Estos axiomas definen completamente la función predecesor `τ` en términos de los axiomas de `σ`.

Voy a intentar una aproximación para definir `τ: N → N`

def Pred : ℕ → ℕ → Prop
  |    0 0  => isTrue
  | σ(n) n  => isTrue
  |    __  => isFalse

def pred(n : ℕ) : ℕ :=
  | Pred n 0 => 0
  | Pred n (σ(m)) => m

Con estas dos definiciones, que no envuelven inducción de nigún tipo, podríamos demostrar que `pred(0) = 0` y que `∀ n, n ≠ 0 ∧ n ≠ σ(1) ⟹ pred(n) ≠ 0` y que `∀ n, pred(σ(n)) = n` y `∀ n, ∀ m, pred(m) ≠ pred(n) ⟹ n ≠ m`. Esto nos dice que `pred` es función, porque siempre existe y es única para cada natural.

pred(0) = 0 por la definición.

pred(σ(n)) = n por la definición.
  Tenemos dos casos:

- Si `n = 0`, entonces `pred(σ(0)) = 0` por la primera cláusula de la definición de `pred`.
- Si `n = σ(m)` para algún `m`, entonces `pred(σ(n)) = pred(σ(σ(m))) = σ(m) = n` por la segunda cláusula de la definición de `pred`.

Supongamos ahora que `∃ n, ∃ m, pred(n) ≠ pred(m)`. Esto quiere decir que `σ(pred(n)) ≠ σ(pred(m))` por la definición de `pred`. Por la definición de `pred`, esto implica que `n ≠ m`. Por lo tanto, `pred` es tiene una única imagen para cada natural.

Supongamos que `∃ n, ∃ m, pred(n) = pred(m)`. Esto quiere decir que `σ(pred(n)) = σ(pred(m))` por la definición de `pred` y la inyección de `σ`. Para distinguir casos, supondremos que `n = 0` y que `m = σ(0)`. En este caso, `pred(n) = pred(0) = 0` y `pred(m) = pred(σ(0)) = 0`, por lo que `pred(0) = pred(σ(0))` es correcto. Sin embargo, supongamos que `m = σ(n)` con `n ≠ 0`. En este caso `pred(m) = pred(σ(n)) = n ≠ 0`, por lo que los únicos casos con imagen igual son el `0` y el `1`.

Creo que se define bien la función `pred` sin necesidad de axiomas adicionales.

**Nota (2026-05-11)**: El argumento de arriba usa `| Pred n 0 => ...` que implica
decidibilidad de `Pred`, lo cual requiere inducción o enumeración. En FOL sin inducción,
no podemos derivar ax25/ax26 de los axiomas de σ; los modelos no-standard pueden asignar
a `τ` cualquier valor en `N`. Por tanto ax25/ax26 **son necesarios** en Minimal.

## Estado de los axiomas ax21, ax24, ax27 (2026-05-11)

## Estado de los axiomas ax21, ax24, ax27 (2026-05-11)

Los tres son **necesarios en Minimal** porque sus versiones de teorema en los Block*
son `sorry` pendientes que en el caso general requieren inducción:

| Axioma | Enunciado | Teorema sorry | Requiere |
|--------|-----------|--------------|----------|
| ax21 | `mod2(n) = 0 ∨ mod2(n) = 1` | `mod2_range` (Block3) | inducción sobre n |
| ax24 | `n = 2k → mod2(n) = 0` | `mod2_of_even` (Block5) | inducción sobre k |
| ax27 | `a+c = b+c → a = b` | `add_left_cancel` (Block4_C6_C7) | inducción sobre c |

Si y cuando los sorry se cubran con pruebas completas (independientes de ax21/ax24/ax27),
se podrán comentar fuera de la lista `axioms` como se hizo con ax20. Hasta entonces,
permanecen en la lista. Los comentarios en `Axioms.lean` ya reflejan este estado.

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
