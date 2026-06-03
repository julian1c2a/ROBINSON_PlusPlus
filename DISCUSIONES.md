# Discusión sobre Axiomas Temporales

**Última actualización:** 2026-06-03 — ~~ax22~~, ~~ax23~~, ~~ax27~~, ~~ax28~~ ELIMINADOS; este doc queda como nota histórica.
**Autor**: Julián Calderón Almendros

Este documento analiza la necesidad y redundancia de ciertos axiomas que se han introducido de forma temporal en el sistema `Minimal`.

> **Estado actualizado (2026-06-03)**:
>
> - ~~**ax22, ax23**~~ (scaffolding Cantor): **ELIMINADOS 2026-06-02** (commit `537fd68`). `proj1`/`proj2` ya no son símbolos opacos sino `def proj1 (c) := x_of_c c` y `def proj2 (c) := y_of_c c` en `Block4_C6_C7`. El contenido de ax22 se prueba como teorema `proj_is_cantor`. ax23 nunca se usó en código (la unicidad real estaba probada como `cantor_uniqueness`).
> - **ax27** (add_left_cancel): sigue siendo necesario sin inducción.
> - ~~**ax28** (mul_two_cancel)~~: **ELIMINADO 2026-06-02**. La spec ya tenía la prueba sin inducción; reprobado como `teo_2_11` en Block1 (vía tricotomía + irreflexividad + monotonía estricta de *2).

## Análisis histórico de los Axiomas 22 y 23 (eliminados)

Los axiomas 22 y 23 se introdujeron originalmente para poder definir las funciones de proyección `π₁` y `π₂` antes de haber demostrado formalmente que la función de apareamiento de Cantor es una biyección. La conclusión declarada era que **ambos axiomas son redundantes** y deberían ser teoremas — exactamente lo que ocurrió en el commit `537fd68` (2026-06-02).

### Axioma 22: `ax22_cantor_proj_exists` (Sobreyectividad) — ELIMINADO

- **Enunciado del Axioma**: `∀ c, is_cantor (π₁ c) (π₂ c) c`
- **Sustituto actual**: `def proj1 (c) := x_of_c c`, `def proj2 (c) := y_of_c c` en `Block4_C6_C7` (testigos concretos de `lemma_C5` + `parity_lemma` + `ax29_sub_witness`), y el teorema `proj_is_cantor (c) : Γ ⊢ mul two c =eq cantor_poly (proj1 c) (proj2 c)` lo demuestra constructivamente con la misma estructura que `cantor_surjectivity`.

### Axioma 23: `ax23_cantor_proj_uniq` (Unicidad Proyectiva) — ELIMINADO

- **Enunciado del Axioma**: `Cantor(x,y,c) ∧ Cantor(x',y',c) ⇒ x=x' ∧ y=y'`
- **Sustituto actual**: el teorema `cantor_uniqueness` en `Block4_C6_C7`, probado vía `lemma_C5_unique` + `cantor_bounds` + `teo_2_11` (cancelación estricta de *2) + `add_left_cancel`. Ax23 nunca se utilizó en código.

## Conclusión histórica (cumplida)

Los axiomas 22 y 23 fueron correctos en su afirmación pero su estatus debía ser el de **teoremas**, como se cumplió el 2026-06-02. La eliminación reduce la superficie axiomática del sistema a **31 axiomas matemáticos** sin sacrificar ningún resultado.

---

## Análisis de los Axiomas 20-26

Esta sección desglosa el propósito y estatus de los axiomas de alto nivel del sistema.

### Axiomas Permanentes del Sistema `Minimal`

*   **Axioma 20 (`ax20_eq_decidable`)**: `∀ n, m, n = m ∨ n ≠ m`
    *   **Propósito**: Establece que la igualdad es decidible. Es fundamental para poder razonar por casos sobre si dos términos son iguales o no.
*   **Axioma 21 (`ax21_mod2_range`)**: `∀ n, mod2(n) = 0 ∨ mod2(n) = 1`
    *   **Propósito**: Define el rango de la función `mod2`. Es crucial para las pruebas de paridad, como el Lema P1.
*   **Axioma 25 (`ax25_tau_zero`)**: `τ(0) = 0`
    *   **Propósito**: Define el caso base de la función predecesor `τ`.
*   **Axioma 26 (`ax26_tau_succ`)**: `∀n, τ(σ(n)) = n`
    *   **Propósito**: Define el paso recursivo de la función predecesor `τ`.

DISCUSIÓN (¿Pueden los axiomas 25 y 26 pasar a ser definiciones + teoremas?):

Def τ : ℕ → ℕ
Def τ(0) := 0
Def ∀ n, τ(σ(n)) := n

Veamos que existe un natural `m` que cumple `τ(n) = m` para cada `n`. De hecho, `m = σ(n)` cumple esta propiedad:
- Para `n = 0`, `τ(0) = 0` por el axioma 25, y `σ(0) = 1`, así que `τ(0) = 0` cumple la propiedad. Las dos reglas colapsan en exactamente el mismo número imagen.
- Cualquier otro número `n` es de la forma `σ(k)` para algún `k`, y entonces `τ(σ(k)) = k` por la propia definición, y `σ(k)` cumple la propiedad. Por otra parte `∀ k, 0 ≠ σ(k)`, así que no hay casos adicionales a considerar.
- Por lo tanto, `τ` es una función total y bien definida, y la definición solo usa los axiomas de `σ`. No se requiere ningún axioma adicional para definir `τ` de esta manera, y no hay contradicciones con los axiomas existentes. Por lo tanto, la función `τ` es perfectamente válida en el sistema `Minimal` con los axiomas dados. No usa inducción para estar perfectamente definida. 

DISCUSIÓN (¿Puede el Axioma 20 pasar a ser un teorema?):

El axioma 20 establece `∀ n, ∀ m, n = m ∨ n ≠ m`

Vamos a pensarlo por casos:

- Si `n` y `m` son el mismo número, entonces `n = m` es verdadero, y la disyunción se cumple.
- Si `n` y `m` son números diferentes, entonces `n ≠ m` es verdadero, y la disyunción se cumple.
- Supongo que el problema es que no se puede demostrar que `n = m` o `n ≠ m` para todos los números `n` y `m` sin usar inducción. Sin embargo voy a intentarlo:
- Para `n = 0` y `m = 0`, `n = m` es verdadero, así que la disyunción se cumple.
- Para `n = 0` y `m = σ(k)` para algún `k`, `n ≠ m` es verdadero, así que la disyunción se cumple, porque para todo `k`, `σ(k) ≠ 0`.
- Idem si `n = σ(k)` y `m = 0`, entonces `n ≠ m` es verdadero, así que la disyunción se cumple.
- Para `n = σ(k)` y `m = σ(l)`. Volvemos a tener dos casos:
    - Si `k = l`, entonces `n = m` es verdadero, así que la disyunción se cumple.
    - Si `k ≠ l`, entonces `n ≠ m` es verdadero, así que la disyunción se cumple.
- ¿No tenemos para la igualdad un principio restringido de exclusión del tercero?

DISCUSIÓN (¿Es el Axioma 20 un teorema?):

Dice así: `∀ n, mod2(n) = 0 ∨ mod2(n) = 1`

Yo creía que con la definición de `div2` y de `mod2` quedaba perfectamente claro que `mod2` solo podía tomar los valores 0 y 1, pero es cierto que no se ha demostrado formalmente. Sin embargo, creo que se puede demostrar sin usar inducción, simplemente por casos sobre la forma de `n`.

Tenemos los siguientes axiomas para `div2` y `mod2`:
Ax 16. $\forall n,\quad mod2(n) = 0 \iff mod2(\sigma(n)) = 1$
Ax 17. $\forall n,\quad \bigl(div2(n) * 2\bigr) + mod2(n) = n$

DISCUSIÓN ¿Como entonces se puede construir la incompletitud de Gödel en un sistema como Q (Aritmética de Robinson) con muchos menos axiomas que `Minimal`?

### Axiomas Temporales (Andamiaje)

Estos axiomas se han añadido para poder avanzar, pero están destinados a ser eliminados una vez que se demuestren los teoremas correspondientes.

*   ~~**Axioma 22 (`ax22_cantor_proj_exists`)**~~ — **ELIMINADO 2026-06-02**: ahora teorema `proj_is_cantor` en `Block4_C6_C7`.
*   ~~**Axioma 23 (`ax23_cantor_proj_uniq`)**~~ — **ELIMINADO 2026-06-02**: el teorema `cantor_uniqueness` ya cubre la unicidad proyectiva sin necesidad de un axioma de respaldo.
*   **Axioma 24 (`ax24_mod2_of_even`)**: `n = 2*k → mod2(n) = 0`
    *   **Propósito**: Postula que el `mod2` de un número par es cero. Es un teorema en sistemas con inducción, pero se mantiene como axioma en `Minimal` porque su prueba formal requiere un sistema más fuerte.
*   ~~**Axioma 27 (`ax27_add_left_cancel`)**~~ — **ELIMINADO 2026-06-03**: derivable en PA⁻ sin inducción. Prueba: por tricotomía (ax19) `a<b ∨ a=b ∨ b<a`; los casos estrictos llevan a `a+c < a+c` vía monotonía (`lt_add_const_of_le_left` + `add_comm'`) y contradicen ax18. Ahora es teorema `add_left_cancel` en `Block4_C6_C7`.
