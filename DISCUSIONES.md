# Discusión sobre Axiomas Temporales

**Última actualización:** 2026-05-09
**Autor**: Julián Calderón Almendros

Este documento analiza la necesidad y redundancia de ciertos axiomas que se han introducido de forma temporal en el sistema `Minimal`.

## Análisis de los Axiomas 22 y 23

Los axiomas 22 y 23 se introdujeron para poder definir las funciones de proyección `π₁` y `π₂` antes de haber demostrado formalmente que la función de apareamiento de Cantor es una biyección.

La conclusión es que **ambos axiomas son redundantes** en un sistema completo, ya que son equivalentes a teoremas que se deben demostrar. Sirven como andamiaje temporal.

### Axioma 22: `ax22_cantor_proj_exists` (Sobreyectividad)

- **Enunciado del Axioma**: `∀ c, is_cantor (π₁ c) (π₂ c) c`
- **Significado**: Para cualquier número `c`, existen un `x` y un `y` (que llamamos `π₁ c` y `π₂ c`) tales que `c` es el resultado de aplicarles la función de Cantor.
- **Redundancia**: Este axioma es un postulado directo del **Teorema C6 (Sobreyectividad)**. La estrategia para demostrar C6, como se describe en `TuplasFuncionesYListas.md`, es construir explícitamente las funciones inversas que, dado `c`, encuentran `x` e `y`. Una vez demostrado el Teorema C6, este axioma se puede eliminar.

### Axioma 23: `ax23_cantor_proj_uniq` (Unicidad Proyectiva)

- **Enunciado del Axioma**: `Cantor(x,y,c) ∧ Cantor(x',y',c) ⇒ x=x' ∧ y=y'`
- **Significado**: Si dos pares `(x, y)` y `(x', y')` producen el mismo número `c` bajo la función de Cantor, entonces los pares deben ser idénticos.
- **Redundancia**: Este axioma es un postulado directo del **Teorema C7 (Unicidad Proyectiva)**. La estrategia para demostrar C7 se basa en la unicidad del valor intermedio `w = x+y` que se obtiene en la inversión de la función. Una vez demostrado el Teorema C7, este axioma se puede eliminar.

## Conclusión

Los axiomas 22 y 23 son correctos en su afirmación, pero su estatus debería ser el de **teoremas**. Se mantienen temporalmente para permitir el desarrollo concurrente de las propiedades de las proyecciones mientras se completan las pruebas de sobreyectividad y unicidad de la función de Cantor.

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

### Axiomas Temporales (Andamiaje)

Estos axiomas se han añadido para poder avanzar, pero están destinados a ser eliminados una vez que se demuestren los teoremas correspondientes.

*   **Axioma 22 (`ax22_cantor_proj_exists`)**: `∀ c, is_cantor (π₁ c) (π₂ c) c`
    *   **Propósito**: Postula la **sobreyectividad** de la función de Cantor. Será eliminado cuando se demuestre el **Teorema C6**.
*   **Axioma 23 (`ax23_cantor_proj_uniq`)**: `Cantor(x,y,c) ∧ Cantor(x',y',c) ⇒ x=x' ∧ y=y'`
    *   **Propósito**: Postula la **unicidad proyectiva** de la función de Cantor. Será eliminado cuando se demuestre el **Teorema C7**.
*   **Axioma 24 (`ax24_mod2_of_even`)**: `n = 2*k → mod2(n) = 0`
    *   **Propósito**: Postula que el `mod2` de un número par es cero. Es un teorema en sistemas con inducción, pero se mantiene como axioma en `Minimal` porque su prueba formal requiere un sistema más fuerte.
