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
