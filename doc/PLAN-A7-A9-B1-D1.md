# El plan de A7, A9, B1 y D1

**Last updated:** 2026-11-10 — creado con [ADR‑264](../DECISIONS.md): el estudio y el plan de cuatro filas de
`doc/AUDITORIAS.md` §2 (el núcleo de `[B]`, `prf_list_induction` sin `listInd`, las capas dentro de RPP y las preguntas
de T71). PROPUESTO: nada ejecutado; faltan tres decisiones del propietario (§0).
**Autor:** Julián Calderón Almendros

> **Qué es esto.** El propietario (2026‑11‑10): «Estoy interesado en A7, A9, B1 y D1. Haz un pequeño estudio/plan para
> atacarlos. Estamos en modo planificación», y después «déjalo escrito todo». Lo MEDIDO lleva su ámbito: el 2026‑11‑10,
> sobre RPP `8b2bb98` y FOL `f5899aa`, por lectura del texto fuente sin comentarios salvo que se diga otra cosa (la
> herramienta y su salida, en `doc/registro/2026-11-10-plan/`). Lo ESTIMADO lo dice. Los IDs (A7, A9, B1, D1) son los
> de `doc/AUDITORIAS.md` §2.

## 0 · Lo que falta decidir (el propietario)

1. **A7:** ¿entra el cuarto cambio (§2, paso 1.d): que `[B]` dé por vivo el nombre ENTERO de una constante de Lean que el
   proyecto no declaró nunca (`if_neg`, `of_decide_eq_false`)?
2. **B1:** ¿cuántas capas (§4: nueve, una por familia, o menos), y los titulares juntos o separados por clase (i)/(ii)?
3. **D1:** ¿sólo las dos primeras preguntas (§5), dejando escritas las otras dos como problemas abiertos?

## 1 · El orden propuesto

| paso | qué | por qué en este orden |
|---|---|---|
| 1 | **A7** | corto, independiente y obligatoriamente aislado (un cambio de `b-citas.awk` va SOLO, ADR‑167); deja `[B]` limpio antes de tocar nada más |
| 2 | **B1, fase 0** (medir y diseñar) | A9 reordena la capa baja: mejor decidir dónde queda cada pieza con el mapa de capas delante |
| 3 | **A9** | la reordenación, hecha según ese mapa |
| 4 | **B1, fases 1 a 3** | el manifiesto se fija sobre el orden final, no sobre el de hoy |
| 5 | **D1** (las preguntas 1 y 2) | independiente, en FOL; puede ir en paralelo con lo anterior |

## 2 · A7 — tres mejoras del núcleo de `[B]` (y una cuarta, a decidir)

**Lo medido.**
* `marcado()` (`b-citas.awk`, desde la línea 200) pasa el segmento por `tolower` y busca un marcador de estado
  (`MARKW`, líneas 60–63). En locale C (y en mawk, el de la CI) `tolower` no baja las vocales acentuadas: «se RETIRÓ»
  queda «se retirÓ», y el patrón sólo conoce «ó» (`\303\263`). No casa.
* `MARKW` pide «se » seguido de la palabra: en «se **BORRARON**» los asteriscos de la negrita se interponen. No casa.
* `scripts/VolcarEntorno.lean` (líneas 62–64) sólo vuelca, de la tabla de tokens del parser, los que empiezan por «#»
  (las órdenes, clase T). Las tácticas del proyecto (`derive_hyp`, `derive_rewrite`, `derive_weaken`, de
  `FOL/Tactics.lean`, declaradas con `elab`/`syntax`) y las de Lean (`exact?`) son tokens, pero no se vuelcan.
* Lo que queda en `[B]` (ADR‑262 §6; la razón de cada una, en `doc/registro/2026-11-09-deuda/LEEME.txt`): en RPP 10
  —`ci/**`, `Sugerencias.md` ×2, `sondeos/pasadas/salida/`, `#censoFrontera`, `#noExiste`, `if_neg`, `exact?` ×2,
  `decodeTerm.eq_1`—; en FOL 29 —`derive_*` ×8, `of_decide_eq_false`, `not_eq_of_beq_eq_false`, `not_not_em`, `_of_`,
  `DautoImplicit` y las 14 de PeanoRF—.
* Las dos primeras mejoras no quitan ninguna de esas 39: los editores de ADR‑262 escribieron alrededor de ellas. Valen
  para lo que se escriba a partir de ahora.

**El plan.**
1. Un prototipo FUERA del árbol: copia de `b-citas.awk` y de `scripts/VolcarEntorno.lean` con:
   a. las mayúsculas acentuadas, a minúsculas antes de casar (Á É Í Ó Ú Ñ Ü, byte a byte, como el `bajar()` de `[A]`);
      y lo mismo en la línea 186, que también usa `tolower`;
   b. los `*` del segmento, a espacios (sin mover posiciones: `marcado()` mide distancias en bytes) y «se +» en `MARKW`;
   c. los tokens del parser con forma de identificador, volcados como clase T (los dos repos tienen su
      `scripts/VolcarEntorno.lean`);
   d. (si el propietario lo aprueba) un nombre que es el nombre ENTERO de una constante del entorno de Lean, nunca
      declarada por el proyecto (no está en el historial), cuenta como vivo; lo que el proyecto sí declaró alguna vez
      (`not_not_em`) sigue muerto.
2. Medir con `b-uno.bash` (`doc/registro/2026-11-09-deuda/b-uno.bash.txt`) qué citas caen. ESTIMACIÓN, por lectura de
   la lista de arriba: con a–c, RPP 10 → 8 (los dos `exact?`) y FOL 29 → 21 (los ocho `derive_*`); con d, además
   `if_neg`, `of_decide_eq_false` y `not_eq_of_beq_eq_false`: RPP → 7, FOL → 19. `decodeTerm.eq_1` (un nombre que Lean
   genera a demanda) cae sólo si d lo resuelve como nombre reservado. No caen: `ci/**`, los ficheros ignorados, las
   órdenes `#…` de sondeos (no están en el entorno del build), `_of_`, `DautoImplicit` ni PeanoRF.
3. El autotest (`B_AUTO_ESP` en `b-control.bash`): un caso por mejora, y VERLO FALLAR con un mutante por mejora (un
   mutante que no ejecuta su camino sale puro).
4. La revisión adversarial ANTES del commit: cada mejora abre una vía nueva de verde, y las revisiones de ADR‑166/167
   encontraron agujeros en este mismo núcleo. En especial: que (b) no convierta en marcador un `*` de un glob, y que (c)
   no absuelva un identificador de los muertos de HIST.
5. El commit, SOLO (ADR‑167), primero en FOL y después en RPP (M‑12); `b-citas.awk` y `b-control.bash` idénticos byte a
   byte en los dos; `--b-deuda-rehacer` en los dos; el ADR, en otro push.

**Cómo se verifica.** El autotest con sus mutantes; las cifras de `[B]` antes y después, medidas por las dos CI; la
portabilidad (mawk en la CI y gawk en local: mawk retrocede con las ventanas de regex largas).

**Riesgo:** debilitar un control sin que se note (por eso el paso 4). **Coste:** medio día (ESTIMACIÓN).

## 3 · A9 — que ningún titular construya pasos `Prf.listInd`

**Lo medido.**
* `prf_list_induction` (`Meta/ChainPrf.lean`) envuelve el constructor `Prf.listInd`. Sus usos: **21 en 8 módulos** —
  `ChainPrf` 9, `BoundedInPrf` 2, `ChainOkBoundedPrf` 3, `CodeWitnessPrf` 2, `EvalListPrf` 1, `EvalNthcPrf` 1,
  `RunFnBoundedPrf` 2 y `SubstfcWitnessPrf` 1 (la herramienta cuenta 11 en `ChainPrf`: los 9 usos, la declaración y
  el `export`). `NatArithPrf` sólo la nombra en un comentario.
* Los titulares que construyen `listInd`, según `sondeos/InduccionTitulares.lean` (sus ejecuciones registradas, la
  última del 2026‑10‑21): por `prf_list_induction`, D2 (por `prf_runFn_concat` y otros ocho de `ChainPrf`), D3,
  `prf_con_imp_godel`, `goedel_second_prf`, `goedel_II`, los dos de Rosser (por NegNum), `lob` y los dos corolarios de
  T78 de la clase (i); y otros sólo al DECODIFICAR con W1 las líneas que el verificador acepta en el modelo
  (`SolidezVerificador.linea_listInd`: `goedel_I_neg`, los cuatro de T75e…) o dentro de las traducciones
  (`deduction_aux` reconstruye el paso que recibe). No la alcanzan D1, `goedel_first_prf`, `goedel_I`, `prf_tarski`,
  `tarski` ni `tarski_semantico`.
* `Meta/ListIndAdmisible.lean` (ADR‑259) da `listInd_admisible` y `prf_list_induction_sin`, con la misma firma que
  `prf_list_induction` y sin `listInd`. Pero no puede sustituirla donde está, porque **hay un ciclo de imports**:
  importa `ChainPrf` directamente; importa la cadena aritmética (`NatArithPrf` importa `ChainPrf`, y las otras cinco
  —`NatOrderPrf`, `NatMulPrf`, `CantorMonoPrf`, `StrongInductionPrf`, `Div2ParityPrf`— lo traen por ella); e importa
  `CodeWitnessPrf`, que es usuaria y trae a `BoundedInPrf`, otra usuaria.
* Lo que esa cadena toma de verdad de `ChainPrf`: sólo diez lemas ecuacionales de `PrfH` —`PrfH_congr_cons_head`,
  `PrfH_eq_symm`, `PrfH_eq_trans`, `PrfH_iff_mp`, `PrfH_iff_mpr`, `PrfH_leibniz_subst`, `PrfH_lt_subst1`,
  `PrfH_lt_subst2`, `PrfH_or_elim`, `PrfH_spec`—, ninguno de listas. Y `ListIndAdmisible` toma de `CodeWitnessPrf`
  `consOk` y `prf_consOk_cons` (de 175 declaraciones), y de `BoundedInPrf`, `prf_zero_or_eq_succ_pred` (de 19).
* `ChainPrf` está en el cierre de imports de 101 de los 121 ficheros `.lean` de `ROBINSON_PlusPlus/` (`DEPENDENCIES.md`:
  120 módulos activos, 402 aristas, profundidad 59). Moverla es recompilar casi todo.

**La vía limpia:** volver a demostrar `prf_list_induction` —el MISMO nombre y el MISMO enunciado— como corolario de
`listInd_admisible`. Ningún usuario cambia, y ninguno construye `listInd`.

**El plan.**
0. **Medir con el elaborador** (medio día, ESTIMACIÓN): un sondeo que dé el cierre de constantes de las trece piezas de
   arriba (los diez `PrfH_*`, `consOk`, `prf_consOk_cons`, `prf_zero_or_eq_succ_pred`) y confirme que ninguna alcanza
   `Prf.listInd`; y en qué módulo vive cada constante de esos cierres. La medida de arriba es textual: ésta decide.
   Y re‑ejecutar `sondeos/InduccionTitulares.lean` sobre los 35 titulares de hoy (la línea de base, con la frontera de
   cada uno: `prf_list_induction`, la decodificación o las traducciones). Medir también si
   `SolidezVerificador.linea_listInd` puede usar `prf_list_induction_sin` (está muy por encima de `ListIndAdmisible`):
   quitaría `listInd` de la decodificación. `deduction_aux` no puede (`ListIndAdmisible` necesita el teorema de la
   deducción: sería un ciclo).
1. **Un ADR de diseño** con el corte:
   * los diez `PrfH_*` (y lo que su cierre pida), de `ChainPrf` a un módulo más bajo. Para que los nombres completos no
     cambien, el módulo nuevo puede declararlos dentro de `namespace ROBINSON_PlusPlus.Meta.ChainPrf` (lo decide el ADR,
     frente a NAMING‑CONVENTIONS; la otra opción es un espacio nuevo con `export`, y las huellas verán renombres);
   * `consOk`, `prf_consOk_cons` y `prf_zero_or_eq_succ_pred`, también abajo;
   * la cadena aritmética importa el módulo bajo, no `ChainPrf`; `ListIndAdmisible` queda entre la aritmética y
     `ChainPrf`; `ChainPrf` importa `ListIndAdmisible` y define `prf_list_induction` con `prf_list_induction_sin`.
2. **La verificación:** el build; las huellas (ADR‑261): ningún TIPO cambia, sólo los valores de `prf_list_induction`
   y de lo movido; los footprints y el contrato de T07, iguales; `InduccionTitulares`: ningún titular alcanza
   `prf_list_induction` por un camino que construya `listInd`, y lo que quede de `listInd` en los cierres, sólo dentro
   de las traducciones (y de la decodificación, si no se cambia), con su lista; la CI completa; el tiempo y la memoria
   del build, medidos (la profundidad del grafo crece).
3. **No hay atajo parcial:** redirigir sólo los usuarios de arriba (`ChainOkBoundedPrf`, que ya podría importar
   `ListIndAdmisible`) no basta, porque D2 llega por `prf_runFn_concat`, que está dentro de `ChainPrf`. Las dos opciones
   honestas son la reordenación o no hacerlo (la admisibilidad ya está en el build como metateorema).

**Lo que da:** las pruebas de los titulares dejan de construir pasos `listInd` (salvo los que reciben y traducen),
medido; una regla menos para Gentzen (A4). Quitar `listInd` de `Prf` es otra decisión, mayor (el verificador, el ancla,
`G`), y queda fuera.

**Riesgo:** medio: toca la capa baja y recompila casi todo; si el paso 0 encuentra que el cierre de `consOk` arrastra
mucho, el corte crece. **Coste:** de uno a dos días (ESTIMACIÓN).

## 4 · B1 — las capas dentro de RPP (ADR‑139 paso 3, aprobado en ADR‑140 §1)

**Lo medido.** No hay manifiesto ni control. Lo que sí hay: `DEPENDENCIES.md`, generado y con `--check` en la CI
(ADR‑238: 120 módulos activos, 402 aristas, profundidad 59, sin ciclos); las familias de `Meta/` en prosa
(CURRENT‑STATUS §4 —decía «siete familias» y listaba ocho: corregido en ADR‑264—); el contrato de los titulares (T07); y
la pureza de los titulares de la clase (i) (T08: el modelo no está en su cierre), que ya es una frontera de capa.

**El plan.**
0. **Medir** (medio día, ESTIMACIÓN): asignar cada módulo a una capa tentativa y contar los imports que SUBEN de capa.
   Esa lista es lo que el diseño tiene que resolver. Las capas tentativas, una por familia de CURRENT‑STATUS §4:

   | capa | qué contiene |
   |---|---|
   | C0 | `Minimal/` y `Full/`: el lenguaje y los axiomas |
   | C1 | la codificación y el cálculo (`Godel`, `Provability`, `Hilbert`, `HilbertDeduction`, `HilbertSeq`, la aritmética de códigos y el verificador) |
   | C2 | la aritmética dentro de `Prf` |
   | C3 | D1, D2 y el punto fijo |
   | C4 | D3 |
   | C5 | el modelo, la solidez y la consistencia |
   | C6 | el puente con FOL |
   | C7 | los titulares |
   | C8 | los controles del build (T07, T08) |

   Los titulares de la clase (ii) necesitan C5 y los de la clase (i) no pueden tocarla: o C7 se parte en dos, o la
   regla de T08 se queda como la frontera dentro de C7. Algún módulo puede tener que partirse (uno con parte sintáctica
   y parte semántica). `ChainPrf` y su familia de listas no tienen familia en la prosa de hoy: el paso 0 lo resuelve
   (y A9 la mueve).
1. **El ADR de diseño:** las capas, la regla (un módulo sólo importa de su capa o de las de abajo) y las excepciones,
   cada una con su razón.
2. **El manifiesto y su control:** `doc/control/capas.tsv` (módulo → capa) y `check-capas.bash`, en las dos CI: rojo si
   un módulo falta o está dos veces, si un import sube de capa sin excepción, o si una excepción no tiene razón; con su
   autotest y visto fallar.
3. **Los contratos por capa** (lo que ADR‑140 §1 llama contratos generados): la superficie de cada capa —nombres y
   huella del tipo, de las huellas de ADR‑261 y del índice de ADR‑254— en un fichero generado, para que un cambio de API
   de una capa baja se vea en el diff.

**Coste:** de dos a tres días en total (ESTIMACIÓN).

## 5 · D1 — las preguntas abiertas de T71 (FOL)

**Lo medido.** `../FOL/auditoria/t71-semanticos-2026-10-29/README.md`, «Lo que queda abierto». Ya está demostrado
(ADR‑220 y ADR‑221): el enunciado de la completitud implica Markov para las ecuaciones diofánticas (`FOL/Markov0.lean`);
el de la compacidad implica WLEM; LS↓ y «countable infinite» implican KSst, y KSst implica WKS; los dos «large»
implican WLPO y WKS (`FOL/EsencialidadSem0.lean`). Ninguno de los dos módulos está congelado.

| # | la pregunta | cómo se ataca | viabilidad (ESTIMACIÓN) |
|---|---|---|---|
| 1 | ¿La compacidad implica Markov diofántico, como la completitud? | una prueba en Lean, sin axiomas, siguiendo el molde de `Markov0`; si no sale, entender por qué | media: `Markov0` se apoya en que la derivabilidad es Σ₁, y la compacidad no da un objeto finito; un día o dos |
| 2 | ¿Alguno de los cinco enunciados implica DNS o ¬¬EM? | intentar la implicación positiva, uno a uno | media; un intento fallido es información, no una prueba de independencia |
| 3 | La cota por arriba: ¿WLEM + ¬¬EM bastan para los cinco? | demostrar la compacidad (y luego los demás) con esas hipótesis en lugar de la lógica clásica | baja: hay que rehacer Lindenbaum con hipótesis; varios días |
| 4 | ¿KSst es estrictamente más fuerte que WKS sin Markov? | una separación: un modelo (Kripke, haces o realizabilidad) en que valga uno y no el otro | muy baja dentro de Lean: es investigación |

**El plan:** la 1, después la 2; la 3 y la 4, escritas como problemas abiertos. Cada resultado, en un módulo de FOL
(`FOL/EsencialidadSem0.lean` o uno nuevo al lado), con su footprint vigilado y su ADR; los intentos, en
`auditoria/` de FOL, como los de T71.

**Véase también:** `doc/AUDITORIAS.md` §2 (de dónde salen las cuatro filas), ADR‑167 (`[B]` va solo), ADR‑259 (la
admisibilidad de `listInd`), ADR‑140 §1 (las capas), ADR‑221 (T71).
