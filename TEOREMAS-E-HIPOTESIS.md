# TEOREMAS CABECERA — y **quién descarga cada hipótesis** (P‑2)

> ## ESTADO REAL — 2026‑10‑18 · `master` · **130 jobs · 113 módulos · 0 sorry · 0 `axiom` de Lean**
>
> 🏁🏁 **Gödel I entero, Gödel II, Tarski y Rosser, SIN HIPÓTESIS** (ADR‑120, ADR‑121, ADR‑157): `goedel_I : ¬ Prf
> godelCN`, `goedel_I_neg : ¬ Prf ¬godelCN`, `goedel_II : ¬ Prf consistencyFormula'`, `tarski` y `rosser : ¬ Prf R ∧
> ¬ Prf ¬R`. Van sobre `Prf`, cuya teoría, `T_Prf`, contiene a PA, por lectura ([AXIOMS.md](AXIOMS.md) §0). `ConsistentH`
> es un TEOREMA, `consistencia` (un modelo de los 142 y la solidez de `Prf`), y lo único que se supone es el núcleo de
> Lean y sus tres axiomas. 🏁 Rosser vale además para toda extensión finita T+E consistente (`rosser_ext`, ADR‑157), por
> REDUCCIÓN a T (ADR‑144/145: T+E es `PrfH E`), y es de la clase (i): su prueba no usa el modelo, y T08 lo comprueba.
> 🏁 Y Löb (ADR‑159): `lob : Prf (Prov⌜φ⌝ ⇒ φ) → Prf φ`, de la clase (i). Con él, la línea de llegada de RPP está
> completa en sus teoremas.
>
> ✏️ *(2026‑10‑16, ADR‑138)* «Sin hipótesis» quiere decir DENTRO de Lean: la consistencia que da `consistencia` es
> RELATIVA a Lean (PRA ⊢ Con(Lean) → Con(T_Prf)), y no puede ser absoluta (§4).
>
> La columna «¿qué usa la prueba?» de §1 está MEDIDA (`sondeos/InduccionTitulares.lean`, `#modelo`, 2026‑10‑14), y la clase (i)
> la COMPRUEBA cada build desde ADR‑143 (`Meta/PurezaTitulares.lean`, T08): si uno de sus 10 titulares nombra la semántica,
> el build no compila.

**Creado:** 2026‑09‑11 · **Autor:** Julián Calderón Almendros
**Last updated:** 2026-10-18 — ADR‑161: el banner, a 130 jobs y 113 módulos (el paso 3 de ADR‑139, en sus módulos). Antes, el mismo día — ADR‑160 (T66): el banner, a 135 jobs y 118 módulos (el subárbol sin consumidor, retirado). Antes, el mismo día — ADR‑159: 🏁 Löb: el banner, a 140 jobs y 123 módulos (`Meta/Lob.lean`), con Löb; §0, la línea de llegada completa y T08 con 10 titulares; §1, la fila de `lob` en lugar de la ⬜. Antes, el mismo día — ADR‑157: 🏁 Rosser: el banner, a 139 jobs y 122 módulos (`Meta/Rosser.lean`, `Meta/PurezaComando.lean`), con Rosser; §0, la línea de llegada y T08 con 9 titulares; §1, las filas de `rosser_ext` (i) y `rosser` (ii) en lugar de la ⬜; §2 y §4, Rosser. Antes, 2026-10-17 — ADR‑156: el banner, a 137 jobs y 120 módulos (`Meta/RosserNegNum.lean`); la fila de Rosser, con NegNum hecho. Antes, el mismo día — ADR‑154: el banner, a 136 jobs y 119 módulos (`Meta/RosserNegLinea.lean`); la fila de Rosser, con NegLineWF hecho. Antes, el mismo día — ADR‑153: el banner, a 135 jobs y 118 módulos (`Meta/RosserGuardNeg.lean`); la fila de Rosser, con GuardNeg hecho. Antes, el mismo día — ADR‑152: el banner, a 134 jobs y 117 módulos (`Meta/RosserNumEval.lean`); la fila de Rosser, con NumEval hecho. Antes, el mismo día — ADR‑151: la fila de Rosser, con el sondeo de `hasWitF` en verde. Antes, el mismo día — ADR‑150: el banner, a 133 jobs y 116 módulos (`Meta/RosserNumerales.lean`); la fila de Rosser, con la etapa 1 hecha. Antes, el mismo día — ADR‑149: el banner, a 132 jobs y 115 módulos (`Meta/RosserPosNum.lean`); la fila de Rosser, con PosNum hecho; §0, el control del recorrido dentro de un módulo (`mutanteLocal`). Antes, el mismo día — ADR‑148: el banner, a 131 jobs y 114 módulos (`Meta/RosserW1.lean`); la fila de Rosser, con W1(ax) hecha. Antes, el mismo día — ADR‑147: la fila de Rosser, con el diseño aceptado. Antes, 2026-10-16 — ADR‑146: la fila de Rosser remite al diseño de NegNum y PosNum. Antes, el mismo día — ADR‑145: Rosser, por REDUCCIÓN (el banner y su fila). Antes, el mismo día — ADR‑143: la clase (i) la comprueba cada build (`Meta/PurezaTitulares.lean`, T08); el banner, a 130 jobs y 113 módulos. Antes, el mismo día — ADR‑140: la línea de llegada de RPP (§0) y la fila de Löb (§1). Antes, el mismo día — ADR‑138: §4 dice que `ConsistentH` es un teorema DE LEAN, una consistencia RELATIVA (PRA ⊢ Con(Lean) → Con(T_Prf)) que no puede ser absoluta, a qué titulares alcanza y los dos sentidos de «relativa»; §5 lo nombra entre lo que se supone. Antes, 2026-10-14 — ADR‑135 (T09 de `doc/AUDITORIA-SUELO-2026-10-12.md`): reescritos el banner, §1 (con la columna «¿qué usa la prueba?», medida, y la fila de Rosser), §2 (`⊬¬G` existe), §3, §4 y §5; y el documento entra en AUTHORITATIVE. Antes, 2026-10-05 — ADR‑129: D7 ejecutada (los símbolos, `List Char`; las cifras del build, 129 jobs y 112 módulos). Antes, 2026-10-05 — ADR‑121: Gödel I ENTERO (`goedel_I_neg : ¬ Prf ¬G`, por W1) y Tarski (`prf_tarski`, `tarski`, `tarski_semantico`), sin hipótesis. Antes, 2026-10-05 — ADR‑120: `ConsistentH` es un TEOREMA del build (`consistencia`, `Meta/Consistencia.lean`), y Gödel I/II tienen versión SIN HIPÓTESIS (`goedel_I`, `goedel_II`). Antes, 2026-10-05 — ADR‑119, ADR‑118, y 2026-10-04 — ADR‑117: el modelo en un sondeo, la clase `AnclaEq` retirada y el ancla, un teorema. Antes, 2026-10-02 — reescrito entero: la capa `⊢` se retiró ([ADR‑115](DECISIONS.md)).

---

## 0 · Por qué existe este documento

La auditoría del 2026‑09‑11 encontró **F‑1**: `goedel_second'` (retirado, ADR‑024) llevaba meses anunciado como el
Segundo Teorema, y su hipótesis `hgi` **no la podía dar ninguna pieza del árbol**. No lo vio ningún
control, y **no podía verlo**: documentación y código **decían lo mismo**. No había desincronía —
había un hueco.

🔑 **La pregunta que lo destapa, y que este documento mecaniza a mano:**

> *Por cada teorema cabecera: **¿quién descarga cada una de sus hipótesis, y con qué?***
> Si la respuesta es «nadie», el teorema está **montado, no ensamblado** — y hay que decirlo
> **donde se anuncia el resultado**, no en un plan.

⭐ **Y la pregunta que faltaba** (2026‑10‑02, F1): *¿pueden valer **a la vez**?* Una hipótesis que nadie
descarga es información; dos hipótesis **incompatibles** hacen el teorema **vacuo**, con footprint
limpio y todos los controles en verde. `#print axioms` no ve las hipótesis de clase.

⭐⭐ **Y la tercera** (2026‑10‑14, T09): *¿qué usa la prueba?* Desde que `ConsistentH` es un teorema, una hipótesis
`hcon : ConsistentH` se descarga sola, y lo que distingue «basta la consistencia» de «usa la verdad en ℕ» es lo que la
prueba NOMBRA: la columna de §1.

🏁 **La línea de llegada de RPP** (2026‑10‑16, [ADR‑140](DECISIONS.md)): los 18 titulares de `T_UNIVERSO`, Rosser y
Löb (las dos filas ⬜ de §1). Gentzen y el libro quedan fuera de este repositorio. ✏️ 2026‑10‑18
([ADR‑157](DECISIONS.md)): Rosser, hecho: `rosser_ext` y `rosser` entran en `T_UNIVERSO`, que tiene 20. Queda Löb, la
única fila ⬜. ✏️ El mismo día ([ADR‑159](DECISIONS.md)): Löb, hecho (`lob`); la línea de llegada, completa en sus
teoremas, y `T_UNIVERSO` tiene 21.

⚠️ **Regla de mantenimiento**: este documento se actualiza **en el mismo commit** que añade o cambia
un teorema cabecera. Una fila con «⬜ nadie» es información, no un fallo; una fila **ausente** sí es
un fallo. Desde ADR‑135 está en AUTHORITATIVE (lo miran `[A]`, `[A2]` y `[B]` de `check-doc-sync.bash`; `[E]` ya lo miraba), y `[T]`
comprueba lo que antes se llevaba a mano: que cada titular de su universo, `T_UNIVERSO`, esté declarado y tenga UNA
fila en §1 o §3 (el nombre en la columna del nombre), y que ninguna fila sobre. Un titular NUEVO se añade a `T_UNIVERSO` en el mismo commit. La columna «¿qué
usa la prueba?» la mide `#modelo` (`sondeos/InduccionTitulares.lean`), fuera de la CI. La clase (i) la comprueba además cada `lake build`: `Meta/PurezaTitulares.lean` (T08,
ADR‑143) recorre el cierre de sus 10 titulares y FALLA si alguno nombra la semántica, o si `goedel_I`, `tarski` y
`rosser`, los controles positivos, dejan de nombrarla (✏️ 2026‑10‑18, ADR‑157: el recorrido y el comando `#pureza`
están en `Meta/PurezaComando.lean`; la lista, en `PurezaTitulares`, que importa Rosser). Desde ADR‑149 el recorrido sigue también las constantes del fichero en curso,
que es lo que necesita el `#pureza` al final de cada módulo de Rosser, y `mutanteLocal` lo vigila en cada build. Un titular nuevo de la clase (i) entra en su lista `PUROS` en el mismo commit.

---

## 1 · Los titulares — sobre el cálculo finitario `Prf`

**¿Qué usa la prueba?** Tres clases, por lo que el cierre de dependencias de su prueba nombra de la semántica
(`FOL.Metamath.Semantics` —`evalFormula`, `contextSatisfies`…— o la solidez de `Prf`, `Meta/SolidezPrf.lean`):
* **(i) sin el modelo**: el cierre no nombra nada de la semántica. Lo que la prueba da, lo da desde las derivaciones de
  la teoría, la aritmética de la metateoría y, si la hay, la hipótesis `ConsistentH`. ⚠️ El criterio es por espacio de
  nombres: la aritmética de `ModeloCodigo` sobre ℕ (`lineWFT`, `chainOkN`, la verdad del verificador en `V₀`) NO cuenta
  como semántica, y una prueba que usara la verdad en ℕ sin pasar por esos dos espacios no se vería.
* **(ii) el modelo, sólo para descargar `ConsistentH`**: la semántica sólo entra por `consistencia`; quitando ese nodo
  del grafo, desaparece.
* **(iii) la verdad en el modelo, más allá de la consistencia**: la semántica entra también por otro camino (la solidez
  de `T_Prf` en `MNV V₀`, o un enunciado sobre el modelo).

Medido el 2026‑10‑14 con `#modelo` (`sondeos/InduccionTitulares.lean`; el sondeo entero, 19 s; la salida, en
`doc/registro/2026-10-14-t09-teoremas/`): los 17 teoremas clasificados de §1 y §3 dan lo que dice su columna; el
dieciocho, `consistencia`, es el nodo por el que se corta, y la clase no se le aplica. ✏️ 2026‑10‑18 (ADR‑157): los dos
de Rosser, medidos igual (`doc/registro/2026-10-18-rosser/`): `rosser_ext`, (i); `rosser`, (ii). Y `lob` (ADR‑159),
(i) (`doc/registro/2026-10-18-lob/`).

| teorema | hipótesis | ¿quién la descarga? | ¿qué usa la prueba? |
|---|---|---|---|
| **`goedel_first_prf`** (`Meta/GodelTwoPrf.lean`) | `hcon : ConsistentH` | 🏁 **`consistencia`** (`Meta/Consistencia.lean`), en el build: un modelo de los 142 (`MN_axioms`) y la solidez de `Prf` (`prf_sound`); el corolario sin hipótesis es `goedel_I`. Es la hipótesis **mínima** (`¬ Prf ⊥`) | **(i)** |
| **`goedel_second_prf`** (`Meta/GodelTwoPrf.lean`) | `hcon : ConsistentH` | 🏁 ídem; el corolario sin hipótesis es `goedel_II` | **(i)** |
| **`prf_con_imp_godel`** (`Meta/GodelTwoPrf.lean`) | `fp_bwd : Prf (¬Prov⌜G⌝ ⇒ G)` y `nec1 : Prf (Prov⌜G ⇒ ¬Prov⌜G⌝⌝)` | ✅ `goedel_second_prf` las da con el punto fijo (`prf_godelCN_fixedpoint`) y D1 (`repr_pos'_prf`); usa D2 (`d2_prf`) y D3 (`d3_prf_real`) | **(i)** |
| **`prf_godelCN_fixedpoint`** (`Meta/GodelTwoPrf.lean`) | ninguna | — (net‑0 PURO) | **(i)** |
| **`prf_tarski`** (`Meta/TarskiPrf.lean`) | ninguna | — (la teoría refuta `Tr(⌜L⌝) ⇔ L` en el mentiroso `L`) | **(i)** |
| **`goedel_I`**, **`goedel_II`** (`Meta/Consistencia.lean`) | ninguna | — (`goedel_first_prf` y `goedel_second_prf`, aplicados a `consistencia`) | **(ii)** |
| **`tarski`** (`Meta/TarskiPrf.lean`) | ninguna | — (`prf_tarski` y `consistencia`: `¬ Prf (Tr(⌜L⌝) ⇔ L)`) | **(ii)** |
| **`goedel_I_neg`** (`Meta/SolidezVerificador.lean`) | ninguna | — (ADR‑121: `¬ Prf ¬godelCN`, la mitad `⊬¬G`; con `goedel_I`, `G` es INDECIDIBLE) | **(iii)**: `prf_sound` en `MNV V₀` y W1 (`verificador_solido`) |
| **`godelCN_indecidible`**, **`modelo_prov_iff`** (`Meta/SolidezVerificador.lean`) | ninguna | — (ni `G` ni `¬G`; y `MNV V₀ ⊨ Prov(⌜φ⌝) ↔ Prf φ`) | **(iii)** |
| **`godelCN_verdadera`**, **`con_verdadera`** (E10, `Meta/SolidezVerificador.lean`) | ninguna | — (`G` y `Con` son VERDADERAS en `MNV V₀`) | **(iii)** |
| **`tarski_semantico`** (`Meta/TarskiPrf.lean`) | ninguna | — (ninguna fórmula define la verdad en `MNV V₀`) | **(iii)** |
| **`consistencia`** (`Meta/Consistencia.lean`) | ninguna | — (es la que descarga `ConsistentH`) | — es el nodo de corte: la clase no se aplica. Usa el modelo para dar `ConsistentH` (`MN_axioms` y `prf_sound`) |
| **`rosser_ext`** (`Meta/Rosser.lean`) | `hcon : ¬ PrfH E ⊥` (T+E es consistente) y `_hE` (E son sentencias: lo que hace de `PrfH E` la teoría T+E; la prueba no la usa, y `rosser_red` es la forma sin ella) | — es la hipótesis del enunciado, una propiedad de E: puede FALLAR (E = [⊥], y entonces T+[⊥] demuestra su sentencia: `control_bottom`) y puede VALER en un miembro NO sólido (T+¬Con, por Gödel II: `control_neg_con`); con E = [] la descarga `consistencia` (`rosser`). 🏁 ADR‑157: la sentencia de Rosser de T+E, `R E`, es indecidible en T+E; por REDUCCIÓN a T (ADR‑144/145: T+E es `PrfH E`, y su predicado de prueba, el de T delante de `impChain`), con PosNum y NegNum de T (ADR‑148…156, `Meta/RosserW1.lean` … `Meta/RosserNegNum.lean`) | **(i)**; en `PUROS` de T08 |
| **`rosser`** (`Meta/Rosser.lean`) | ninguna | — (`rosser_ext` con E = [], y `consistencia`: ni `R []` ni `¬R []` son teoremas) | **(ii)** |
| **`lob`** (`Meta/Lob.lean`) | `h : Prf (Prov⌜φ⌝ ⇒ φ)`, el antecedente de la regla (como el `Prf φ` de D1) | — puede VALER (si φ es teorema: `lob_iff`) y puede FALLAR (φ = ⊥ y φ = G, con `consistencia`: `control_reflexion_bot`, `control_reflexion_godel`). 🏁 ADR‑159: por el punto fijo de Prov(#0) ⇒ φ y D1–D3; Gödel II sale de él con φ = ⊥ (`goedel_second_de_lob`) | **(i)**; en `PUROS` de T08 |

Las condiciones de derivabilidad, D1–D3, dan **(i)** las tres (§3). Lo que usan de la INDUCCIÓN —otra pregunta, que
`#print axioms` tampoco ve— está en [AXIOMS.md](AXIOMS.md) §0.3: D1 la aritmética, D2 la de listas, ningún titular un
paso de DNE salvo `goedel_I_neg`, al decodificar el modelo, y los dos de Rosser, al decodificar con W1(ax) (✏️ 2026‑10‑18,
ADR‑157).

**Footprint** (medido, `check-footprints.bash`): todos los teoremas de esta tabla salvo `prf_con_imp_godel`, y
`d3_prf_real` → `[propext, Classical.choice, Quot.sound]`. D1, D2 y `prf_con_imp_godel` no tienen fila (T11b; medido a mano el
2026‑10‑12: D1 y `prf_con_imp_godel`, los tres; D2, `[propext, Quot.sound]`). 🔑 *Un footprint limpio no dice que el
teorema diga algo*: lo que lo dice es la columna de arriba.

---

## 2 · Gödel I, la mitad `⊬¬G` — 🏁 `goedel_I_neg` (ADR‑121)

`goedel_I_neg : ¬ Prf (neg godelCN)` (`Meta/SolidezVerificador.lean`), sin hipótesis. La prueba es SEMÁNTICA, clase
**(iii)**: si `Prf ¬G`, por la solidez `¬G` es verdadera en `MNV V₀` y, como el punto fijo también vale en el modelo,
éste cree en una prueba de `G`; W1
(`verificador_solido`: lo que el verificador acepta en el modelo es derivable) da `Prf G`, contra `goedel_I`. No usa
ω‑consistencia ni Rosser: usa la verdad de `T_Prf` en ℕ, que es más que su consistencia. Para `G`, `⊬¬G` pide más
que la consistencia simple (T+¬Con es consistente y demuestra `¬G`): ω‑consistencia, o la verdad en ℕ, como aquí.
Rosser da las dos mitades desde la consistencia simple, cambiando de sentencia (🏁 ADR‑157: `rosser`, y para las extensiones finitas, `rosser_ext`).

> 🗄️ **Registro (hasta ADR‑121, 2026‑10‑05).** Esta sección se titulaba «⛔ NO EXISTE sobre `Prf`». Hasta el 2026‑10‑02
> la mitad `⊬¬G` vivía entera sobre `⊢`, y lo que sigue está retirado con esa capa (ADR‑115):
> `goedel_first_undecidable_numeral` y `goedel_first_undecidable_omega` (retirados), `reflects_of_omega` y
> `NegVerifier`, con `ConsistentOmega` y `OmegaConsistent` como hipótesis, también retirados. `NegVerifier` (ADR‑097) **no estaba demostrado**: su footprint llevaba meta‑reglas refutadas. Y la definición
> de `OmegaConsistent`, trasladada a `Prf`, es refutable (`not_omegaConsistentPrf`, `sondeos/OmegaConsistentRefutable.lean`):
> por eso las dos salidas eran `OmegaConsistentProv` o Rosser. Salió por una tercera, W1 en el modelo.

---

## 3 · Las condiciones de derivabilidad — sobre `Prf`

| | teorema | hipótesis | ¿qué usa la prueba? |
|---|---|---|---|
| **D1** | **`repr_pos'_prf`** (`Meta/Representability2Prf.lean`) | ninguna (el antecedente `Prf φ` es el de la regla; hasta ADR‑118, también `[AnclaEq]`) | **(i)**; usa la inducción aritmética, en esta prueba (AXIOMS §0.3) |
| **D2** | **`d2_prf`** (`Meta/DerivCondPrf.lean`) | ninguna | **(i)**; usa la inducción de listas |
| **D3** | **`d3_prf_real`** (`Meta/PremsBdAllPrf.lean`) | ninguna (`d3_prf_real` nació teorema; sobre `⊢`, D3 fue el `axiom` `d3` hasta el 2026‑09‑10g; hasta ADR‑118, también `[AnclaEq]`) | **(i)**; usa las dos |

Las versiones sobre `⊢` (`repr_pos'`, `d2`, `d3`) están retiradas con esa capa. La ligadura `[AnclaEq]` de D1 y D3,
y las demás del árbol (426), se retiraron con la clase el 2026‑10‑05 ([ADR‑118](DECISIONS.md)).

---

## 4 · Las hipótesis que quedan, y qué son exactamente

| hipótesis | definición | qué es de verdad |
|---|---|---|
| **`ConsistentH`** | `¬ Prf ⊥` | la de `goedel_first_prf` y `goedel_second_prf`: la consistencia de `T_Prf` —los 142 CON los esquemas de `Prf`—, la **mínima honesta**. 🏁🏁 **TEOREMA desde ADR‑120** (2026‑10‑05): `consistencia` (`Meta/Consistencia.lean`), por `prf_sound` (`Meta/SolidezPrf.lean`) y el modelo `MNV V₀` de los 142 (`MN_axioms`) |
| **`¬ PrfH E ⊥`** (de `rosser_ext`, ADR‑157) | T+E no deriva `⊥` | la consistencia de la EXTENSIÓN T+E: un parámetro del enunciado, no un supuesto global. Puede fallar (E = [⊥]) y valer sin solidez (T+¬Con, por Gödel II); con E = [] es `ConsistentH`, y la descarga `consistencia` (`rosser`) |
| ~~`[AnclaEq]`~~ | `Prf (axiomsCodeT =eq listFormCodeM axioms)` | 🏁 **ya no es un supuesto: es TEOREMA** desde ADR‑117 (2026‑10‑04), `prf_ancla` (`Meta/Representability2Prf.lean`), por el axioma objeto DIAGONAL `ax_axiomsCodeT_def`, el último de los 142; la clase, con su instancia, se retiró el 2026‑10‑05 (ADR‑118). Hasta ADR‑117 era ⛔⛔ **INCONSISTENTE** (F1: daba `Prf ⊥` sobre los 141) |

🗑️ **Retiradas con la capa `⊢`** (ADR‑115): `ConsistentOmega` (`¬ (axioms ⊢ ⊥)`), `OmegaConsistent`,
`NegVerifier`, `Reflects`.

### `ConsistentH` es un teorema DE LEAN: consistencia RELATIVA, no absoluta (2026‑10‑16, [ADR‑138](DECISIONS.md))

`consistencia` demuestra en Lean que `Prf` no deriva `⊥`. Fuera de Lean, lo que eso garantiza es una consistencia
**relativa**: PRA ⊢ Con(Lean) → Con(T_Prf). La razón: Con(T_Prf) es una sentencia Π₁. Si `T_Prf` fuera inconsistente,
habría una derivación concreta de `⊥`, un objeto finito; Lean construiría con ella un término de `Prf ⊥` y, con
`consistencia`, derivaría `False`. Y todo eso vale si el núcleo (v4.31.0) implementa bien su teoría de tipos: leanchecker
y los censos `@TRUST`/`@NATIVO` lo vigilan en parte (ADR‑116), pero un error del núcleo no lo excluye ningún control.

**No puede ser absoluta.** `T_Prf` contiene a PA ([AXIOMS.md](AXIOMS.md) §0.1). Por el propio Gödel II, ninguna
teoría contenida en `T_Prf` demuestra Con(T_Prf), salvo que `T_Prf` sea inconsistente. Así que la metateoría que
descarga `ConsistentH` es, por fuerza, MÁS fuerte que la teoría de la que habla. La de Lean lo es con mucho: su teoría
de tipos es equiconsistente con ZFC más infinitos cardinales inaccesibles (Carneiro, *The Type Theory of Lean*, 2019;
de la literatura, no medido aquí). «Sin hipótesis», en los banners, quiere decir sin hipótesis DENTRO de Lean. La que
queda, Con(Lean), Lean no la puede descargar: es Gödel II aplicado a Lean.

**A qué titulares alcanza.** A `consistencia` y a los de las clases (ii) y (iii) de §1. `goedel_I`, `goedel_II`,
`goedel_I_neg`, `tarski` y `rosser` dicen que `Prf` no deriva cierta fórmula, y eso implica `ConsistentH`, porque de `Prf ⊥`
sale cualquier fórmula (EFQ): heredan la misma condición. Los demás de la clase (iii) hablan además de la verdad en
`MNV V₀`, que la teoría ni siquiera puede definir (`tarski_semantico`). Los de la clase (i) —los condicionales
`goedel_first_prf` y `goedel_second_prf`, D1–D3, `prf_tarski`, `rosser_ext`— son otra cosa: no pasan por el modelo, y en ellos está
el contenido gödeliano. Que para ellos baste una metateoría débil es lo esperable (Gödel lo hizo en una finitaria; el plan del
libro dice «≈ IΣ₁»), pero **no está medido**: la columna de §1 mide qué nombra la prueba, no la fuerza de la metateoría
que la reproduciría.

**Dos sentidos de «relativa», para no mezclarlos.**
* *Probada en S*: S ⊢ Con(T). Da PRA ⊢ Con(S) → Con(T). Es el caso de `consistencia`, con S = Lean.
* *Equiconsistencia entre teorías objeto*: por ejemplo, PRA ⊢ Con(HA) ↔ Con(PA), por la traducción negativa de
  Gödel–Gentzen. No afirma la consistencia de ninguna de las dos.

La prueba de Gentzen, PRA + TI(ε₀) ⊢ Con(PA), es del primer tipo con una S mucho más débil que Lean: rebaja aquello
respecto de lo que la consistencia es relativa. Para `T_Prf` haría falta, además, reducirla a PA (interpretar en PA
los símbolos de la codificación, o probar que sus ecuaciones son conservativas), y eso no está hecho (AXIOMS §0.1).

---

## 5 · Lo que se supone — sólo Lean; y `axiom` de Lean, **0**

Los tres `axiom` que quedaban vivían sobre `⊢` y están retirados con esa capa (ADR‑115): `ax_induction_prim`,
`ax_list_induction` (**falso**: daba `[] ⊢ ⊥`, L1‑2) y `ax_axiomsCodeT_eq`, los tres retirados.
⇒ **Ningún postulado gödeliano, ningún `axiom` en el build y ninguna hipótesis sin descargar**: `ConsistentH` es teorema (§4), y lo que ancla `axiomsCodeT` es
un axioma OBJETO de la teoría, el último de los 142. Lo único que se supone es el núcleo de Lean y sus tres axiomas
(`propext`, `Classical.choice`, `Quot.sound`) y, con ellos, su consistencia, que Lean no puede demostrar: lo demostrado
vale relativo a ella (§4, ADR‑138); el detalle, y lo que no fija ningún control (las definiciones: T07), en
[`AXIOMS.md`](AXIOMS.md) §0.2.

---

## 6 · 🗑️ Registro de lo retirado

| | |
|---|---|
| ~~`goedel_second'`~~, ~~`con_imp_godel'`~~ | retirados el 2026‑09‑11 ([ADR‑024](DECISIONS.md), opción (b)): su `hgi : ¬(axioms ⊢ G)` decía «el cálculo refuta `G`», porque `axioms ⊢` era completo |
| ~~`goedel_first_numeral`~~, ~~`goedel_first_undecidable_numeral`~~, ~~`goedel_first_undecidable_omega`~~, ~~`reflects_of_omega`~~, ~~`negVerifier_proved`~~ | retirados el 2026‑10‑02 con la capa `⊢` ([ADR‑115](DECISIONS.md)) |
| ~~`[AnclaEq]`~~ en `goedel_first_prf`, `goedel_second_prf` y `prf_con_imp_godel` | retirada de las tres firmas el 2026‑10‑04 ([ADR‑117](DECISIONS.md)): el ancla es el teorema `prf_ancla` |
| ~~`class AnclaEq`~~, ~~`instAnclaEq`~~ y sus 426 ligaduras | retiradas el 2026‑10‑05 ([ADR‑118](DECISIONS.md)): un commit mecánico; los tres usos de `AnclaEq.eq`, a `prf_ancla` |

---

**Véase también:** [`AXIOMS.md`](AXIOMS.md) §0 (la teoría y lo que se supone), `PLAN-PRUEBAS.md` §4 (lo que ningún
control garantiza), `doc/AUDITORIA-2026-09-11.md` F‑1, `DECISIONS.md` ADR‑022/023/024/026/114/115/117/120/121/135.
