# TEOREMAS CABECERA — y **quién descarga cada hipótesis** (P‑2)

> ## ESTADO REAL — 2026‑09‑11 · `master` · **144 jobs · 130 módulos · 0 sorry · 5 `axiom`**

**Creado:** 2026‑09‑11 · **Autor:** Julián Calderón Almendros

---

## 0 · Por qué existe este documento

La auditoría del 2026‑09‑11 encontró **F‑1**: `goedel_second'` llevaba meses anunciado como el
Segundo Teorema, y su hipótesis `hgi` **no la podía dar ninguna pieza del árbol**. No lo vio ningún
control, y **no podía verlo**: documentación y código **decían lo mismo**. No había desincronía —
había un hueco.

🔑 **La pregunta que lo destapa, y que este documento mecaniza a mano:**

> *Por cada teorema cabecera: **¿quién descarga cada una de sus hipótesis, y con qué?***
> Si la respuesta es «nadie», el teorema está **montado, no ensamblado** — y hay que decirlo
> **donde se anuncia el resultado**, no en un plan.

⚠️ **Regla de mantenimiento**: este documento se actualiza **en el mismo commit** que añade o cambia
un teorema cabecera. Una fila con «⬜ nadie» es información, no un fallo; una fila **ausente** sí es
un fallo.

---

## 1 · La cadena de Gödel

### 🏁 Gödel I — la mitad `⊬G`

| teorema | hipótesis | ¿quién la descarga? |
|---|---|---|
| **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`) | `hcon : ConsistentOmega` | ⬜ **nadie, y es correcto**: es la hipótesis del teorema. ⚠️ Pero **no es «consistencia simple»** — ver §3 y [ADR‑024](DECISIONS.md) |
| | *(el punto fijo)* | ✅ `godelCN_fixedpoint`, **sin hipótesis** |

### ⬜ Gödel I — la mitad `⊬¬G`

| teorema | hipótesis | ¿quién la descarga? |
|---|---|---|
| **`goedel_first_undecidable_numeral`** | `hcon : ConsistentOmega` | ⬜ hipótesis del teorema |
| | `hrefl : Reflects godelCN` | ✅ **`reflects_of_omega`** (`Meta/OmegaReflect.lean`) |
| **`reflects_of_omega`** | `hω : OmegaConsistent` | ⬜ hipótesis META, explícita y honesta |
| | `hneg : NegVerifier` | 🔶 **`negVerifier_of_deudas`** — pero ver la fila siguiente |
| **`negVerifier_of_deudas`** (`Meta/VerifierSound.lean`) | `hchain : DEUDA_chainNeg` | ⛔ **NADIE** — módulo **D** de `PLAN-NEGVERIFIER.md` |
| | `hin : DEUDA_inNeg` | ⛔ **NADIE** — módulo **C** |
| **`goedel_first_undecidable_omega`** | `hcon`, `hω` | ⬜ hipótesis |
| | `hneg : NegVerifier` | ⛔ **NADIE de forma incondicional** ⇒ **la mitad `⊬¬G` NO está cerrada** |

### 🏁 Gödel II — sobre el cálculo finitario

| teorema | hipótesis | ¿quién la descarga? |
|---|---|---|
| **`goedel_second_prf`** (`Meta/GodelTwoPrf.lean`) | `hcon : ConsistentOmega` | ⬜ hipótesis del teorema — **la única** |
| | *(punto fijo)* | ✅ `prf_godelCN_fixedpoint`, **net‑0 PURO** |
| | *(necesitación `nec1`)* | ✅ `repr_pos'_prf` (D1) sobre el punto fijo |
| | *(`Con' ⇒ G`)* | ✅ `prf_con_imp_godel`, sobre `d2_prf` (D2) y `d3_prf_real` (D3) |

⇒ **ninguna hipótesis suelta.** Es lo que distingue *ensamblado* de *montado*.

### 🗑️ Retirado

| | |
|---|---|
| ~~`goedel_second'`~~, ~~`con_imp_godel'`~~ | **retirados el 2026‑09‑11** ([ADR‑024](DECISIONS.md), opción (b)). Su `hgi : ¬(axioms ⊢ G)` no significaba «`G` es indemostrable» sino **«el cálculo refuta `G`»**, porque **`axioms ⊢` es completo** |

---

## 2 · Las condiciones de derivabilidad — las tres, sin hipótesis

| | sobre `⊢` | sobre `Prf` | hipótesis |
|---|---|---|---|
| **D1** | `repr_pos'` | **`repr_pos'_prf`** | ninguna (toma `Prf φ` como argumento, que es su contenido) |
| **D2** | `d2` | **`d2_prf`** | ninguna |
| **D3** | `d3` | **`d3_prf_real`** | ninguna — fue `axiom` hasta el 2026‑09‑10g |

---

## 3 · ⚠️ Las hipótesis que quedan, y qué son exactamente

| hipótesis | definición | qué es de verdad |
|---|---|---|
| **`ConsistentOmega`** | `¬ (axioms ⊢ ⊥)` | ⚠️ **NO es «Q++ es consistente»**. Como `axioms ⊢` es **completo**, dice que una **compleción completa** de `axioms` es consistente — cercano a suponer **solidez**. [ADR‑024](DECISIONS.md) |
| **`ConsistentH`** | `¬ Prf ⊥` | **la honesta**: consistencia del cálculo **finitario**. `consistentH_of_omega` da `ConsistentOmega → ConsistentH`; **la vuelta no existe** |
| **`OmegaConsistent`** | no probar `∃A` refutando todos los testigos estándar | la ω‑consistencia, **estrechada** por [ADR‑022](DECISIONS.md) a testigos con forma de línea |
| **`NegVerifier`** | Δ₀‑completitud negativa del verificador | ⛔ **la única obligación abierta de `⊬¬G`**, reducida a dos deudas con nombre |

⬜ **P‑4** (`PLAN-PRUEBAS.md` §5): **intentar Gödel I y II con `ConsistentH`** en lugar de
`ConsistentOmega`. Sería estrictamente mejor. Si no sale, hay que **escribir por qué** donde se
anuncia el resultado.

---

## 4 · Los 5 `axiom` de Lean — la otra clase de hipótesis

| axioma | qué es | ¿retirable? |
|---|---|---|
| `ax_induction_prim` | el esquema de inducción sobre los 24 primitivos | ⛔ no: **es lo que `Full` significa** |
| `ax_list_induction` | ídem, listas | ⛔ no |
| `ax_p_tfa` | teorema fundamental de la aritmética, forma idealizada | 🔶 `tfa_numeral` es la realización real |
| `ax_axiomsCodeT_eq` | ancla de codificación (⊢) | ⬜ **frente abierto** |
| `prf_axiomsCodeT_eq` | ancla de codificación (`Prf`) | ⬜ **frente abierto** — arrastra casi todo el árbol |

**Ninguno es gödeliano**: D1, D2 y D3 son teoremas.

---

**Véase también:** `PLAN-PRUEBAS.md` §4 (lo que ningún control garantiza),
`doc/AUDITORIA-2026-09-11.md` F‑1, `DECISIONS.md` ADR‑022/023/024.
