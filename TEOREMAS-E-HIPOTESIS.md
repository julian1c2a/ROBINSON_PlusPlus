# TEOREMAS CABECERA — y **quién descarga cada hipótesis** (P‑2)

> ## ESTADO REAL — 2026‑09‑11 · `master` · **145 jobs · 131 módulos · 0 sorry · 5 `axiom`**

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
| 🏁 **`goedel_first_prf`** (`Meta/GodelTwoPrf.lean`) | `hcon : ConsistentH` | ⬜ **nadie, y es correcto**: es la hipótesis del teorema — y es **la MÍNIMA** (`¬ Prf ⊥`). **P‑4 resuelto** |
| | ⭐ **`[AnclaEq]`** (nuevo, 2026‑09‑12) | ⛔⛔ **NADIE. Y hay que leerlo bien.** Era el `axiom prf_axiomsCodeT_eq`; hoy es **hipótesis de instancia** ([ADR‑026](DECISIONS.md)). El footprint bajó a `[propext, Classical.choice, Quot.sound]` — **cero axiomas del proyecto**— pero eso **NO** significa «Gödel sin postulados»: el postulado **se movió a la firma**. ⚠️ **No existe ninguna `instance : AnclaEq` en el árbol** [medido] ⇒ la hipótesis está **abierta**. Anunciar el footprint sin esta fila sería **M‑8 con otro nombre** |
| | *(el punto fijo)* | ✅ `prf_godelCN_fixedpoint`, **net‑0 PURO** |
| `goedel_first_numeral` (`Meta/DiagonalNumeral.lean`) | `hcon : ConsistentOmega` | 🔶 **versión antigua**, sobre la hipótesis **más fuerte**. Se conserva (la usa la cadena `⊢`), pero **el enunciado bueno es el de arriba** |

### ⬜ Gödel I — la mitad `⊬¬G`

| teorema | hipótesis | ¿quién la descarga? |
|---|---|---|
| **`goedel_first_undecidable_numeral`** | `hcon : ConsistentOmega` | ⬜ hipótesis del teorema |
| | `hrefl : Reflects godelCN` | ✅ **`reflects_of_omega`** (`Meta/OmegaReflect.lean`) |
| **`reflects_of_omega`** | `hω : OmegaConsistent` | ⬜ hipótesis META, explícita y honesta |
| | `hneg : NegVerifier` | 🔶 **`negVerifier_of_deudas`** — pero ver la fila siguiente |
| **`negVerifier_of_deudas`** (`Meta/VerifierSound.lean`) | `hchain : DEUDA_chainNeg` | ⛔ **NADIE todavía** — pero ⭐ su **puente** está: `derives_chainOk_neg_of_line` (`Meta/ChainNegPrf.lean` §1). Queda «el decodificador rechaza ⟹ hay línea con `lineWF` refutable», y de sus **cinco** causas **cuatro tienen maquinaria** |
| | `hin : DEUDA_inNeg` | 🏁 **SALDADA** (2026‑09‑11): **`deuda_inNeg`**, `Meta/ChainNegPrf.lean` §3 |
| **`goedel_first_undecidable_omega`** | `hcon`, `hω` | ⬜ hipótesis |
| | `hneg : NegVerifier` | 🔶 **a UNA deuda**: con `deuda_inNeg` saldada, `negVerifier_of_deudas` sólo espera `DEUDA_chainNeg` ⇒ **la mitad `⊬¬G` está a un paso, no a dos** |

### 🏁 Gödel II — sobre el cálculo finitario

| teorema | hipótesis | ¿quién la descarga? |
|---|---|---|
| **`goedel_second_prf`** (`Meta/GodelTwoPrf.lean`) | `hcon : ConsistentH` | ⬜ hipótesis del teorema — **la MÍNIMA** |
| | ⭐ **`[AnclaEq]`** | ⛔⛔ **NADIE** — ídem que Gödel I: el ancla de codificación, **movida del footprint a la firma** ([ADR‑026](DECISIONS.md)). Sin instancia en el árbol |
| | *(punto fijo)* | ✅ `prf_godelCN_fixedpoint`, **net‑0 PURO** |
| | *(necesitación `nec1`)* | ✅ `repr_pos'_prf` (D1) sobre el punto fijo |
| | *(`Con' ⇒ G`)* | ✅ `prf_con_imp_godel`, sobre `d2_prf` (D2) y `d3_prf_real` (D3) |

⇒ **ninguna hipótesis suelta.** Es lo que distingue *ensamblado* de *montado*.

⭐⭐ **Y el footprint lo certifica** (2026‑09‑11, P‑4): con `ConsistentH`, `goedel_first_prf` y
`goedel_second_prf` dependen de

    [propext, Classical.choice, Quot.sound, prf_axiomsCodeT_eq]

**un solo axioma del proyecto.** Desaparecen las ω‑reglas (`dne`, `gen`, `imp_intro`), los dos
esquemas de inducción (`ax_induction_prim`, `ax_list_induction`) y el ancla `⊢`
(`ax_axiomsCodeT_eq`): entraban todos por la hipótesis vieja, que hablaba de `⊢`.
⇒ **la cadena de Gödel de este proyecto es ENTERAMENTE FINITARIA.**

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
| 🏁 **`ConsistentH`** | `¬ Prf ⊥` | **LA QUE SE USA desde el 2026‑09‑11**: consistencia del cálculo **finitario**, la hipótesis **mínima**. P‑4 |
| **`ConsistentOmega`** | `¬ (axioms ⊢ ⊥)` | ⚠️ **NO es «Q++ es consistente»**. Como `axioms ⊢` es **completo**, dice que una **compleción completa** lo sea — cercano a suponer **solidez**. 🔶 **Ya no aparece en los enunciados cabecera**; `consistentH_of_omega` la transfiere si un consumidor la tiene. [ADR‑024](DECISIONS.md) |
| **`OmegaConsistent`** | no probar `∃A` refutando todos los testigos estándar | la ω‑consistencia, **estrechada** por [ADR‑022](DECISIONS.md) a testigos con forma de línea |
| **`NegVerifier`** | Δ₀‑completitud negativa del verificador | ⛔ **la única obligación abierta de `⊬¬G`**, reducida a dos deudas con nombre |

🏁 **P‑4 RESUELTO el 2026‑09‑11**: **sí bastaba**. Con el punto fijo ya sobre `Prf`, los dos
teoremas salen en cuatro líneas con `ConsistentH`, y el footprint cae a **un solo axioma del
proyecto**. La hipótesis de la cadena de Gödel es hoy **la mínima honesta**.

---

## 4 · Los **3** `axiom` de Lean — la otra clase de hipótesis

| axioma | qué es | ¿retirable? |
|---|---|---|
| `ax_induction_prim` | el esquema de inducción sobre los 24 primitivos | ⛔ no: **es lo que `Full` significa** |
| `ax_list_induction` | ídem, listas | ⛔ no |
| ~~`ax_p_tfa`~~ | teorema fundamental de la aritmética | 🗑️ **RETIRADO el 2026‑09‑12**. Medido HUÉRFANO: cero consumidores, y `IsFactorization` no aparecía ni una vez fuera de `Block8.lean`. ⚠️ Y con él cae una afirmación **medible‑mente falsa**: `tfa_numeral` **NO** es «la realización real» — tiene otro dominio (`Nat` vs `Term`), otra unicidad (`Perm` vs igualdad objeto) y otra hipótesis (meta vs objeto) |
| `ax_axiomsCodeT_eq` | ancla de codificación (⊢) | ⬜ frente abierto. ⭐ **Ya NO está en el footprint de Gödel I/II** desde P‑4 |
| ~~`prf_axiomsCodeT_eq`~~ | ancla de codificación (`Prf`) | 🗑️ **RETIRADO el 2026‑09‑12**: ya no es `axiom`, es la **clase `AnclaEq`** ([ADR‑026](DECISIONS.md)). ⚠️ **No desapareció el supuesto** — cambió de sitio: del footprint a la **firma** de los teoremas que lo necesitan. Ver §1 |

**Ninguno es gödeliano**: D1, D2 y D3 son teoremas.

⭐⭐ **Y por qué se retiró, que es lo que importa**: un `axiom` de tipo `Prf …` **HABITA el inductivo
`Prf`**, y por **M‑11** eso prohíbe demostrar nada sobre `Prf` por inducción — pero el árbol lo hacía
**tres veces** (`prf_to_derives`, `prf_to_prfH`, `prf_to_derivation`), y D1 **se aplicaba al propio
postulado**. ⚠️ `#print axioms` **no detecta** esa clase: los tres tenían footprint limpio y eran
**injustificados**. Como hipótesis, `Prf` queda sin ningún axioma habitándolo y las tres inducciones
pasan a ser legítimas.

---

**Véase también:** `PLAN-PRUEBAS.md` §4 (lo que ningún control garantiza),
`doc/AUDITORIA-2026-09-11.md` F‑1, `DECISIONS.md` ADR‑022/023/024.
