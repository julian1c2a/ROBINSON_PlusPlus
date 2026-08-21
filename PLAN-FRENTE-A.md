# FRENTE (a) — ¿vuelve la capa rastreada? (D3 y Gödel II)

**Abierto:** 2026‑08‑19, tras ejecutar la reparación (`master`, HEAD `d6552b9`, 85 jobs).
**Contexto:** `cuarentena/README.md`, `sondeos/PilotoRastreada.lean`, `PLAN-SORTES.md`.

---

## La pregunta

Retirar `ax_tc_cons` dejó 31 módulos en `cuarentena/`. **¿Se pueden recuperar sin reintroducir la
inconsistencia?** La vía candidata es probar la **Σ₁‑completitud internalizada** con **inducción
interna** en vez de con la ecuación `tc` sintáctica.

**La herramienta existe**: `PrfH.ind`/`PrfH.listInd` (`Meta/HilbertDeduction.lean:32‑41`) y su
eliminador `prf_nat_induction` (`Meta/NatArithPrf.lean:44`) **sobrevivieron** a la cuarentena.

---

## Resultado 1 · `Sigma1CorePrf` es el KEYSTONE

Medido sobre el grafo de importaciones de `cuarentena/`: **los 24 módulos no‑raíz dependen de
`Sigma1CorePrf`. Todos, sin excepción.** No hay ninguno recuperable de forma independiente.

⟹ **Cualquier recuperación empieza necesariamente por ahí.**

## Resultado 2 · La cuarentena se parte en DOS niveles, y sólo uno es un muro

| nivel | módulos | qué usan | ¿lo cubre la vía numeral? |
|---|---|---|---|
| **1 — argumentos CONCRETOS** | `Sigma1CorePrf`, `InAxiomsCodePrf`, `D3InDotPrf` | `prf_tc_form` / `prf_tc_of_cons` sobre `formCode φ` y `objList cs` (**estructura concreta**) | ✅ **SÍ** |
| **2 — argumentos ABSTRACTOS** | `EvalListPrf`, `EvalNthcPrf`, `CodeCtorKit`, `LineWFTrackedPrf` | `prf_tc_cons' h t` con `h`,`t` **abstractos** | ⛔ **el muro** |

### Por qué el nivel 1 sí sale

Los usos son del patrón `Prf (tcFn X =eq termCode X)` con `X` de estructura concreta. La vía numeral
da el mismo puente con el **código estático cambiado**:

```lean
prf_formCode_numeral φ : Prf (formCode φ =eq numeral (codeNat φ))   -- YA demostrado, net-0
prf_tc_numeral N       : Prf (tcFn (numeral N) =eq termCode (numeral N))
⟹ tcFn (formCode φ) =eq termCode (numeral (codeNat φ))
```

Lo que cambia es **el código estático dentro de los enunciados** (`termCode (formCode φ)` pasa a
`termCode (numeral (codeNat φ))`), y `provCode_transfer` (`Meta/DiagonalNumeral.lean`) puentea las
dos representaciones en **un** paso de Leibniz.

### Por qué el nivel 2 es un muro

`pcc_eval_carc (h t)` necesita `tcFn (cons h t) =eq consT (tcFn h) (tcFn t)` con `h`,`t`
**abstractos**. Medido en `sondeos/PilotoRastreada.lean`: bajo la lectura numeral eso daría un
código de cabeza `⌜σ⌝` igual a uno de cabeza `⌜::⌝`. **Es falso, no sólo indemostrable.**

---

## El plan

### (a.1) — Refundar `Sigma1CorePrf` con códigos estáticos numerales

Bounded y mecánico: sustituir `prf_tc_form φ` por la cadena numeral, y propagar el cambio de código
estático por los enunciados. **Desbloquea estructuralmente los 24 módulos no‑raíz.**
Después, igual con `InAxiomsCodePrf` y `D3InDotPrf`.

⚠️ **Cambia enunciados**, no sólo pruebas: hay que revisar que lo que consume cada lema siga
encajando, o componer con `provCode_transfer`.

### (a.2) — El muro: la Σ₁‑completitud internalizada

El objetivo exacto:

```lean
pcc_dot_cons (h t : Term) :
    Prf (provFromCode (eqCodeFn (tcFn (cons h t)) (consT (tcFn h) (tcFn t))))
```

o sea `⊢ Prov(⌜ (cons h t)˙ = cons(ḣ, ṫ) ⌝)` — el `prf_cons_eval` **internalizado y para argumentos
abstractos**. Con él, `pcc_eval_carc` se reconstruye como `pcc_axiom_inst ax_carc` + este puente, y
los 4 módulos del nivel 2 vuelven.

**La escalera propuesta**, cada peldaño por `prf_nat_induction`:

```
Prov(⌜ ẋ + ẏ = (x+y)˙ ⌝)        ← inducción en y; usa ax_tc_succ y x + σy = σ(x+y)
Prov(⌜ ẋ · ẏ = (x·y)˙ ⌝)        ← inducción en y, apoyada en la anterior
Prov(⌜ div2(ẋ) = (div2 x)˙ ⌝)
Prov(⌜ (cons h t)˙ = cons(ḣ,ṫ) ⌝)   ← de las anteriores vía cpOf
```

**El primer peldaño (`+`) es el sondeo decisivo**: si sale, la escalera es viable y (a) también; si
bloquea, D3 y Gödel II quedan fuera por esta vía.

⚠️ **Prerrequisito práctico:** `pcc_axiom_inst` (`cuarentena/MpCodePrf.lean`) y `eqCodeFn`
(`cuarentena/Sigma1AtomPrf.lean`) están en cuarentena, y ambos dependen de `Sigma1CorePrf`.
**Por eso (a.1) va antes que (a.2)**: sin él, (a.2) ni siquiera se puede enunciar con la maquinaria
existente.

---

## Estado

### ✅ (a.1) — HECHO (2026‑08‑19). Build **95 jobs**, cuarentena **31 → 21**.

`Sigma1CorePrf` refundado con códigos estáticos numerales, net‑0. Tres declaraciones cambiadas:

| antes | ahora |
|---|---|
| `prf_provCodeC'_In_formCode_of_tracked` vía `prf_tc_form` | vía `prf_tc_numeral`; ⚠️ concluye sobre `In (numeral (codeNat φ)) L` |
| `prf_tc_objList` vía `prf_tc_of_cons` | `prf_objList_numeral` vía `prf_cons_eval_of` |
| `prf_tc_objList_formCode` | idem, con `termCode (numeral N)` a la derecha |

**Recuperados además 9 módulos** que sólo dependían del keystone: `EvalArithPrf`, `ExIntroCodePrf`,
`ForallElimCodePrf`, `LineWFCases`, **`MpCodePrf`** (`pcc_axiom_inst`), `OmegaReflect`,
**`Sigma1AtomPrf`** (`eqCodeFn`), `Sigma1TrackedPrf`, `TrackedCorePrf`.
⇒ **el prerrequisito de (a.2) ya está cubierto.**

`OmegaReflect` necesitó un añadido: `goedel_first_undecidable_numeral` (análogo de
`goedel_first_undecidable_real'`, retirado con el punto fijo roto), y reapuntar a `godelCN`.

### ▶ (a.2) — **la escalera está a mitad, y mejor de lo estimado**

Al recuperar `EvalArithPrf` de la cuarentena apareció que **el primer peldaño YA ESTABA HECHO**, y
justo por la técnica propuesta (`prf_nat_induction`):

```lean
evalAddCode a b = eqCodeFn (addcT (tcFn a) (tcFn b)) (tcFn (add a b))
pcc_eval_add (a b) : Prf (provFromCode (evalAddCode a b))     -- ∀ a b ARBITRARIOS
```

o sea `⊢ Prov(⌈ ȧ + ḇ = (a+b)˙ ⌉)`. Footprint verificado tras la reparación:
`[propext, choice, Quot.sound, prf_axiomsCodeT_eq]` — **sin `tc_cons`**. Son ~440 líneas
(`Meta/EvalArithPrf.lean`) y sirven de **plantilla exacta** para los demás peldaños.

Y el peldaño `div2` **no necesita inducción**: `pcc_thm_inst` internaliza cualquier teorema‑∀
OBJETO, y `prf_div2_double` (de `Div2ParityPrf`) sube a ∀ objeto con `Prf.gen`
(`sondeos/Div2Gen.lean`, net‑0):

```lean
prf_div2_double_all : Prf (∀. div2 (· · two) =eq ·)      -- Prf.gen, net-0
pcc_thm_inst : ∀ φ, Prf (∀. φ) → ∀ w, Prf (provFromCode (substfc zero w (formCode φ)))
```

#### Estado de la escalera

| peldaño | estado |
|---|---|
| `Prov(⌈ ẋ + ỳ = (x+y)˙ ⌉)` | ✅ **HECHO** (`pcc_eval_add`) |
| `Prov(⌈ ẋ · ỳ = (x·y)˙ ⌉)` | ⏳ por construir, **plantilla en `EvalArithPrf`** |
| `div2` | ✅ **resuelto por atajo** (`Prf.gen` + `pcc_thm_inst`), sin inducción |
| `Prov(⌈ (cons h t)˙ = cons(ḧ,ṫ) ⌉)` | ⏳ ensamblaje vía `ax_L0_cons_def` + `cpOf` |

#### Lo que queda enunciable ahora

Quedan **6 raíces** en cuarentena: `CodeCtorKit`, `D3InDotPrf`, `EvalListPrf`, `EvalNthcPrf`,
`InAxiomsCodePrf`, `LineWFTrackedPrf`. Y **`EvalListPrf` es el nuevo keystone**: bloquea a 9 de los
15 no‑raíz restantes.

El objetivo sigue siendo `pcc_dot_cons`, y **ahora SÍ se puede enunciar**, porque `pcc_axiom_inst`
y `eqCodeFn` han vuelto.

### ⚠️ Trampa encontrada al ejecutar (a.1)

`lake build` dio **verde con 85 jobs** después de mover 9 módulos a `Meta/`… porque los `import`
en `Meta.lean` **no se habían escrito**: la `lean_lib` sólo construye lo **alcanzable desde el
módulo raíz**, así que los ficheros estaban en el sitio pero fuera del build. **Señal de alarma:
el número de jobs NO cambió al añadir módulos.** Comprobar siempre que el conteo se mueve.
