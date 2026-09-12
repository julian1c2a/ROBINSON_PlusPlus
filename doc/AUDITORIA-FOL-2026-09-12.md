# AUDITORÍA UNIFICADA DE FOL — y su engarce con ROBINSON_PlusPlus

**Fecha:** 2026‑09‑12 · **Autor:** auditoría automatizada, síntesis · **Alcance:** los dos repos hermanos
`E:/dropbox/github/lean4/FOL` (HEAD `ef54c6f`, árbol limpio) y `E:/dropbox/github/lean4/ROBINSON_PlusPlus`
(HEAD `47d7348`, **un fichero modificado sin commitear**).

> ## Cómo leer este documento
>
> * Cada afirmación va marcada **[medido]** o **[hipótesis]**. *Medir una obstrucción no es probarla*, y
>   *un veredicto sobre una ruta de prueba es hipótesis mientras no compile*.
> * Este documento **sintetiza cinco dimensiones de auditoría** (`docs-fol`, `inventario-fol`,
>   `patron-axioma-inductivo`, `engarce`, `axiomas-fol`) más una pasada de crítico de completitud. Los
>   hallazgos que un refutador tumbó **no aparecen**; las gravedades son las **ya corregidas** por los
>   refutadores, no las originales.
> * ⚠️ **Colisión de identificadores en el material de partida**: dos dimensiones distintas usaron los IDs
>   `FOL-AX-1..6`. Aquí se renumeran: los de la dimensión del patrón inductivo son **`PAT-n`**, los del
>   censo de axiomas son **`AX-n`**. Los `FOL-D2-*`, `FOL-D4-*`, `ENG-*`, `CC-*`, `META-1`, `WL-1` y
>   `RPP-AX-*` conservan su nombre.
>
> ### ⚠️ EL ÁRBOL SE MOVIÓ DOS VECES DURANTE ESTA AUDITORÍA — y eso es un dato, no una nota al pie
>
> 1. **FOL, commit `ef54c6f`, ya empujado** [medido: `git log`, `git status -sb`]. Retira los **seis**
>    `axiom` del bloque `subst_lift_cancel_formula`/`subst_distrib_and`/`lift_distrib_and` en `FOLPure` y
>    `FOL_poli`, portando la corrección que `FOL/` hizo el 2026‑06‑23. **El censo pasa de 34 a 28**, y la
>    inconsistencia conocida más antigua del ecosistema queda cerrada en las cuatro librerías.
>    ⛔ Pero **sigue sin verificarse por build**: FOLPure y FOL_poli no tienen target (ver §1.3). *Está
>    escrito y compilable en apariencia; que tipe no lo ha medido nadie.* [hipótesis]
> 2. **RPP, sin commitear, INCOMPLETO** [medido]. `Meta/Representability2Prf.lean` ha dejado de declarar
>    `axiom prf_axiomsCodeT_eq` y lo ha sustituido por `class AnclaEq : Prop where eq : Prf (…)`
>    (ADR‑026, anunciado en el docstring). Estado real medido: `AnclaEq` aparece **en un solo fichero**
>    (9 menciones), `ADR-026` **no existe todavía en `DECISIONS.md`**, y quedan **117 referencias** a
>    `prf_axiomsCodeT_eq` en 67 ficheros — **dos de ellas a nivel de término en producción**
>    (`Meta/InAxiomsCodePrf.lean:308` y `:317`). ⇒ **el árbol de RPP no construye ahora mismo**
>    [medido por grep; no compilado]. Ninguna cifra de «145 jobs verdes» describe el estado de hoy.
>
> Ese refactor es **la reparación correcta de M‑11 sobre `Prf`** y a la vez **crea el agujero de §6.2**.
> Es el hallazgo más importante de esta síntesis y está en **CC‑03 / AX‑NUEVO‑1**.

---

## 1. QUÉ HAY EN FOL

### 1.1 Las cinco `lean_lib` — medido el 2026‑09‑12 contra `ef54c6f`

`lakefile.lean` declara cinco `lean_lib` y **una sola** `@[default_target]`: `FOL`. `make build` = `lake build`
= sólo esa. Consecuencia medida: **cuatro de las cinco librerías no se han compilado nunca en este checkout**.

| `lean_lib` | módulos `.lean` | líneas | `axiom` | `.olean` de módulo | consumidores | estado |
|---|---:|---:|---:|---:|---|---|
| **`FOL`** ⭐ `@[default_target]` | 14 | 2.432 | **13** | **11** (3 huérfanos) | RPP (10 módulos) | **VIVA** — la única |
| `FOLPure` | 12 | 1.896 | 5 | **0** | ninguno | MUERTA (sin build) |
| `PropLogic` | 11 | 1.064 | 3 | **0** | ninguno | MUERTA (sin build) |
| `TheoryFramework` | 8 | 428 | **0** | **0** | ninguno | MUERTA (sin build) — ver ⚠️ |
| `FOL_poli` | 16 | 2.336 | 7 | **0** | ninguno | MUERTA — **clon**: `FOL_poli/FOL.lean` es **byte‑idéntico** a `FOL/FOL.lean` |
| *(`cuarentena/`, fuera del lakefile)* | 4 | 304 | 0 | — | — | apartada 2026‑09‑11 |
| **TOTAL** | **61 + 5 barrels + 4** | **≈ 8.460** | **28** | **11 + 1 barrel + 4 huérfanos** | | |

* **0 `sorry`, 0 `admit`, 0 `native_decide`** en todo el árbol [medido; el único acierto del grep es la
  palabra «adm**ite**» dentro de un comentario de `cuarentena/Inconsistencia.lean:11` — lo que de paso
  mide que `check-sorry.bash`, que hace `grep -c 'sorry'` sin delimitar palabra, es frágil por
  construcción].
* `lean-toolchain` = **v4.31.0** [medido].
* ⚠️ **El `0 axiom` de `TheoryFramework` es engañoso**: no declara ninguno, pero **postula la solidez y la
  completitud como campos de clase**. Ver §2.4 y §6.2.

### 1.2 La librería viva, fichero a fichero [medido]

| fichero | líneas | `axiom` | ¿`.olean`? | qué provee |
|---|---:|---:|:--:|---|
| `FOL/FOL.lean` | 225 | 0 | ✅ | `Term`, `Formula`, `Derives` (**18 constructores**), `substFormula`/`liftFormula`, toda la notación. **0 `namespace`** ⇒ vuelca 15 nombres + 3 definiciones de ejemplo en la raíz del entorno de RPP |
| `FOL/MetaRules.lean` | 150 | **6** | ✅ | `imp_intro`:67, `gen`:87, `raa`:92, `dne`:100, `or_elim`:124, `ex_elim`:138 — **los seis que llegan al footprint de RPP** |
| `FOL/Deduction.lean` | 30 | 0 | ✅ | `deduction_theorem`. RPP lo importa **28 veces** y **no usa su único export** |
| `FOL/Tactics.lean` | 52 | 0 | ✅ | `derive_hyp`, `derive_weaken`, `derive_raa`. ⛔ `derive_raa` expande a `apply Derives.raa` y **`Derives.raa` no existe** (18 constructores, ninguno se llama `raa`) [medido] |
| `FOL/Semantics.lean` | 343 | 0 | ✅ | `Model`, `satisfies`. **Existía desde mayo y nadie lo importaba**; es lo que permitió `prf0_soundness` en RPP |
| `FOL/Completeness.lean` | 702 | **5** | ✅ | modelo canónico, Lindenbaum, `completeness`. **CERO consumidores reales** |
| `FOL/Theorems/Eq.lean` | 308 | 0 | ✅ | igualdad. ⚠️ **No está en el barrel**: se compila sólo porque `Completeness` lo importa. RPP lo importa **20 veces** |
| `FOL/Theorems/Neg.lean` | 99 | **1** | ✅ | `dne` **esquema** (:57) — el segundo `dne` del repo |
| `FOL/Theorems/Quantifiers.lean` | 186 | **1** | ✅ | `forall_not_impl_exists_not` (:115); y el `subst_lift_cancel_formula` **ya reparado** (:57) |
| `FOL/Theorems/Impl.lean` | 74 | 0 | ✅ | — |
| `FOL/Theorems/Derived.lean` | 191 | 0 | ✅ | — |
| `FOL/Classical.lean` | 4 | 0 | ⛔ **HUÉRFANO** | nada; no lo alcanza ningún barrel |
| `FOL/Tactics2.lean` | 47 | 0 | ⛔ **HUÉRFANO** | redefine `derive_hyp`/`derive_weaken` — **colisiona** con `Tactics.lean` |
| `FOL/Theorems/Deduction.lean` | 21 | 0 | ⛔ **HUÉRFANO** | `deduction_theorem` **duplicado palabra por palabra** |

Los tres huérfanos **compilan limpios uno a uno** [medido en la auditoría previa con `lake env lean`], y
ninguno declara axiomas — por eso su gravedad es BAJA. Lo que no es bajo es que **`make root` los metería
dentro** (§4.1, AX‑10/CC‑08).

### 1.3 Doc y controles de FOL [medido]

* **16 ficheros `.md`**. Los cinco titulares (`README`, `CURRENT-STATUS-PROJECT`, `REFERENCE`,
  `NEXT-STEPS`, `PLANNING`) están fechados **2026‑05‑16** y publican como **hito demostrado** justo lo que
  hoy está medido FALSO: la solidez.
* **No existe `FOL/AXIOMS.md`**, ni ningún equivalente al de RPP.
* **7 scripts `.bash`, ninguno mira la documentación**. `grep -ln axiom *.bash` → **vacío**: ningún control
  del repo cuenta `axiom`.
* El único control de deuda, `check-sorry.bash`, da **VERDE (0)** con **28 `axiom` en el árbol**.
* **No hay `.github/`**: FOL **no tiene CI propia**.

---

## 2. EL ESTADO UNIFICADO FOL + RPP

### 2.1 El cuadro único: dónde está cada cosa y de qué depende

```
                         ┌──────────────────────────────────────────────┐
  E:/…/FOL               │ lakefile: 5 lean_lib, 1 @[default_target]     │
  (paquete `FOL`)        │ salida ÚNICA: FOL/.lake/build/lib/lean/       │  ← un solo directorio
                         └──────────────────────────────────────────────┘
                                        │ LEAN_PATH de RPP  [medido: lake env]
   ┌────────────────────────────────────┴──────────────────────────────────────┐
   │  VIVO Y CONSUMIDO          │  VIVO Y NO CONSUMIDO   │  SIN BUILD           │
   │  FOL.FOL            (42×)  │  FOL.Completeness      │  FOLPure      (5 ax) │
   │  FOL.Theorems.Neg   (28×)  │    5 ax, 0 consumidores│  PropLogic    (3 ax) │
   │  FOL.Deduction      (28×)  │  FOL.Classical    HUÉRF│  TheoryFramework(0 ax│
   │  FOL.Theorems.Impl  (27×)  │  FOL.Tactics2     HUÉRF│    pero `sound` como │
   │  FOL.Theorems.Derived(27×) │  FOL.Th.Deduction HUÉRF│    CAMPO de clase)   │
   │  FOL.Theorems.Quant.(25×)  │                        │  FOL_poli     (7 ax) │
   │  FOL.Tactics        (22×)  │  cuarentena/ (4 mód.)  │  ── 15 ax en código  │
   │  FOL.Theorems.Eq    (20×)  │   Soundness, Compacity │     que nada compila │
   │  FOL.MetaRules       (1×)  │   Theorems_Soundness   │                      │
   │  FOL.Semantics       (1×)  │   Inconsistencia       │                      │
   └────────────────────────────┴────────────────────────┴──────────────────────┘
        │  6 axiom entran al footprint          0 entran            0 entran
        ▼
  E:/…/ROBINSON_PlusPlus — 132 módulos + 64 sondeos + 331 Probe
        `require FOL from "../FOL"` · NUNCA `import FOL` a secas [medido: 0 apariciones]
```

**Superficie del engarce, medida** [ENG‑13, re‑medida hoy]: RPP importa **10 de los 14** módulos de la
librería `FOL` con las cuentas de arriba, y **ninguno** de las otras cuatro librerías (`grep '^import
(FOLPure|PropLogic|TheoryFramework|FOL_poli)'` → vacío). De ~65 símbolos exportados usa **33**.

**Tres cosas que la documentación no dice y que este cuadro sí** [medido]:

1. **`FOL.Theorems.Eq` no está en el barrel** y sólo entra al build porque `FOL.Completeness` lo importa.
   ⇒ **si se retirase `Completeness`, los 20 módulos de RPP que importan `FOL.Theorems.Eq` dejarían de
   construir.** Nadie lo ha escrito y es una dependencia de verdad.
2. La protección de RPP frente a la cuarentena **no es el borrado del fichero**: es el hecho contingente de
   que ningún módulo escribe `import FOL` a secas. **Nada lo impide** (FOL‑D2‑14).
3. Las cinco librerías **comparten directorio de salida**, y ese directorio entero está en el `LEAN_PATH`
   de RPP (CC‑01). Hoy `import FOLPure` **falla** [medido: *object file … does not exist*], pero sólo
   porque sus `.olean` de contenido no existen. **Un solo `lake build FOLPure` reabre la puerta**, y el
   control `[F]` no lo vería.

### 2.2 Censo de axiomas de LOS DOS REPOS, junto [medido 2026‑09‑12]

**FOL — 28** (13 + 5 + 3 + 0 + 7). **RPP — 4 hoy en el árbol de trabajo**, 5 en HEAD y 5 en la doc.

| # | axioma | fichero:línea | forma | habita | ¿inevitable? | footprint RPP |
|---|---|---|---|---|---|---|
| **GRUPO 1 — `FOL/MetaRules.lean`: los 6 que SÍ llegan a RPP** ||||||
| 1 | `imp_intro` | MetaRules:67 | `(Γ⊢A → Γ⊢B) → Γ⊢(A⇒B)` | `Derives` | **SÍ** — no positiva | **182** ctes / 73 mód. |
| 2 | `gen` | MetaRules:87 | `(∀ n:Term, Γ⊢A[n]) → Γ⊢∀A` | `Derives` | **NO** ⛔ | **193** / 69 |
| 3 | `raa` | MetaRules:92 | `(Γ⊢A → Γ⊢⊥) → Γ⊢¬A` | `Derives` | **SÍ** | **45** / 19 |
| 4 | `dne` (regla) | MetaRules:100 | `Γ⊢¬¬A → Γ⊢A` | `Derives` | **NO** — y **redundante** | **71** / 13 |
| 5 | `or_elim` | MetaRules:124 | premisas `Γ⊢A → Γ⊢C` | `Derives` | **SÍ** | **105** / 26 |
| 6 | `ex_elim` | MetaRules:138 | `∀t, Γ⊢A[t] → Γ⊢C` | `Derives` | **SÍ** | **106** / 31 |
| **GRUPO 2 — esquemas de `FOL/Theorems/`: habitan `Derives`, 0 en RPP** ||||||
| 7 | `Neg.dne` (esquema) | Neg:57 | `Γ ⊢ (¬¬A ⇒ A)` | `Derives` | **NO** (nulario) | **0** — único uso `Completeness:680` |
| 8 | `forall_not_impl_exists_not` | Quantifiers:115 | `Γ ⊢ (¬∀A ⇒ ∃¬A)` | `Derives` | **NO** (nulario) | **0** — único uso `Completeness:519` |
| **GRUPO 3 — `FOL/Completeness.lean`: 5, ninguno llega a RPP** ||||||
| 9 | `formula_enum` | Completeness:119 | `Nat → Formula` | `→` | **NO — derivable, COMPILADO** (94 líneas) | 0 |
| 10 | `formula_enum_surj` | Completeness:120 | `∀f, ∃n, enum n = f` | `Exists` | **NO — derivable, COMPILADO** | 0 |
| 11 | `termEqv_func_congr` | Completeness:389 | congruencia `func` | — | derivable en principio, **no medido** | 0 |
| 12 | `termEqv_rel_congr` | Completeness:392 | congruencia `atom` | — | derivable en principio, **no medido** | 0 |
| 13 | `henkin_extension_lemma` | Completeness:657 | extensión maximal+Henkin | — | **el único caro de verdad** | 0 |
| **GRUPO 4 — las cuatro librerías sin build: 15 axiomas, 0 consumidores, 0 `.olean`** ||||||
| 14‑28 | FOLPure 5 · PropLogic 3 · FOL_poli 7 | — | el mismo reparto `formula_enum`/`…_surj`/`henkin`/`dne`/`forall_not…` | — | — | **0** |
| **RPP — los `axiom` del proyecto** ||||||
| R1 | `ax_induction_prim` | `Full/Induction.lean:251` | `primAxioms ⊢ inductionFormula φ` | `Derives` | habitante simple | — |
| R2 | `ax_list_induction` | `Full/Lists.lean:55` | `step : ∀h t, Γ⊢φ t → Γ⊢φ(cons h t)` ⇒ **premisa‑FUNCIÓN** + conclusión `∀ L:Term` | `Derives` | **SÍ** (no positiva) ⛔ | — |
| R3 | `ax_axiomsCodeT_eq` | `Minimal/Axioms.lean:1594` | `axioms ⊢ (…)` | `Derives` | habitante simple | — |
| R4 | `ax_p_tfa` | `Minimal/Theorems/Block8.lean:302` | concluye **dentro de un `∃`** | `Derives` | habitante simple | — |
| ~~R5~~ | ~~`prf_axiomsCodeT_eq`~~ | `Meta/Representability2Prf.lean` | **RETIRADO hoy** → `class AnclaEq` | `Prf` | ver ⚠️ §6.2 | era el ÚNICO del footprint de Gödel |

**Cifras de cabecera del censo unificado:**
de los **28 de FOL**, ⇒ **4 son inevitables** (premisa no positiva), **2 medidos como derivables**,
**1 redundante**, **4 más podrían ser constructores**, **1 caro de verdad**, **15 en código sin build**.
Y **sólo 6 llegan al footprint de RPP** [medido: barrido de `collectAxioms` sobre las **4.786 constantes**
de `ROBINSON_PlusPlus`, `EXIT=0`].

### 2.3 Lo que queda medido sobre Gödel

Antes del refactor en vuelo: `goedel_first_prf` y `goedel_second_prf` →
`[propext, Classical.choice, Quot.sound, prf_axiomsCodeT_eq]` — **ningún axioma de FOL**, confirmado
compilando. ⇒ La cadena de Gödel **no depende de `MetaRules`**, y ésa es la arquitectura correcta:
`⊢` como herramienta, `Prf` como sujeto. Ver §6.2 para lo que esa cifra va a pasar a decir.

### 2.4 El hallazgo que el censo de `axiom` no ve: `TheoryFramework`

`TheoryFramework` declara **0 `axiom`** y alberga **la hipótesis no descargada más grande de los dos
repos** [medido, leído hoy]:

```lean
class LogicSystem (F : Type) where
  derives, bottom, neg, semanticEntails …
  sound    : ∀ {Γ f}, derives Γ f → semanticEntails Γ f   -- ← para FOL: medido FALSO
  complete : ∀ {Γ f}, semanticEntails Γ f → derives Γ f
```

y **deriva de ella**: `MetaTheorems.proves_iff_models (T) (f) : T.proves f ↔ T.models f` —
demostrabilidad ⇔ verdad, para cualquier teoría sobre cualquier instancia— y `models_monotone`, que pasa
por el ida y vuelta de ese bicondicional. La cabecera del fichero anuncia: *«These are provable once and
apply to PropLogic, FOLPure, and FOL^= automatically»*.

Y `TheoryFramework/Instances/FOL.lean` rellena ese campo con `sound := @FOL.Metamath.Soundness.soundness`
— **namespace que dejó de existir el 2026‑09‑11** al mover el fuente a `cuarentena/`. El fichero se
autodescribe *«This instance is fully complete and verified»* (:9). **No lo compila ningún build**: el
barrel `TheoryFramework.lean:14-18` excluye `Instances/` a propósito, y una `lean_lib` sólo cubre el
cierre de imports del módulo raíz. ⇒ es **el único consumidor de `soundness` y `completeness` de los dos
repos**, está roto, y nada lo nota.

---

## 3. ⛔ LISTA NEGRA / LISTA BLANCA DE INDUCTIVOS

> **M‑11 (ADR‑025).** Un `axiom` que **HABITA** un tipo inductivo prohíbe demostrar nada sobre ese tipo
> por **eliminación**. Los habitantes que produce el axioma no son aplicaciones de constructor; la
> eliminación cubre los constructores y el teorema cuantifica sobre **todos** ⇒ el teorema es FALSO.
> Es **eliminar** lo peligroso, no introducir.

### 3.1 LISTA NEGRA — prohibido eliminar

| inductivo | ctores | habitantes‑axioma | n | detonado |
|---|---:|---|---:|---|
| **`FOL.Derives`** | 18 | `MetaRules`: `imp_intro`, `gen`, `raa`, `dne`, `or_elim`, `ex_elim` · `Theorems/Neg.lean:57`: `dne` esquema · `Theorems/Quantifiers.lean:115`: `forall_not_impl_exists_not` | **8 en FOL** | **SÍ** — `FOL.soundness` daba `False` sin hipótesis, footprint `[propext, raa]` |
| | | ＋ RPP: `ax_induction_prim`, `ax_list_induction`, `ax_axiomsCodeT_eq`, `ax_p_tfa` | **12 con RPP** | |
| `FOLPure.Derives` | — | `Theorems/Neg.dne`, `Theorems/Quantifiers.forall_not…` | 2 | NO — `FOLPure/Soundness.lean:26` induce sobre él, pero **no hay `raa`** que ceba el detonador |
| `PropLogic.Derives` | — | `Theorems/Neg.dne` | 1 | NO — ídem, `PropLogic/Soundness.lean:27` |
| `FOL_poli.Derives` | — | `Theorems/Neg.dne`, `Theorems/Quantifiers.forall_not…` | 2 | NO — ídem, `FOL_poli/Soundness.lean:30` |
| ~~`Prf`~~ (RPP, 7 ctores) | 7 | ~~`prf_axiomsCodeT_eq`~~ | ~~1~~ → **0** | **RESUELTO hoy** por ADR‑026 (en vuelo) — ver ⚠️ |
| `Formula` / `Eq` (FOLPure, FOL_poli) | — | `subst_lift_cancel_formula` | 0 | **RESUELTO** por `ef54c6f` |

### 3.2 LISTA BLANCA — eliminación segura [medido]

**RPP, 9 de 10 inductivos de producción**: `Prf₀` (17 ctores), `PrfH` (8), `Rule` (21), `CTree`, `STree`,
`Sym`, `GuardSlot`, `IsCodeShaped`, `StdArgs`. El décimo era `Prf`; con ADR‑026 pasa a la blanca y son
**10 de 10**.
**FOL**: `Term`, `Pos`, `LocalRule`, `PointwiseEqv`, `Model` (structure), `Theory` (structure).

### 3.3 ⛔⛔ LA CORRECCIÓN DE FONDO A M‑11: sólo CUATRO de los ocho son inevitables

La doctrina escrita hoy —ADR‑025, `FOL/MetaRules.lean:16-17`, `cuarentena/README.md`,
`sondeos/AnclaSoundness.lean:36`— justifica los ocho así: *«tienen que ser axiomas, porque sus premisas
son funciones de Lean, ocurrencias negativas que Lean rechazaría en un `inductive`»*.
**Eso es cierto para cuatro y FALSO para los otros cuatro.**

**[MEDIDO — reproducido independientemente en esta pasada, `lake env lean` desde la raíz de RPP]:**
compilé un `inductive D : List Formula → Formula → Prop` con `gen`, `dne` (regla), `dne` (esquema) y
`forall_not_impl_exists_not` **como CONSTRUCTORES** y el kernel lo **ACEPTA**: `EXIT=0`, y `#check @D.rec`
imprime el recursor con un caso por cada uno, **incluido el de `gen` con su hipótesis de inducción
infinitaria** `(∀ (n : Term), motive (substFormula 0 n A) ⋯)`. El control en dirección contraria discrimina:

```
error: (kernel) arg #4 of 'ProbeNeg.E.imp_intro' has a non positive occurrence
       of the datatypes being declared                                    EXIT=1
```

⇒ el reparto exacto:

* **INEVITABLES (4)** — el kernel los rechaza como constructor: **`imp_intro`, `raa`, `or_elim`,
  `ex_elim`**. Son los que toman `Γ ⊢ A → Γ ⊢ B`. En RPP se les añade **`ax_list_induction`**, cuyo `step`
  tiene exactamente esa forma [medido, `Full/Lists.lean:55-58`].
* **EVITABLES (4)** — el kernel los acepta: **`gen`** (premisa infinitaria pero **estrictamente
  positiva**: el dominio del `∀` es `Term`, no `Derives`), **`MetaRules.dne`** (premisa positiva simple),
  **`Theorems.Neg.dne`** y **`forall_not_impl_exists_not`** (esquemas sin premisa ⇒ constructores nularios).

**Consecuencia:** la lista negra de `Derives` en FOL **puede pasar de 8 a 4** sin cambiar una sola prueba
ni la fuerza del cálculo — las mismas reglas de inferencia, dentro de la definición inductiva en vez de
fuera. No arregla `soundness` (los cuatro inevitables bastan para el ataque de `raa`), pero **divide por
dos la superficie de la regla**. Y el coste dentro de `FOL/` es **cero pruebas tocadas**: las cuatro
`induction h with` sobre `Derives` del repo están todas **fuera** de la librería `FOL`
(`cuarentena/Soundness.lean:30`, `FOLPure/Soundness.lean:26`, `PropLogic/Soundness.lean:27`,
`FOL_poli/Soundness.lean:30`).

### 3.4 M‑11 está enunciada sólo para `induction`, y la puerta es el ELIMINADOR

Todos los enunciados de M‑11 dicen «por INDUCCIÓN» y la lista negra habla de «inducir». Pero el mecanismo
que describen es el del **eliminador**, y `induction` no es el único que lo invoca: `cases`, `rcases`,
`match h with`, `injection`, `.rec`, `.recOn`, `.casesOn`, `.noConfusion` hacen lo mismo y son igual de
inseguros. Un análisis de casos que concluya «luego `h` es uno de estos 18 constructores» es exactamente el
paso falso. **Hoy no hay violación viva** [medido] — y conviene escribirlo — pero **el enunciado no
protege** y cualquier control que grepee `induction` dará VERDE sobre un `cases` igual de roto.

### 3.5 El criterio FINO, que hay que fijar por escrito (PAT‑5)

La distinción «eliminar peligroso / introducir seguro» es correcta pero **insuficiente**: no separa `raa`
de `formula_enum`, y aplicada cruda condena media librería. El criterio que sí separa es semántico —
**un `axiom a : I …` es peligroso sólo si su enunciado es FALSO bajo la lectura de `I` como punto fijo
MÍNIMO de sus constructores** — y da **tres grados con nombre**:

* **(i) LETAL** — falso bajo punto fijo mínimo **y** algún teorema‑por‑eliminación lo distingue ⇒ teorema
  FALSO ⇒ cuarentena. (`raa`/`imp_intro`/`or_elim`/`ex_elim` + `soundness`.)
* **(ii) HUECO** — no es aplicación de constructor pero su enunciado es verdadero en el modelo
  intencionado ⇒ el teorema puede ser cierto y **la prueba no lo cubre** ⇒ cerrar el caso a mano o
  convertir el axioma en constructor. (`dne` ×2, `forall_not_impl_exists_not`, `ax_induction_prim`.)
* **(iii) BENIGNO** — habita un inductivo ajeno al razonamiento por eliminación. (`formula_enum`,
  `henkin_extension_lemma`.)

---

## 4. LAS CORRECCIONES

> ✅ **YA HECHO EL 2026‑09‑12 — no reportar como abierto.** Estos hallazgos figuraban vivos en el material
> de partida y están **cerrados** [medido]:
>
> | hallazgos | qué se hizo |
> |---|---|
> | `FOL-D2-1`, `FOL-D4-13`, `ENG-3` | **La cuarentena no era efectiva** — se borraron los `.olean` huérfanos. Verificado hoy: `import FOL.Soundness` da *object file … does not exist*, `EXIT=1` |
> | *(nuevo)* | **Control `[F]`** en `check-doc-sync.bash:338-374` — rompe si hay `.olean` sin `.lean`. Al estrenarlo aparecieron **4 fantasmas en RPP**, uno `Meta/Incompleteness` (capa Gödel LEGACY que reexponía `axiom D2` y `axiom D3`). Borrados |
> | `FOL-D2-4`, `FOL-D4-4`, `PAT-3`, `ENG-1` | **El censo de habitantes de `Derives`** corregido de 5‑9 a **8 en FOL / 12 con RPP** en `DECISIONS.md` (M‑11, ADR‑025), `NEXT-STEPS.md`, `FOL/MetaRules.lean`, `FOL/cuarentena/README.md` y `sondeos/AnclaSoundness.lean` |
> | `ENG-2` | Escrito que **mover sólo `MetaRules` no bastaría**: dejaría seis habitantes |
> | `FOL-D2-2`, `PAT-1`, `PAT-2`, `ENG-10`, `AX-7`, mitad de `FOL-D4-3` | **`ef54c6f`**: retirados los 6 `axiom` falsos de `FOLPure`/`FOL_poli`. **34 → 28**. Commiteado y **empujado** |
> | `RPP-AX-1`, `RPP-AX-2` | **En vuelo**, sin commitear: `prf_axiomsCodeT_eq` deja de ser `axiom` (ADR‑026, `class AnclaEq`). ⚠️ **Incompleto** — ver la advertencia de cabecera y §6.2 |

### 4.1 FOL — por gravedad

#### ⛔ ALTO

**A‑1 · `FOL/AXIOMS.md` no existe y ningún control cuenta `axiom`** *(AX‑1, FOL‑D2‑7, FOL‑D4‑10)*
*Hoy:* `check-sorry.bash` da VERDE con 28 `axiom`; `grep -ln axiom *.bash` → vacío. El censo **se movió
de 34 a 28 hoy mismo sin que nada lo registrara**.
*Debería:* crear `FOL/AXIOMS.md` con la tabla de §2.2, fechada, con la columna **«¿llega a RPP?»**; y añadir
a `check-sorry.bash` (o portar `check-doc-sync.bash`, que existe y está reparado en RPP) un bloque
`check-axiom` que cuente `^axiom ` **por librería** y **ROMPA** si difiere de lo escrito. Nota al pie
obligatoria: *«`FOL/Completeness.lean` sustituyó un `sorry` por **cinco `axiom`** (commit `e9580a4`,
titulado “100% sorry‑free”); el Teorema de Completitud **no está demostrado** en el sentido en que
`README.md` y `REFERENCE.md` lo publican.»*

**A‑2 · Cuatro de las cinco `lean_lib` nunca se compilan — 15 de 28 axiomas en código sin build** *(AX‑6)*
*Hoy:* `lakefile.lean` con un solo `@[default_target]`; `Makefile:8-9` `build: lake build`; **0 `.olean`**
en FOLPure, PropLogic, TheoryFramework, FOL_poli.
*Debería:* decidirlo y escribirlo (§5.1). Si se quedan: `build-all: lake build FOL FOLPure PropLogic
TheoryFramework FOL_poli` en el Makefile y ejecutarlo en el control. En cualquier caso **borrar los cuatro
`.olean` de barrel huérfanos de contenido** (`FOLPure.olean`, `PropLogic.olean`, `TheoryFramework.olean`,
`FOL_poli.olean` — siguen ahí hoy [medido]) y ampliar `[F]` para que rompa cuando un `.olean` de barrel
exista sin los `.olean` de sus imports. ⚠️ **Ésta es la causa raíz** de que `subst_lift_cancel_formula`
sobreviviera 80 días con un enunciado que el propio proyecto había declarado FALSO.

**A‑3 · Los cinco titulares publican la SOLIDEZ como hito demostrado** *(FOL‑D4‑1, ENG‑6, FOL‑D2‑10,
ENG‑14, FOL‑D4‑9)*
*Hoy:* `README.md:34` lista *«Hito 2: Teorema de Corrección: Γ⊢A → Γ⊨A»*; `REFERENCE.md` §3.10 «Status:
Completo»; `CURRENT-STATUS-PROJECT.md:33` `Soundness.lean | 1 | 0 | ✅ Complete`. Y su cabecera contradice
el árbol en cinco cifras a la vez [medido hoy]: `lean_lib 4` → **5**; `~43 módulos` → **61 + 5 barrels +
4**; `1 sorry` → **0**; `v4.28.0` → **v4.31.0**; `Prelim.lean` **no existe**; falta la fila que importa,
**`axiom` → 28**. `git show --stat 76ac56d`: el commit de cuarentena tocó 7 ficheros y **ningún documento
de estado**.
*Debería:* una sola pasada sobre los cinco, sustituyendo el hito por: *«**No hay teorema de Corrección.**
`soundness` es FALSO en presencia de `FOL/MetaRules.lean` — ver `cuarentena/README.md`. Lo único sólido
medido del ecosistema es `prf0_soundness` sobre `Prf₀`
(`../ROBINSON_PlusPlus/sondeos/AnclaSoundness.lean`).»* ⚠️ **No escribir «Axioms: ninguno»** en
`REFERENCE.md` §3.6 —lo propuso el hallazgo original y sería sustituir una mentira por otra—: el bloque
correcto es *«Axioms: ninguno en §3.6 desde `d01f0f1`; los de la librería están en `AXIOMS.md`»*.

**A‑4 · Corregir la doctrina de M‑11 en FOL: «tienen que ser axiomas» es falso para cuatro** *(AX‑3)*
*Hoy:* `FOL/MetaRules.lean:16-17`: *«No son derivables de los constructores de `Derives` (la hipótesis
meta‑función no se reduce a hipótesis‑en‑contexto…)»*; `cuarentena/README.md` y ADR‑025 lo repiten.
*Debería:* *«**CUATRO** tienen que serlo — `imp_intro`, `raa`, `or_elim`, `ex_elim`, cuya premisa
`Γ ⊢ A → Γ ⊢ B` es una ocurrencia NO POSITIVA que el kernel rechaza (**medido**). Los otros cuatro **no**:
`gen`, `dne` (regla), `dne` (esquema) y `forall_not_impl_exists_not` son shapes de constructor legales; el
kernel acepta un `Derives` que los incluya, `gen` incluido pese a su premisa infinitaria.»*

**A‑5 · `TheoryFramework/Instances/FOL.lean` está roto, se autodescribe verificado, y no lo compila nadie**
*(CC‑02, FOL‑D4‑7, FOL‑D2‑3)*
*Hoy:* `open FOL.Metamath.Soundness` (:15) y `sound := @FOL.Metamath.Soundness.soundness` (:27), namespace
inexistente; cabecera *«This instance is fully complete and verified»*.
*Debería:* o (a) **retirarlo a `cuarentena/`** con nota —es código muerto que afirma lo que el proyecto ya
midió FALSO—, o (b) añadir `globs := #[.submodules \`TheoryFramework]` a la `lean_lib` **para que el build
lo vea romperse**. Lo que no puede quedarse es la tercera opción actual.

**A‑6 · Partir `LogicSystem`: `sound`/`complete` no son parte de «ser un sistema lógico»** *(CC‑03,
FOL‑D2‑3)*
*Hoy:* `TheoryFramework/Logic.lean:30-38` los exige como campos y `MetaTheorems.lean:25` deriva
`proves_iff_models` de ellos.
*Debería:* `class LogicSystem` (derives/bottom/neg/semanticEntails) + `SoundLogic` / `CompleteLogic`
separadas; `proves_iff_models` pide las dos y queda **explícitamente condicional**, que es lo que es. Y
documentar en el docstring: *«`sound` es un CAMPO, no un teorema: el marco POSTULA la solidez de cada
instancia. Para `FOL` ese campo es indemostrable.»*

**A‑7 · `gen-root.bash` no sólo borra el aviso: AÑADIRÍA tres módulos con declaraciones duplicadas**
*(FOL‑D4‑11, AX‑10, CC‑08)*
*Hoy:* el script vuelca con `} > "$ROOT_FILE"` (sobrescritura total) y sus únicas exclusiones son `_*`,
`test*`, `Test*` (:41‑43). `make root` está en el Makefile y `README.md:130` lo documenta como paso normal.
Un `make root` (a) borra el aviso de cuarentena de `FOL.lean:22-26` y (b) pasa el barrel de **10 imports
curados a 14 alfabéticos**, metiendo `Classical`, `Tactics2` y `Theorems/Deduction` — y `Tactics2:21,:30`
redeclara `derive_hyp`/`derive_weaken` de `Tactics.lean:26,43`, importado **22 veces por RPP**, y
`Theorems/Deduction.lean:19` duplica `deduction_theorem`.
*Debería:* (a) fichero `gen-root.exclude`; (b) preservar bloques `-- BEGIN MANUAL` / `-- END MANUAL`;
(c) que el script se niegue a escribir si detecta un nombre de declaración duplicado. **Mientras no esté,
documentar `make root` como PROHIBIDO en FOL**, igual que `cd FOL && lake build`.

#### 🔶 MEDIO

**M‑1 · Los DOS `dne`: el de `MetaRules` es redundante hoy** *(AX‑4)*. Medido compilando: la regla desde el
esquema es `Derives.elim_impl Γ (neg (neg A)) A FOL.Theorems.Neg.dne h`, footprint **`[propext, dne]`** —
un axioma; la recíproca cuesta **dos**. ⇒ **el esquema es el primitivo**. `MetaRules` importa sólo `FOL.FOL`
y `Theorems/Neg` también ⇒ no hay ciclo. Efecto: **28 → 27**. ⚠️ Si además se aplica A‑4, la salida buena es
otra: `dne` esquema pasa a **constructor** y la regla es teorema por `elim_impl` — **los dos desaparecen a
la vez**.

**M‑2 · `formula_enum`/`formula_enum_surj` son derivables — COMPILADO en 94 líneas** *(AX‑5)*. Footprint
`[propext, Classical.choice, Quot.sound]`, importando **sólo `FOL.FOL`**. Efecto: **28 → 26**. ⚠️ El pago no
es gratis: la maquinaria (`triN`/`consN`/`codeNat` + inyectividad) vive hoy en RPP, que es el
**consumidor**; hay que **portarla** a un `FOL/Coding.lean` nuevo. Fichero ya compilado en
`…/scratchpad/ProbeEnum.lean`. ⚠️ De los otros tres de `Completeness` **no digo lo mismo**: los dos
`termEqv_*_congr` son *derivables en principio, no medido*, y `henkin_extension_lemma` es **el único caro
de verdad**. La doc debe distinguir esos **tres grados**, que hoy no distingue.

**M‑3 · `ENGARCE-ROBINSON-FOL.md` describe un engarce que NO EXISTE** *(ENG‑5)*. `encodeList`,
`encodeList_bijective`, `IsList`, `code_nil`/`code_cons`, el lema β y los W‑Types tienen **0 apariciones**
en RPP; su frase final —*«cada flecha es una reducción formalmente demostrada en Lean»*— es un **sobreclaim
duro**; y **nunca menciona `Derives`, `MetaRules`, `Prf` ni `⊢`**, que es el engarce que sí existe.
*Debería:* dos mitades explícitas, **§A EL ENGARCE QUE HAY (medido)** con la tabla de §2.1, y **§B
PROYECTADO (hoja de ruta, nada formalizado)**.

**M‑4 · `derive_raa` expande a `Derives.raa`, que no existe** *(ENG‑11)*. `FOL/Tactics.lean:49-52`, en un
módulo que RPP importa 22 veces; al ser `macro_rules` el error sólo aparece al invocarla. **18
constructores medidos, ninguno se llama `raa`.** *Debería:* borrarla (0 usos medidos) o reapuntarla a
`FOL.MetaRules.raa` **con el aviso de que mete el axioma en el footprint**. Y corregir `NEXT-STEPS.md:17`,
que la marca `[x]`.

**M‑5 · `FOL/FOL.lean` no declara namespace** *(ENG‑12)*. `grep -c '^namespace'` → **0** [medido]. Vuelca
15 nombres en la raíz del entorno de 132 módulos de RPP, **incluidas tres definiciones de ejemplo**
(`formula_ejemplo`, `posicion_Q`, `formula_simplificada`, 0 usos). Viola el propio ADR‑005 de FOL.
*Debería:* **(a) barato, hacerlo ya**: borrar las tres de ejemplo. **(b) caro, decisión del propietario**:
`namespace FOL` + `export`. ⚠️ *No he medido si el `export` basta para que la notación y los `.ctor`
anónimos sigan resolviendo* [hipótesis].

**M‑6 · La cita «Ver ADR‑008» apunta al ADR equivocado en los DOS repos** *(ENG‑9)*.
`FOL/MetaRules.lean:53` y `RPP/Minimal/Axioms.lean:1695` citan ADR‑008, que en los dos `DECISIONS.md` es
«Sistema de anotaciones en REFERENCE.md». El que documenta las meta‑reglas es **RPP ADR‑010**.
*Debería:* corregir las dos citas **y** añadir a los dos `DECISIONS.md`: *«ADR‑001..009 son COMUNES
(plantilla compartida); desde ADR‑010 divergen. Toda cita cruzada lleva prefijo: `FOL ADR-010` /
`RPP ADR-010`.»*

**M‑7 · Acotar bien el radio del daño y etiquetar los tres `Soundness` vivos** *(FOL‑D4‑2, FOL‑D2‑5,
PAT‑4, ENG‑4)*. `cuarentena/README.md` §2 justifica el radio con un `grep` **restringido a `FOL/`**;
ampliado al repo son **cuatro**. *Debería:* sustituir la frase por el grep completo y añadir en
`FOLPure/Soundness.lean:26`, `PropLogic/Soundness.lean:27` y `FOL_poli/Soundness.lean:30` el aviso: *«⚠️
`Derives` de esta librería está HABITADO por `Theorems.Neg.dne` (y `…forall_not_impl_exists_not`). Esta
inducción cubre los N constructores; el enunciado cuantifica sobre todos los habitantes. **El enunciado
sigue siendo cierto** porque esos esquemas son semánticamente válidos, pero la prueba NO los cubre: hay
que cerrarlos a mano.»* — **defecto estructural MEDIDO, detonación NO medida**, y así hay que escribirlo.

**M‑8 · `FOL/Completeness.lean`: 702 líneas, 5 axiomas, 0 consumidores reales** *(FOL‑D2‑8, PAT‑6,
AX‑9, CC‑02, CC‑06)*. Su único «consumidor» es `TheoryFramework/Instances/FOL.lean:28`, que **está roto y
no lo compila nadie**. Y **siete de los trece axiomas de la librería `FOL` —el 54 %— cuelgan de este
módulo**: los 5 propios más los dos esquemas de `Theorems/`, cuyo **único sitio de uso en todo el
ecosistema** es `Completeness.lean:680` y `:519`. *Debería:* cabecera con el estado real y `README.md:36`
pasar de *«4. Teorema de Completitud de Gödel»* a *«esquema de prueba condicionado a cinco postulados»*.
✅ **Y lo que sí está medido y limpia al módulo** (CC‑06): `Completeness` **no** importa `Soundness` ni
`MetaRules`, **no** induce sobre `Derives` (sus 6 inducciones son sobre `Nat`, `Nat.le`, `List`, `Formula`)
y su `DerivesSet` es un **`def`**, no un `inductive` ⇒ **no hereda M‑11**. Escribirlo en
`cuarentena/README.md` §«radio del daño», que hoy deja al lector sin saberlo.

#### ⬜ BAJO

**B‑1 · `FOL_poli` es un clon muerto** *(FOL‑D2‑6)*. `FOL_poli/FOL.lean` **byte‑idéntico** a
`FOL/FOL.lean` (md5 igual, 225 líneas, cero `namespace` en los dos) ⇒ **no pueden coexistir en un fichero**
(la colisión está **compilada**: `import FOL.FOL` + `import FOL_poli.FOL` da error).
**B‑2 · Duplicados** *(FOL‑D2‑12)*: `deduction_theorem` en `Deduction.lean:25` y
`Theorems/Deduction.lean:19`; `derive_hyp`/`derive_weaken` en `Tactics.lean` y `Tactics2.lean`. Hoy no
colisionan **porque los segundos son huérfanos** — ver A‑7.
**B‑3 · git‑lock instalado pero INERTE** *(FOL‑D4‑12)*: el hook existe (2026‑04‑20) y protege **cero**
ficheros; `frozen_files.txt` 0 bytes y `locked_files.txt` contiene 4 bytes de basura (`an\r\n`).
**B‑4 · Ruido documental** *(FOL‑D4‑14, FOL‑D4‑15)*: `build_report.txt` da fe de un **BUILD FALLIDO** de
2026‑05‑08 listado como documentación; `PROCESANDO.md` con **0 bytes**; y placeholders de plantilla nunca
sustituidos — `REFERENCE.md:1` «# Technical Reference — **ProjectName**», `WORKFLOW.md:3` «Author: Your
Name», `README.md:120` clone de `ProjectName.git`.
**B‑5 · 96 de 157 declaraciones de la librería `FOL` (61 %) no las usa nadie** *(FOL‑D2‑11)*. **No borrar en
bloque** —mucho es andamiaje legítimo—: **etiquetar**. En particular `Semantics.lean` tiene 13 de 21
huérfanas **por la cuarentena** (servían a `Soundness.lean`), y eso no está escrito en ningún sitio.

### 4.2 ROBINSON_PlusPlus — por gravedad

#### ⛔ ALTO

**R‑1 · RPP no sólo HEREDA meta‑reglas envenenadas: las FABRICA** *(CC‑04)*
*Hoy:* `ax_list_induction` (`Full/Lists.lean:55-58`) tiene `step : ∀ h t, Γ ⊢ φ t → Γ ⊢ φ (cons h t)` —
**premisa‑FUNCIÓN de Lean**, la forma exacta que `MetaRules.lean:80-85` identifica como origen de la fuerza
patológica de `raa` — y conclusión `∀ L : Term`, o sea una ω‑regla sobre términos, más fuerte que `gen`.
*Debería:* (a) añadirlo **por su nombre** a la lista negra escrita de M‑11 con la etiqueta
**«premisa‑FUNCIÓN»**, que es el criterio que de verdad separa; (b) reescribir la frase de la «reparación
de fondo»: **mover `FOL/MetaRules` NO limpia `Derives`** mientras `Full/Lists.lean:55` siga ahí; (c) dejar
escrito que la reparación estructuralmente correcta de una regla que se quiere añadir a una relación
inductiva es un **CONSTRUCTOR** (o un inductivo que la envuelva), nunca un `axiom`: el `axiom` **no
extiende el punto fijo, afirma una falsedad sobre él**.

**R‑2 · Terminar ADR‑026 — el refactor está a medias y el árbol no construye** *(nuevo, medido hoy)*
*Hoy:* `class AnclaEq` en un solo fichero; 117 referencias a `prf_axiomsCodeT_eq`, **2 a nivel de término
en producción** (`Meta/InAxiomsCodePrf.lean:308,317`); ADR‑026 sin escribir; `AXIOMS.md` y todos los
banners siguen diciendo **5 `axiom`** cuando el árbol tiene **4**.
*Debería:* cerrarlo o revertirlo, **y en cualquier caso escribir en `AXIOMS.md` y en M‑11 la frase de
§6.2**: el ancla no ha desaparecido, ha cambiado de sitio a un sitio que `#print axioms` no mira.

**R‑3 · ADR‑010 sigue VIGENTE con sus dos afirmaciones centrales refutadas** *(ENG‑8, FOL‑D4‑6)*
*Hoy:* `DECISIONS.md:288` eleva a decisión vinculante *«`gen` … es la **ω‑regla** (regla de Büchi) … Su
presencia como `axiom` es correcta e inevitable»*, y justifica con una «soundness práctica». Las dos están
desmentidas: `gen` **no es la ω‑regla** (premisa sobre **todo `Term`**, no sobre numerales ⇒ premisa mayor,
regla **más débil**), y la premisa vacua es **exactamente el detonador** de
`cuarentena/Inconsistencia.lean`. Y hoy sabemos además que **`gen` sí podría ser constructor** (§3.3), con
lo que «inevitable» es falso por partida doble. El error sobrevive en **8 documentos de RPP**
(`GODEL-D-ARITHMETIZATION.md:13,16,25,41,52,136`, `GODEL-STATUS.md:188`, `MINIMAL-AXIOMS.md:266`,
`doc/REFERENCE-Incompleteness.md:9`).
*Debería:* **abrir `ADR-027`** (⚠️ **no** ADR‑024 ni ADR‑025: ya existen; y ADR‑026 está en vuelo) que
supersede la JUSTIFICACIÓN de ADR‑010 dejando en pie su DECISIÓN, y un bloque bajo su cabecera remitiendo.

**R‑4 · Bajar a FOL los lemas de lógica pura De Bruijn — y son DOCE, con uno probado TRES veces**
*(ENG‑7, CC‑07)*
*Hoy* [medido]: la proposición `substFormula c s (liftFormula c φ) = φ` está probada **tres veces**:
`Full/StrongInduction.lean:52` y `Meta/StrongInductionPrf.lean:75` (mismo nombre
`substFormula_liftFormula`, el segundo con docstring que **admite la copia**) y `Meta/Hilbert.lean:55` con
el nombre **`subst_lift_same`** — mismo teorema, tercer nombre, tercer módulo, y **ninguno de los tres
docstrings menciona a los otros dos**. Los nueve restantes: `liftTerm_swap`/`liftTerms_swap`/
`liftFormula_swap` (`StrongInductionPrf:117/126/135`), `subst1_id`/`subst0_var0_id` (:173/:176) y los
cuatro `substTerm(s)_liftLiftLift(Lift)` (`SubstArith:72/85/97/112`). Más dos duplicados internos que
ENG‑7 no vio: `liftTerm_nil`/`substTerm_nil` en `Minimal/Axioms.lean:604,667` **y otra vez palabra por
palabra** en `Meta/PremsBdAllPrf.lean:81,140`.
⚠️ **Y lo que esto significa para FOL**: FOL sólo tiene la versión de **TÉRMINO** y la variante off‑by‑one
`subst_lift_cancel_formula`; **la versión de FÓRMULA, general en `s`, NO EXISTE en FOL** y está escrita
tres veces en RPP.
*Debería:* bajar a `FOL/Theorems/Quantifiers.lean` (junto al `subst_lift_cancel_formula` reparado) el lema
general con **un** nombre, más los tres swaps y los cuatro `liftLiftLift*`; borrar las copias y dejar el
import. ⚠️ **Antes de mover nada, ADR‑019 (ciclos de import)**: `Meta/Hilbert.lean` está aguas arriba de
`Full/`, que es la razón escrita de la copia.

**R‑5 · La CI de RPP no compila el FOL local sino `julian1c2a/FOL@master`, y sin SHA** *(CC‑09)*
*Hoy:* `.github/workflows/build.yml` hace un segundo `actions/checkout` de `julian1c2a/FOL` en
`ref: master`. ⇒ un verde certifica la combinación (RPP@commit, FOL@master‑remoto), **que no es la que
compila en la máquina**; y `ref: master` no es un SHA ⇒ **el build de RPP no es reproducible**. FOL no
tiene CI propia. Nota menor pero real: la clave de caché de `FOL/.lake` **no incluye ninguna fuente de
FOL** y `restore-keys` es un prefijo ⇒ el `.olean` de un módulo borrado sobrevive en la CI; lo salva `[F]`,
pero **lo salva DESPUÉS del paso `Build`**.
*Debería:* fijar el checkout a un SHA e imprimir `git -C ../FOL rev-parse HEAD` en el log; dar CI propia a
FOL; y mover `Check doc sync` (o al menos `[F]`) **antes** de `Build`.

#### 🔶 MEDIO

**R‑6 · La frase retirada del docstring sobrevive literal en un `.md` de RPP** *(FOL‑D4‑5)*.
`MINIMAL-AXIOMS.md:271`: *«Junto con `gen` (ω‑regla) axiomatizan “demostrabilidad = verdad en el modelo
estándar ℕ”: el sistema es **sólido y completo relativo a ℕ**»*. Las dos mitades medidas falsas: **la
solidez es lo que NO se tiene**; la completitud es cierta **por otra razón y con otra consecuencia**
(`Meta/OmegaStrength.lean`: `raa` toma una función de Lean ⇒ lo que `⊢` no prueba lo **refuta** ⇒ `⊢` **no
es r.e.** y no puede ser sujeto de un teorema de incompletitud).

**R‑7 · `Probe/V4_census.lean` y `doc/book/fragmentos.json` dan por sancionados dos axiomas RETIRADOS**
*(ENG‑16)*: `ax_mod2_alternation` (hoy `theorem`, `Full/Mod2.lean:97`) y `GodelTwo.d3`. Y usan
`Full.Induction.ax_induction` en vez de `ax_induction_prim`. La base real de hoy son **14 entradas** —
⚠️ **y con ADR‑026 pasa a 13**. Mecanizarla en vez de mantenerla a mano.

**R‑8 · Ampliar M‑11 de `induction` a ELIMINAR** *(CC‑05)*. Enumerar `induction`, `cases`, `rcases`,
`match` sobre la prueba, `injection`, `.rec`, `.recOn`, `.casesOn`, `.noConfusion`; y añadir a
`check-doc-sync.bash` un bloque que grepee ese patrón contra la lista negra (`Derives`, `Prf`) y **AVISE —
no rompa—** con el número de apariciones, para que **el 0 de hoy quede medido y vigilado en vez de
supuesto**.

**R‑9 · La regla del alias `=eq` / `≐` no está escrita en ningún repo** *(ENG‑15)*. No hay colisión de
parseo [medido], pero el reparto está torcido —**4.410 usos de `=eq` contra 201 de `≐`**— y **20+ módulos
de `Meta/` usan los dos en el mismo fichero**. Escribirla en `NAMING-CONVENTIONS.md` de los dos repos. Y
**copiar M‑11 a `FOL/DECISIONS.md`**, que hoy declara «Sin MANDATORIES» mientras la regla que gobierna su
defecto más grave vive sólo en el otro repo.

#### ⬜ BAJO

**R‑10 · La corrección de ayer dejó su propio off‑by‑one** *(CC‑10 — **verificado vivo hoy**)*.
`sondeos/AnclaSoundness.lean:36` dice *«`FOL/MetaRules.lean` declara **seis** `axiom`s que lo HABITAN»* y
enumera a continuación **cinco**: `imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`. Falta **`dne`** — el que
la auditoría de ayer descubrió que faltaba en todos los conteos. El total del mismo párrafo (8 + 4 = 12) sí
es correcto: **el banner se actualizó y el cuerpo no**, que es el patrón que el propio proyecto tiene
documentado. ⚠️ Y **la misma frase arrastra la doctrina refutada en §3.3**: *«y tienen que ser axiomas,
porque sus premisas son funciones de Lean»* — falso para dos de los que lista.

---

## 5. LO QUE HAY QUE DECIDIR — y no puede decidir un auditor

**D‑1 · Las cuatro librerías muertas: ¿vivas, históricas, o fuera?**
Hoy están en el peor de los tres estados: **declaradas en el lakefile**, con 15 axiomas, **nunca
compiladas**, sin consumidor, y **con su salida en el `LEAN_PATH` de RPP**. Dado que `FOL_poli/FOL.lean` es
byte‑idéntico a `FOL/FOL.lean` y que ninguna tiene consumidor, la respuesta honesta es casi seguro
**retirarlas** — pero es decisión del propietario y hay que escribirla en `DECISIONS.md`. Es **la decisión
de la que dependen A‑2, A‑5, B‑1 y la mitad del censo**.

**D‑2 · ¿Se aplica la corrección de M‑11 y se mueven los cuatro evitables a constructores?**
Beneficio medido: **28 → 24 axiomas** y lista negra de `Derives` de **8 → 4**, sin tocar la fuerza del
cálculo. Coste medido: cambia la aridad del recursor ⇒ hay que revisar las 4 pruebas por `induction h with`
del repo, **todas fuera de la librería `FOL`** ⇒ **coste dentro de `FOL/`: cero pruebas tocadas**. Requiere
ADR y requiere decidir D‑1 primero (tres de esas cuatro pruebas están en librerías muertas).

**D‑3 · `FOL/Completeness.lean`: ¿se queda, se marca como no verificado, o se retira?**
Es el módulo del que cuelgan **siete de los trece axiomas** de la librería viva, no lo consume nadie, y su
único consumidor nominal está roto. ⚠️ **Si se retira hay un efecto medido que nadie ha escrito**:
`FOL.Theorems.Eq` **no está en el barrel** y sólo se compila porque `Completeness` lo importa ⇒ **20
módulos de RPP dejarían de construir**. Añadir `Theorems.Eq` al barrel **antes** de tocar nada.

**D‑4 · ¿Se parte el barrel `FOL.lean` en `FOL.Core` + `FOL.Omega`?**
`FOL.Core` sería **exactamente lo que RPP importa**; `FOL.Omega` añadiría `MetaRules`. Hoy `import FOL`
compila `EXIT=0` [medido] y trae `MetaRules` **y** `Completeness` juntos: `completeness` sobrevive mientras
su pareja está en cuarentena. ⚠️ *No he podido medir ninguna inconsistencia residual del barrel; lo intenté
por la vía `raa` + `completeness` y no sale (`raa` sólo AGRANDA `⊢`, y agrandar `⊢` hace `⊨ → ⊢` más fácil,
no contradictorio). Marco «no hay inconsistencia» como* **[hipótesis]**, *no como medida.*

**D‑5 · El git‑lock de FOL: ¿se retira o se usa?** Un mecanismo instalado que protege cero ficheros es peor
que ninguno. Si se usa, los candidatos evidentes son `FOL/MetaRules.lean`, `FOL.lean`,
`cuarentena/Inconsistencia.lean` y `cuarentena/README.md`.

**D‑6 · La numeración de ADR y el nombre del próximo.** ADR‑024 y ADR‑025 existen; **ADR‑026 está en vuelo
sin escribirse**. El ADR que R‑3 pide debe ser **ADR‑027**, y el de D‑2 el siguiente. Decidirlo antes de que
dos agentes escriban dos ADR‑026 distintos.

---

## 6. LO QUE NINGÚN CONTROL GARANTIZA

### 6.1 ⛔⛔ `#print axioms` es CIEGO a M‑11 *(META‑1)*

Un teorema probado por eliminación sobre un inductivo habitado por un `axiom` **puede ser falso y tener
footprint limpio**. No es un descuido de la herramienta, es estructural: **el axioma peligroso no aparece
en el footprint del TEOREMA, aparece en el footprint del USO.**

* `FOL.soundness` tenía footprint limpio y demostraba `False`.
* `prf_to_prfH` y `prf_to_derivation` tienen footprint `[propext, Classical.choice, Quot.sound]` —
  **net‑0 puro, la etiqueta que el proyecto usa como sello de calidad** — y su enunciado era falso en un
  habitante de `Prf`.
* Y **no era riesgo latente**: `Meta/InAxiomsCodePrf.lean:308` aplicaba `prf_to_prfH` **al axioma desnudo**.

⇒ **la regla escrita del proyecto —«el footprint se audita sólo con `#print axioms`»— es insuficiente**, y
hay que escribirlo donde esa regla vive.

### 6.2 ⛔⛔ Y hay una SEGUNDA ceguera, por un mecanismo distinto: **los CAMPOS DE CLASE**

**[MEDIDO, sonda compilada en esta pasada]:**

```lean
class Ancla : Prop where
  eq : False
theorem consecuencia [Ancla] : 2 + 2 = 5 := (Ancla.eq).elim
#print axioms consecuencia
```
```
'ProbeCls.consecuencia' does not depend on any axioms          EXIT=0
```

Un teorema que demuestra `2 + 2 = 5` desde un campo de clase que contiene `False` reporta **«no depende de
ningún axioma»**. La hipótesis no viaja como axioma sino como **argumento de instancia**, y la resolución
la hila sola.

Eso tiene **dos consumidores reales, y el segundo es de hoy**:

1. **`TheoryFramework.LogicSystem`** (§2.4): `#print axioms proves_iff_models` sale **limpio** porque su
   hipótesis —la solidez, para FOL medida FALSA— es el campo `sound`.
2. ⚠️ **El refactor ADR‑026 en vuelo en RPP.** `prf_axiomsCodeT_eq` era **el único axioma del proyecto en
   el footprint de `goedel_first_prf` y `goedel_second_prf`**. Convertido en `class AnclaEq`, ese footprint
   pasará a ser `[propext, Classical.choice, Quot.sound]` — **net‑0 puro** — y la hipótesis **seguirá
   estando ahí**, sólo que en un sitio que `#print axioms` no mira. [medido: el mecanismo; **hipótesis**:
   la cifra concreta, porque el árbol no construye ahora mismo.]

**El refactor es correcto** —`Prf` queda sin habitantes‑axioma y sus tres inducciones pasan a ser
legítimas, que era la deuda de M‑11— pero **no es gratis**: cambia una deuda visible por una invisible. La
frase que hay que escribir, y que hoy no está en ningún sitio, es:

> **El footprint de Gödel I y II no es net‑0: es net‑0 MÁS la instancia `[AnclaEq]`.** `#print axioms` no
> la enseña; para verla hay que hacer `#print` del teorema y mirar sus **binders de instancia**.

### 6.3 Lo que los demás controles tampoco garantizan [medido]

| control | qué NO ve |
|---|---|
| `FOL/check-sorry.bash` | **los 28 `axiom`**. Da VERDE. Y su `grep -c 'sorry'` **no delimita palabra** ⇒ frágil por construcción (hoy acierta con «adm**ite**» en un comentario) |
| `RPP/check-doc-sync.bash` `[A]` | cuenta `^axiom ` **sólo en `ROBINSON_PlusPlus/`** ⇒ **los 6 axiomas de FOL que SÍ están en el footprint de RPP son invisibles a su cifra de cabecera** |
| `RPP/check-doc-sync.bash` `[F]` | los **cuatro `.olean` de barrel huérfanos de contenido** (`FOLPure.olean`, `PropLogic.olean`, `TheoryFramework.olean`, `FOL_poli.olean`) — **siguen ahí hoy**: sus `.lean` existen, así que `[F]` los pasa en verde |
| cualquiera | **`import FOL` a secas**. Hoy hay 0 apariciones [medido] y **nada lo impide**. Un solo `import FOL` en cualquiera de los 132 módulos mete `MetaRules` + `Completeness` en la cadena |
| cualquiera | **`lake build FOLPure`**. Hoy `import FOLPure` falla [medido] sólo porque faltan los `.olean`; un build los repone y las cinco librerías comparten directorio de salida dentro del `LEAN_PATH` de RPP |
| la CI de RPP | **el FOL local**. Compila `julian1c2a/FOL@master` sin SHA |
| ninguno | **`TheoryFramework/Instances/*.lean`**: no entra en el cierre de imports de ninguna `lean_lib` ⇒ no lo compila `lake build`, ni `lake build TheoryFramework`, ni la CI |

### 6.4 Y lo que NO se ha probado — dicho para que nadie lo cite al revés dentro de seis meses

* **No hay prueba de consistencia de FOL.** El barrido de sospechosos no encuentra ninguna otra igualdad
  postulada sobre `substFormula`/`liftFormula` tras `ef54c6f` [medido]; `FOL/Completeness.lean` no importa
  `MetaRules` y no induce sobre `Derives` [medido]; y el detonador de `Inconsistencia.lean` **se
  autoalimenta** (usa la solidez para obtener una no‑derivabilidad, y sólo entonces `raa` dispara),
  mientras la completitud va en el sentido contrario y no ceba el mismo detonador. ⚠️ **Esto es hipótesis
  razonada, no medida: no se ha encontrado un ataque análogo, que no es lo mismo que haber probado que no
  lo hay.**
* **La corrección de `FOLPure`/`FOL_poli` (`ef54c6f`) está escrita, no verificada.** No hay forma de
  compilarla sin resolver D‑1 primero. *Puedo afirmar que está escrita; no que tipe.*
* **Que los cuatro evitables sean constructores legales está medido; que el refactor de D‑2 no rompa nada
  es hipótesis** hasta que alguien lo compile.
* **El árbol de RPP no construye ahora mismo** (§cabecera). Cualquier cifra de «145 jobs verdes» en
  cualquier banner del proyecto describe el estado de ayer, no el de hoy.

---

*Documento generado el 2026‑09‑12 contra FOL `ef54c6f` (limpio) y RPP `47d7348` + 1 fichero modificado.
Las mediciones marcadas se regeneran con `grep`/`find`/`git` sobre los dos árboles y con
`lake env lean <fichero>` desde PowerShell en la raíz de `ROBINSON_PlusPlus` (⛔ nunca `cd FOL && lake
build`). **Toda cifra de este documento caduca: se re‑mide, no se re‑lee.***
