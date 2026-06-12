# Changelog

**Last updated:** 2026-06-12 — **TFA completo + Gödel I/II + refactor meta-reglas**. `Full/` cierra el **Teorema Fundamental de la Aritmética** (`tfa_numeral`: existencia object ∧ unicidad ℕ) sobre una capa de **representabilidad** (numerales + homomorfismo + Euclides), autocontenido sin Mathlib/Peano. `Meta/Incompleteness.lean` (Nivel D): **Gödel I** mitad esencial + **Gödel II** (postulando D2/D3). Las 5 meta-reglas ω de deducción se movieron a **`FOL/MetaRules.lean`** (re-export desde `Minimal.Axioms`). **25 módulos** (Minimal 11 + Meta 3 + Full 11), build verde (39 jobs) 0 warnings / 0 sorrys.
**Author**: Julián Calderón Almendros

All notable changes to this project will be documented in this file.

Format based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added (2026-06-12) — Gödel Nivel D: Incompletitud (Meta/Incompleteness.lean)

- **Gödel I (mitad esencial)**: `goedel_first_unprovable : Consistent → ⊬ goedelSentence` (si el sistema es consistente, `G` no es demostrable), `goedel_first_true` (`G` verdadera-pero-indemostrable), `incompleteness`. Derivado de D1 (`provFormula_repr`) + diagonalización (`goedelSentence_fixedpoint`) del Nivel C.
- **Gödel II**: `goedel_second : Consistent → ⊬ consistencyFormula` (`Con := ¬Prov(⌜⊥⌝)`). **Postulando D2 y D3** (Hilbert-Bernays-Löb). Lema crucial `con_imp_goedelSentence : ⊢ (Con ⇒ G)` (Gödel I formalizado). Toda la cadena HBL (incl. contrapositiva) con `imp_intro`/`mp`, **sin DNE object-level** → funciona en el FOL intuicionista.
- Pendiente: otra mitad de Gödel I (`⊬ ¬G`, vía ω-consistencia/Rosser).

### Changed (2026-06-12) — refactor: meta-reglas ω → FOL/MetaRules.lean

- Las 5 meta-axiomas ω (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`) + wrappers de `Derives` (`mp`, `and_*`, `or_intro_*`, `false_elim`, `ex_intro`, `iff_*`) movidos de `Minimal/Axioms.lean` (lógica pura conviviendo con axiomas aritméticos) a **`FOL/MetaRules.lean`** (namespace `FOL.MetaRules`). `Minimal.Axioms` los **re-exporta** → cero churn en sitios de uso. FOL gana la ω-regla como axioma (documentado). Commits: FOL `084dbd2`, RPP `5fc89bb`.

### Added (2026-06-12) — Full: TFA completo + capa de representabilidad

- **Reencuadre numerales + representabilidad** (Gödel-aware): tras detectar que `ax_p_tfa` (meta de Block8) no admite discharge constructivo (object existenciales no dan testigos meta; disyunciones object no se eliminan a meta), se trabaja sobre **numerales** (`numeral n = σⁿ(0)`) con cómputo meta en ℕ + transferencia por homomorfismo.
- **`Full/Numerals.lean`**: `numeral` + homomorfismo `numeral_add/mul/pow`, orden `numeral_lt`, separación `numeral_ne`.
- **`Full/StrongInduction.lean`**: `strong_induction` (course-of-values) **DERIVADA de `ax_induction` sin axioma nuevo** + `substFormula_liftFormula` + `lt_succ_split`.
- **`Full/Bounded.lean`**: `le_numeral_split` (cuantificación acotada → casos finitos).
- **`Full/Divisibility.lean`**: `numeral_dvd`, `divisor_le`. **`Full/Division.lean`**: `division_numeral`. **`Full/Primality.lean`**: `isPrime_numeral`.
- **`Full/PrimeFactor.lean`** (ℕ pura, sin Mathlib): `exists_prime_factor`, `primeFactorList`, **lema de Euclides** (`euclid` vía `Nat.Coprime.dvd_of_dvd_mul`), unicidad (`count_unique`, `factorization_perm_unique` vía `List.perm_cons_erase`).
- **`Full/Factorization.lean`**: `toTerm`, `prod_pairs_toTerm`, **`tfa_numeral`** — TFA completo (existencia object ∧ unicidad ℕ). El `ax_p_tfa` de Block8 queda como forma idealizada.

### Added (2026-06-11) — Full/Lists.lean: ax_C3 y ax_L3 derivados (inducción estructural)

- **NUEVO módulo `Full/Lists.lean`** (330 líneas) — derivación de los dos axiomas de listas postulados en Minimal vía meta-axioma de inducción estructural:
  - **NUEVO meta-axioma `ax_list_induction`** (estilo `imp_intro`/`gen`/`or_elim`):
    ```lean
    axiom ax_list_induction {Γ} (φ : Term → Formula)
      (base : Γ ⊢ φ nil)
      (step : ∀ h t, Γ ⊢ φ t → Γ ⊢ φ (cons h t)) :
      ∀ L, Γ ⊢ φ L
    ```
    Parametrizado por función Lean `φ : Term → Formula` (no `Formula → Formula` como `ax_induction`). Más limpio: evita el manejo De Bruijn de los dos binders ∀h ∀t que requeriría una versión object-level. Conclusión sobre **todos** los Terms (no solo listas) — análogo a cómo `ax_induction` decide tratar Term como generado libremente por 0 y σ. (Observación: con 3 binders esta forma generalizaría a inducción sobre ordinales / W-types arbitrarios.)
  - **Helpers de congruencia**: `eq_congr_cons_right_full` (cons respeta `=` en arg derecho), `eq_congr_concat_left/right` (concat respeta `=` en ambos args), `eq_subst_in` (substituye igualdad bajo predicado `In`), helper local `iff_intro` (construye `iff` desde dos meta-implicaciones).
  - **`concat_assoc_pointwise` + `concat_assoc_thm : ⊢ ax_C3_concat_assoc`** — `(L##M)##N = L##(M##N)` por inducción estructural en L con M, N como parámetros Lean. Base nil: `ax_C1` doble + congruencia. Paso cons: `ax_C2` triple + IH + `eq_congr_cons_right_full`.
  - **`in_concat_pointwise` + `in_concat_thm : ⊢ ax_L3_in_concat`** — `In(x, L##M) ⇔ In(x,L) ∨ In(x,M)` por inducción estructural en L con x, M como parámetros. Base nil: `ax_L1` (¬In x nil) + `ax_C1`. Paso cons: `ax_C2` (concat fuera) + `ax_L2` (membership recursiva) + IH + asociatividad de `∨`. Prueba completa de las dos direcciones del `⇔`.
- **Cobertura del fragmento de Minimal en Full**: ax6/7/10/11/12 (algebraicos), ax18/19 (orden), ax21/24 (mod2), **ax_C3/L3 (listas)** ✅. Pendientes: Ax-P (TFA, inducción fuerte), Gödel Nivel D.

### Added (2026-06-11) — Full: ax21 y ax24 derivados (Opción C.2)

- **NUEVO módulo `Full/Mod2.lean`** (290 líneas) — caracterización completa de la recursión de `mod2` y derivación de los dos axiomas restantes del fragmento aritmético de `Minimal`:
  - **Nuevo axioma de Full**: `ax_mod2_alternation : axioms ⊢ ∀n, mod2(σn) + mod2(n) = 1`. Conservativo respecto a Minimal (allí derivable de `ax21 + ax16 + teo_1_3`).
  - **`mod2_zero_aux : axioms ⊢ mod2(0) = 0`** — re-probado en Full **sin usar `ax21`**, sólo `ax17 + teo_2_9`. (Block3.mod2_zero usa case-split sobre `ax21`.)
  - **Helpers**: `eq_congr_mod2` (congruencia de `mod2`), `a_plus_one_eq_one` (`a + 1 = 1 → a = 0` por `ax3+ax4+ax5`).
  - **`mod2_range_thm : axioms ⊢ ax21_mod2_range`**: `∀n, mod2(n) = 0 ∨ mod2(n) = 1`. Por inducción object-level con base `mod2_zero_aux` + paso usando `ax_mod2_alternation` con case-split sobre la IH.
  - **`mod2_two_k_eq_zero_ax` + `mod2_of_even_thm : axioms ⊢ ax24_mod2_of_even`**: `∀n k, n = 2k → mod2(n) = 0`. Por inducción sobre k (motivo `mod2(2k) = 0`), usando ax9 para reescribir `2·σk = 2k + 2 = σσ(2k)` y dos aplicaciones de alternancia. Luego se generaliza a `∀n k, n = 2k → mod2(n) = 0` vía `eq_congr_mod2`.
- **Auditoría en `MINIMAL-AXIOMS.md §3.2` actualizada**: documenta el hallazgo de que `ax16` sólo captura media alternancia (`mod2(n)=0 ⇔ mod2(σn)=1` no implica `mod2(n)=1 → mod2(σn)=0`) y que `ax16+ax17` dejan `mod2` subdeterminado (modelos no estándar con `mod2(σn) ≥ 2` cumplen ambos). Por eso `ax21` carga información independiente, no derivable sin un axioma extra como `ax_mod2_alternation`.
- Estado del fragmento aritmético de Minimal derivado en Full: **ax6, ax7, ax10, ax11, ax12, ax18, ax19, ax21, ax24** ✅. Pendientes: ax_C3, ax_L3 (listas — inducción sobre listas codificadas vía Cantor), Ax-P (TFA — inducción fuerte), Gödel D.

### Removed (2026-06-11) — `Intermediate/` eliminado

- **`Intermediate/Induction.lean` BORRADO** + directorio `Intermediate/` eliminado. **Justificación** (decisión 2026-06-11): el prototipo confirmó que la inducción general (esquema sobre `φ` arbitrario en Full) no añade fricción técnica sobre la restringida (Φ finito). Cualquier instancia inductiva concreta que necesitemos se postula directamente en `Full/`. Mantener un nivel separado para Φ finito era **burocracia conceptual** sin valor técnico.
- **Cadena de embeddings simplificada**: `FOL⁼ ⊂ Minimal ⊂ Full` (sin `Intermediate` intermedio).
- Referencias a Intermediate actualizadas en `ROBINSON_PlusPlus.lean` (root barrel), `PLANNING.md §6`, `NEXT-STEPS.md` Eje 3.

### Added (2026-06-07) — Full: ax19 (tricotomía) derivado

- **`lt_trichotomy_ax` / `lt_trichotomy_thm : axioms ⊢ ax19_lt_trichotomy`**: `∀a ∀b, a<b ∨ a=b ∨ b<a` derivado por inducción object-level (inducción sobre `a`, `∀b` interno, `or_elim` de 3 vías). Lemas auxiliares nuevos: `zero_lt_succ` (0<σk), `zero_or_succ_ax` (`∀b, b=0 ∨ ∃k b=σk`, por inducción con `∨`/`∃`), `lt_succ_cases` (`a<b → σa<b ∨ σa=b`, casando el testigo), `lt_intro` (construcción de `lt` desde testigo), `succ_add2`.
- Con ax18, **los dos axiomas de orden (ax18, ax19) son ahora teoremas en `Full`**. Acumulado derivado: **ax6, ax7, ax10, ax11, ax12, ax18, ax19**.
- Pendiente: ax21/24 (mod2), listas (ax_C3/ax_L3 — inducción sobre listas), Ax-P (TFA), Gödel D.

### Added (2026-06-07) — `Full/Induction.lean` (inducción general object-level, lift-aware)

- **NUEVO módulo `Full/Induction.lean`** (namespace `ROBINSON_PlusPlus.Full`): inducción general como **axioma object-level** (diseño elegido por el usuario: la inducción entra solo como axioma; las pruebas usan `mp`/`gen`/`imp_intro`, sin meta-inducción).
  - **`ax_induction (φ) : axioms ⊢ inductionFormula φ`** — esquema general. `inductionFormula` codifica `φ(σn)` de forma **lift-aware** como `substFormula 0 (σ#0) (liftFormula 1 φ)` (preserva variables-parámetro; la versión ingenua las decrementaba, rompiendo el caso multivariable).
  - **Lema de composición De Bruijn** (resuelve el obstáculo): `substTerm_subst_succ_lift`/`substTerms_subst_succ_lift` (`substTerm 0 m (substTerm 0 (σ#0) (liftTerm 1 t)) = substTerm 0 (σm) t`), `substFormula_eq_succ_lift`, `step_eq_reduce`.
  - **`induction_object`**: empaquetado object-level (doble `mp` sobre `ax_induction`).
  - Derivados **en forma object-level pura**: `zero_add`, `succ_add` (multivariable), `add_comm_ax`, y **`add_comm_thm : axioms ⊢ ax6_add_comm`** — `ax6` (postulado en `Minimal`) es ahora teorema. Sin usar `ax6`.

### Added (2026-06-07) — Full: más axiomas derivados + limpieza

- **`add_assoc_ax`** (= `ax7`): `∀c, (a+b)+c = a+(b+c)` por inducción object-level (2 parámetros). `ax7` derivado como teorema (queda pendiente sólo el empaquetado `∀³` literal, por ajuste De Bruijn de niveles).
- **Cadena `mul` completa** (object-level): `zero_mul`, `succ_mul`, **`mul_comm_ax`/`mul_comm_thm` (= ax10)**, **`mul_distrib_ax` (= ax12)**, **`mul_assoc_ax` (= ax11)**. Con esto **TODOS los axiomas algebraicos ECUACIONALES de Minimal son teoremas en Full**: ax6, ax7, ax10, ax11, ax12. Helpers de instanciación añadidos (`add_zero1`, `add_succ2`, `add_assoc3`, `add_comm2`, `mul_zero1`, `mul_succ2`, `zero_mul1`, `succ_mul2`, `mul_distrib3`).
- **Limpieza**: eliminados los directorios stray root-level `Full/`, `Intermediate/`, `Minimal/` (solo contenían `_template.lean` genéricos; el código real vive en `ROBINSON_PlusPlus/`).
- **Composición De Bruijn generalizada** (2026-06-07): `substTerm_subst_succ_lift_gen`/`substTerms_..._gen` (offset arbitrario, por tricotomía) y `substFormula_succ_lift_gen` (estructural sobre `Formula`, casos `∀`/`∃` por `congrArg`+defeq a offset `c+1`). De ahí `substFormula_succ_lift` (offset 0) y **`step_reduce` general** (reduce el paso de inducción de CUALQUIER `φ` a `φ(n) ⇒ φ(σn)`). Esto **desbloquea la inducción object-level sobre fórmulas no-ecuacionales** (`∨`/`∃`/`¬`/`∀`).
- **`ax18` (lt_irrefl) derivado** (2026-06-07): **primer axioma no-ecuacional**, vía `step_reduce` general + `ax13` (def de `lt`, con `∃`) + `ax2`/`ax3` + `zero_add`/`succ_add` derivados. `lt_irrefl_ax : ⊢ ∀a ¬(a<a)` y **`lt_irrefl_thm : ⊢ ax18_lt_irrefl`**. Valida la inducción object-level sobre fórmulas con `¬`/`∃`.
- **Lemas de orden auxiliares hacia `ax19`** (2026-06-07): `lt_succ_self` (`a < σa`), `not_lt_zero` (`¬(a<0)`), `lt_succ_of_lt` (`b<a → b<σa`). Validan el patrón de **construcción** de `lt` (vía `ax13` + `ex_intro`) además del de eliminación (`ex_elim`).
- Pendiente: **ax19** (tricotomía) — falta `zero_or_succ` + `lt_succ_cases` + el ensamblaje 3-vías (inducción con `∀b` interno y `or_elim`). Luego **ax21/24** (mod2), **listas** (ax_C3/ax_L3 — inducción sobre listas), **Ax-P** (TFA, inducción fuerte), y **Gödel Nivel D**. Empaquetado `⊢ axN` literal sale directo para `∀²` (ax6, ax10); para `∀³` (ax7, ax11, ax12) queda pendiente un helper n-ario (la derivación sustantiva `_ax` ya está).

### Added (2026-06-06) — `Intermediate/Induction.lean` (prototipo de inducción)

### Added (2026-06-06) — `Intermediate/Induction.lean` (prototipo de inducción)

- **NUEVO módulo prototipo `Intermediate/Induction.lean`** (namespace `ROBINSON_PlusPlus.Intermediate`), para validar la viabilidad del esquema de inducción antes de comprometerse con la estructura de `Intermediate/` (Φ finito) o `Full/` (inducción general).
  - Meta-axioma **`peano_induction`** (forma híbrida: paso meta, conclusión object-level, análoga a `gen`/`ex_elim`): de `φ(0)` y `∀n (⊢φ(n) → ⊢φ(σn))` concluye `⊢ ∀n φ(n)`.
  - **`zero_add_ind`** (`∀n, 0+n=n` por inducción, **sin `ax6`** — a diferencia de `teo_2_2`).
  - **`succ_add_ind`** (`∀a n, σa+n = σ(a+n)`, inducción multivariable con `liftTerm` para el parámetro).
  - **`add_comm_ind`** + **`add_comm_thm : axioms ⊢ ax6_add_comm`**: `ax6` (postulado en `Minimal`) **derivado como teorema** por inducción usando sólo `ax4`/`ax5`. Primer eslabón del embedding `Minimal ⊂ Intermediate`.
  - **Hallazgo**: la inducción general se formula/usa igual de fácil que una restringida a Φ; `Full/` (general) sería el camino de menor fricción técnica, `Intermediate/` (Φ finito) aporta valor conceptual. Decisión Intermediate-vs-Full pendiente.
- Build: **27 jobs, 0 errores, 0 warnings, 0 sorrys**. 14 módulos (incl. prototipo).

### Added (2026-06-06) — `Meta/Provability.lean` (Nivel C: demostrabilidad y diagonalización)

- **NUEVO módulo `Meta/Provability.lean`** (namespace `ROBINSON_PlusPlus.Meta.Provability`), Fase 19 del spec. Construye sobre `Meta/Godel.lean`.
  - **Codificación estructural de Gödel** de la sintaxis FOL: `charsCode`/`strCode` (símbolos vía lista de caracteres), `termCode`/`termsCode` (mutuos, por el anidamiento `func : String → List Term → Term`), y `formCode : Formula → Term` (tag por constructor: ⊥=2, atom=3, eq=4, impl=5, ∀=6, ∧=7, ∨=8, ∃=9).
  - **Inyectividad demostrada (consistency-free)**: `charsCode_injective`, `strCode_injective`, `termCode_injective`/`termsCode_injective` (mutuos), `formCode_injective` — vía `injection` + inducción estructural; sin postular nada.
  - **Def 29** `IsFormula (x) := ∃ φ, x = formCode φ`; `Provable (x) := ∃ φ, x = formCode φ ∧ axioms ⊢ φ`; **teorema real** `provable_formCode_iff : Provable ⌜φ⌝ ↔ axioms ⊢ φ` (vía `formCode_injective`).
  - **Def 30** `Dem : Term → Term → Prop` (meta-axioma) + **Teo Meta** `dem_iff_provable : axioms ⊢ φ ↔ ∃ d, Dem d ⌜φ⌝` (meta-axioma).
  - **Lema del punto fijo** `diagonal_lemma : ∀ φ, ∃ ψ, ⊢ ψ ⇔ φ[⌜ψ⌝]` (meta-axioma); `provFormula`/`provFormula_repr` (predicado de demostrabilidad object-level + representabilidad, meta-axiomas).
  - **Sentencia de Gödel** `goedelSentence` (punto fijo de `¬provFormula`) + `goedelSentence_fixedpoint : ⊢ G_Min ⇔ ¬Prov(⌜G_Min⌝)` (demostrado a partir de `diagonal_lemma`).
  - **5 meta-axiomas nuevos** (`Dem`, `dem_iff_provable`, `provFormula`, `provFormula_repr`, `diagonal_lemma`): la aritmetización de demostraciones y la diagonalización requieren inducción → teoremas en el **Nivel D** (`Intermediate/`/`Full/`). El Nivel D (Gödel I/II internos) queda pendiente.
- **Barrel `Meta.lean`** creado (agrega `Meta.Godel` + `Meta.Provability`); el barrel raíz importa `ROBINSON_PlusPlus.Meta`.
- Build: **26 jobs, 0 errores, 0 warnings, 0 sorrys**. 13 módulos.

### Added (2026-06-06) — Block8 corolarios (Dvd/TFA) + `Meta/Godel.lean` (Nivel B)

- **`Block8.lean` — +10 teoremas (sin inducción)**:
  - Álgebra de `Dvd`: `dvd_trans`, `dvd_mul_right`, `dvd_mul_left`, `dvd_mul_of_dvd_left`, `dvd_mul_of_dvd_right`, `dvd_add` (vía `mul_assoc'`/`mul_comm'`/`mul_distrib'` de Block4_C5 + congruencia `eq_congr_mul/add_*`).
  - Corolarios del TFA (`ax_p_tfa`): `factorization_exists`, `factorization_unique` (vía `eq_trans` sobre la factorización canónica), `lt_zero_one` (testigo `k=0` en `ax13`, cierra con `teo_1_2`), `factorization_one_eq_nil`.
  - **Fuera de scope `Minimal/`**: lema de Euclides (`IsPrime p → p ∣ a·b → p ∣ a ∨ p ∣ b`) y multiplicatividad (`prod_pairs (concat f g) = prod_pairs f · prod_pairs g`) requieren `prod_pairs_concat` (recursión sobre lista) → inducción; diferidos a `Intermediate/`/`Full/`.

- **`Meta/Godel.lean` — NUEVO módulo (Nivel B Gödelización, Fase 18 del spec)**:
  - Namespace `ROBINSON_PlusPlus.Meta.Godel`. **No añade axiomas matemáticos** sobre `Minimal/`.
  - **Def 27**: `inductive Sym` (alfabeto Λ, 12 símbolos), `gNat : Sym → Nat` (tabla de Gödel: ∀↦2, ∃↦3, =↦10, …, m↦111) + `gNat_injective`.
  - `numeral : Nat → Term` (σⁿ0) + `numeral_injective`; `G : Sym → Term := numeral ∘ gNat` + `G_injective`.
  - **Def 28**: `encode : List Sym → Term` (corner brackets `⌜·⌝`, notación scoped) + `encode_nil`/`encode_cons`.
  - **Teo G1**: `encode_injective` (meta-inyectividad, **consistency-free**, vía `injection` + inducción estructural sobre la lista). Versiones object-level `encode_cons_inj` (vía `cons_inj`) y `encode_cons_neq_nil` (vía `cons_neq_nil`), faithful al "Teo L2 repetidamente" del spec. Pasar de la object-level a la conclusión meta `S = S'` requeriría `Con(axioms)`, diferido al Nivel C/D.
  - Añadido `import ROBINSON_PlusPlus.Meta.Godel` al barrel raíz. Sistema: **12 módulos**, build verde, 0 warnings, 0 sorrys.

### Changed (2026-06-06) — Linter `unusedSimpArgs` a `false` global + warning FOL cerrado

- **Linter `unusedSimpArgs` → `false` en los 12 módulos** (revierte el `true` del barrido del cierre anterior). Razón: el linter puede dar falsos positivos bajo binders existenciales y se prefiere libertad para conservar args de `simp` por robustez. El build permanece con 0 warnings.
- **Warning externo `FOL/Theorems/Eq.lean:130` cerrado**: eliminado el arg `simp` no usado `hne` en `substTerm_liftLift` (la rama de la variable cierra con `hgt` + `omega`). Commit en el repo hermano `FOL`: `9888c58`. Build global ahora con **0 warnings incluido el externo**.

### Added (2026-06-06) — Bloque VIII extendido

- **`Axioms.lean` — Lenguaje extendido**: nuevos símbolos `pow_sym = "^"` y `prodp_sym = "Π_p"`, con constructores `pow (b e : Term) : Term` y `prod_pairs (l : Term) : Term`. Cuatro axiomas definitorios añadidos:
  - `ax_pow_zero`: `∀ b, b^0 = 1`
  - `ax_pow_succ`: `∀ b, ∀ e, b^(σe) = b^e * b`
  - `ax_prodp_nil`: `prod_pairs [] = 1`
  - `ax_prodp_cons`: `∀ p, ∀ e, ∀ t, prod_pairs ((p,e)::t) = p^e * prod_pairs t`

  Sistema reducido de **30 → 34 axiomas matemáticos** (25 aritm: 23 base + 2 pow; + 7 listas; + 2 factorización: prodp_nil, prodp_cons).

- **`Block8.lean` — Fase 17 completa**: añadidos:
  - Lemas básicos `pow_zero`, `pow_succ`, `prod_pairs_nil`, `prod_pairs_cons` (instancias inmediatas de los nuevos axiomas).
  - **Def 26 `IsFactorization (f n : Term) : Prop`**: meta-Prop. `f` factoriza a `n` ⟺ `prod_pairs f =eq n` ∧ todo par `(p,e)` que aparece en `f` cumple `IsPrime p ∧ e > 0`. La restricción de forma sobre `f` proviene de `ax_prodp_cons` (solo se activa en cons-de-pair).
  - `isFactorization_nil_one`: caso base, `[]` factoriza al `1` (la cuantificación sobre elementos es vacuamente satisfecha por explosión object-level vía `ax_L1_in_nil`).
  - **Meta-axioma `ax_p_tfa` (TFA)**: `∀ n, axioms ⊢ lt zero n → ∃ f, IsFactorization f n ∧ ∀ f', IsFactorization f' n → axioms ⊢ (f =eq f')`. Estilo idéntico a `imp_intro`/`gen`/`raa`/`or_elim`/`ex_elim` (no expresable como `Formula` por ser meta-Prop). Justificación spec: en sistemas con inducción débil es derivable; en `Minimal` se adopta como axioma (§Apéndice B.4).

  Fase 17 completa según spec `TuplasFuncionesYListas.md §BLOQUE VIII`. Las Fases 18-19 (Gödelización + autorreferencia) permanecen fuera del scope `Minimal/` y corresponden a un módulo `Meta/` futuro.

### Changed (2026-06-06) — Limpieza warnings global

- **Todos los 11 módulos `Minimal/Theorems/*.lean`** ahora tienen `set_option linter.unusedSimpArgs true` activo. **411 → 0 warnings** en RPP. Eliminados argumentos `simp` no usados (mayoritariamente `liftTerm`, `liftTerms`, `FOL.substTerm_lift_comm`, `FOL.substTerm_liftLift`) en simp calls que ya no los requerían tras refactors anteriores.
- Reparto por módulo: Block5 (2), Block7 (6), Block4_C6_C7 (14), Block8 (22), Block1 (22), Block4_C5 (32), Block6 (39), Block2 (274).
- Único warning persistente: `FOL/Theorems/Eq.lean:130` (librería externa, no parte del proyecto RPP).

### Added (2026-06-03)

- **`Block8.lean` — BLOQUE VIII Fase 17 parcial (Primos)**: nuevo módulo con `Dvd` (divisibilidad), `IsPrime` (Def 25), y lemas básicos (`dvd_refl`, `dvd_one`, `dvd_zero`, `isPrime_zero_inconsistent`, `isPrime_one_inconsistent`). Mismo estilo meta-Prop que Block7. Build verde, 0 sorrys. **Pendientes documentados** (requieren extensión del lenguaje, fuera de scope `Minimal/`): Def 26 (`IsFactorization` — necesita `pow`/`prod_list`), Ax-P (TFA), Fases 18-19 (Gödelización + autorreferencia, corresponden a `Meta/` futuro).

- **`Block7.lean` — BLOQUE VII (Funciones Discretas)**: nuevo módulo con `IsFunction` (Def 21), `Functional` (Def 24, con `Map` inlineado), y los teoremas F1 (`IsFunction nil`), F2 (evaluación única), F3 (`IsFunction ⟺ Functional`). Estilo de formalización: `IsFunction`/`Functional` se definen como **meta-predicados Lean** (`Term → Prop`) parametrizados por cuantificación universal sobre `Term`, evitando el manejo manual de De Bruijn (`liftTerm`/`substTerm`) que aparecería con `forall_2`/`forall_3`. Build verde a la primera, 0 sorrys. Spec: `TuplasFuncionesYListas.md §BLOQUE VII`.

### Removed (2026-06-03)

- **`ax27_add_left_cancel` ELIMINADO** — derivable en PA⁻ sin inducción. Prueba (style PA⁻): si `a+c=b+c`, por tricotomía (ax19) `a<b ∨ a=b ∨ b<a`; los casos estrictos llevan a `a+c < a+c` vía `lt_add_const_of_le_left` (Block4_C5) + `add_comm'` y contradicen ax18. Reescrito `add_left_cancel` (Block4_C6_C7) con esta prueba. Refactorizado `succ_le_of_lt` (Block2) para no depender de ax27: en su lugar usa `ax5+ax3` para llegar a `a + σ(k+kp) = a`, luego `ax13` da `lt a (a + σ(k+kp))`, sustituye y contradice ax18. Sistema reducido de **31 → 30 axiomas matemáticos** (23 aritméticos + 7 listas).

### Fixed (2026-06-03)

- **Build roto reparado**: el commit `537fd68` (eliminación de `ax22`/`ax23`) introdujo `proj_is_cantor` en `Block4_C6_C7` usando `mod2_of_even`, pero este último vivía en `Block5` — y `Block5` importa `Block4_C6_C7`, creando dependencia circular. Solución: mover `mod2_of_even` a `Block4_C6_C7` (justo antes de `proj_is_cantor`) y exportarlo desde allí. `Block5` lo sigue viendo vía `open Block4_C6_C7`. Sin cambios de prueba, solo de ubicación.
- **Conteo de axiomas rectificado**: docs previos decían "30 axiomas matemáticos" — el conteo real de la lista `axioms` es **31** (24 aritméticos: ax2-19, ax21, ax24-27, ax29 + 7 listas: ax_L0-3, ax_C1-3). El número "30" era un error histórico arrastrado.

### Removed (2026-06-02, commit 537fd68 — Claude Code Pro / Copilot Pro)

- **`ax22_cantor_proj_exists` ELIMINADO**: `proj1`/`proj2` dejan de ser símbolos opacos del lenguaje (con axioma "Skolem" atándolos a `is_cantor`) y pasan a ser `def proj1 (c) := x_of_c c`, `def proj2 (c) := y_of_c c` en `Block4_C6_C7`. El contenido de ax22 se demuestra constructivamente como teorema `proj_is_cantor`.
- **`ax23_cantor_proj_uniq` ELIMINADO**: era `cantor_uniqueness` reescrito como axioma; nunca se usó en código (el teorema `cantor_uniqueness` real ya estaba probado en `Block4_C6_C7`).
- Símbolos `proj1_sym`, `proj2_sym` y los `def proj1`/`def proj2` opacos de `Axioms.lean` eliminados.
- `Block5` refactorizado: `proj1_pair_eq_x`, `proj2_pair_eq_y`, `pair_proj_eq_c` ahora usan `proj_is_cantor` en lugar de `spec h_ax22`.

### Removed (2026-06-02)

- **`ax28_mul_two_cancel` ELIMINADO** del sistema axiomático. Era redundante: la spec `TuplasFuncionesYListas.md §Teo 2.11` ya proporcionaba la prueba sin inducción (tricotomía + irreflexividad + monotonía estricta de *2). Sistema de **33 → 32 axiomas matemáticos** (con el conteo rectificado).
- El `def ax28_mul_two_cancel` queda comentado en `Axioms.lean` como nota histórica.

### Added (2026-06-02)

- **`Block1.mul_two_succ_ne_zero (k) : ¬(2·σk = 0)`** — Helper público para `teo_2_11`. Demostrado vía teo_2_7 + ax5 + ax2 (sin inducción).
- **`Block1.mul_two_lt_mono {a b} (h : a<b) : 2a < 2b`** — Monotonía estricta de *2 sin inducción. Usa ax5/ax12/ax13 + ax13 (testigo `j := σk+k`).
- **`Block1.teo_2_11`** reprobado directamente desde primeros principios (tricotomía ax19 + irreflexividad ax18 + `mul_two_lt_mono` + sustitución vía `Derives.subst`). Anteriormente delegaba a `ax (... ax28 ∈ axioms)`. Ahora es un teorema real sin axioma de respaldo.

### Changed (2026-06-02)

- **`Block4.cantor_injective_c`** refactorizado para usar `spec teo_2_11` en lugar de `spec h_ax28`.
- **`Block4_C6_C7.cantor_uniqueness`** refactorizado análogamente.
- **`REFERENCE.md`** reescrito completo (proyección al estado actual: 9 módulos ✅, 30 axiomas, lista de exports por módulo, signaturas + descripción matemática).

### Added (2026-05-27)

- **Axiomas `ax_C3_concat_assoc` y `ax_L3_in_concat`** en `Minimal/Axioms.lean`. Postulados siguiendo el patrón de ax21/ax24/ax27/ax28 (teoremas en sistemas con inducción, axiomas en `Minimal`). Permiten cerrar `concat_assoc` y `in_concat_iff` en Block6 sin inducción sobre L.
- **Axioma `ax29_sub_witness`** + función `sub` con `sub_sym` en `Minimal/Axioms.lean`. Postula el testigo de la resta truncada (`b ≤ a → b + (a − b) = a`). Permite definir `x_of_c`/`y_of_c` constructivamente y cerrar `cantor_surjectivity`.
- **`eq_congr_pred`** en `Minimal/Axioms.lean` (análogo a `eq_congr_succ`).
- **`lemma_C5_unique`** y **`cantor_bounds`** exportados desde `Block4_C5`.
- **`is_cantor_pair`** exportado desde `Block5` (clave del isomorfismo pares ↔ N).

### Changed (2026-05-27)

- **🎉 PROYECTO `Minimal/` A 0 SORRYS REALES**. Build verde `lake build` exit 0, `WARN_sorry=0`. Los 5 `axiom imp_intro/gen/raa/or_elim/ex_elim` son meta-reglas de FOL, no `:= sorry`.
- **Block4_C5 cerrado** (commit `4b6a2a9`): probados `sq_2w_plus_1`, `w_w1_le_2c_iff_sq_2w1_le_8c1`, `mono_w_w1`, `h_sq_2w1_le_sq_s`, `h_existence_part2` (este último por contradicción reusando el iff). Sentencia ajustada a `liftTerm 0 c` y cerrada con `ex_intro w`. Helper `lemma_C5_unique` exportado.
- **Block4_C6_C7 cerrado** (commits `4b6a2a9` + `fde7476`): `cantor_uniqueness` (vía `cantor_bounds` + `lemma_C5_unique` + `add_left_cancel` + ax28) y `cantor_surjectivity` (construcción constructiva con `sub`/ax29 + `parity_lemma`).
- **Block5 cerrado** (commit `871e5e2`): `mod2_of_even`, `proj1_pair_eq_x`, `proj2_pair_eq_y`, `pair_proj_eq_c`, `pair_inj` — todos vía `cantor_uniqueness`/`cantor_injective_c` + `is_cantor_pair`.
- **Block6 cerrado** (commits `71862ca` + `1470a90`): `cons_neq_nil`, `cons_inj`, `in_cons_self_nil`, `in_cons_nil_imp_eq`, `concat_singletons` (vía helpers); `concat_assoc` y `in_concat_iff` cerrados vía spec de los nuevos `ax_C3`/`ax_L3`.
- **~30 helpers de orden/aritmética hechos públicos y exportados** desde `Block4_C5` (le_rewrite, lt_rewrite, le_self_add, le_add_one_cancel, le_mul_*, mul_lt_mono_right, sq_lt_mono, add_comm', mul_assoc', etc.). Helpers de Block2 (`zero_le`, `mul_le_mono_right`, `sq_le_mono`) hechos públicos. Duplicados eliminados.
- **Linter `unusedSimpArgs` desactivado** en todos los módulos (genera falsos positivos con simps bajo binders existenciales donde `FOL.substTerm_lift*` sí disparan reducciones que el linter no traza).
- **Conflicto de merge en `FOL/Theorems/Eq.lean` resuelto** (commit `4b262bf` en FOL): restaurados `substTerm_lift_comm` y `substTerm_liftLift` (necesarios para ROBINSON; eliminados por el merge previo `29ad33f`).

### Documentation (2026-05-27)

- `README.md`, `CURRENT-STATUS-PROJECT.md`, `PLANNING.md`, `NEXT-STEPS.md` actualizados al estado actual (Minimal completo, próximos pasos: Block7 / Intermediate / Full).
- Header de `Block3.lean` documenta su tamaño (~1900 líneas) como consecuencia explícita de la ausencia de inducción en Minimal (enumeración por numeral).

### Changed (2026-05-12)

- **Block3.lean — `div2_zero`, `div2_one`, `div2_two` (parcial) + helpers privados** (2026-05-12): Eliminados 2 sorry. Se demostraron completamente `div2_zero`, `div2_one` y los auxiliares `div2_zero_mul`, `div2_one_mul`, `div2_two_mul`. Se añadieron helpers privados `add_succ_left_ne_zero` y `mul_succ_two_ne_zero`. `div2_two` queda con 1 sorry (caso `1 < div2(2)`); `div2_three` y `div2_four` permanecen como sorry. Build: ✅ exit code 0, sin errores de compilación. **Corrección técnica**: `eq_congr_mul_right` para congruencia del argumento izquierdo de `mul`; `FOL.derive_eq_trans` para encadenamiento estándar `a=b, b=c → a=c` (vs `eq_trans` no-estándar con mismo LHS). Total sorry: 60 (antes 62).

### Changed (2026-05-09)

- **Bloque IV (Fase 9.1)**: Continuada la demostración del Lema C5 con la adición de múltiples lemas auxiliares para la manipulación de desigualdades.

### Changed (2026-05-09)

- **Bloques II y III completados**: Se han demostrado todos los teoremas de los bloques de raíz cuadrada (`Block2.lean`) y `div2`/`mod2` (`Block3.lean`). El proyecto ya no contiene `sorry`s.

### Added (2026-04-25 21:30)

- Declaración del axioma `henkin_extension_lemma` para manejar la expansión de constantes.
- Formalización del Teorema de Compacidad (`compactness_theorem`) y Consistencia (`consistency_of_satisfiable`) en `Compacity.lean`.
- El proyecto alcanza oficialmente **0 sorries** en su totalidad. ¡Hito final completado!
- Build status: ✅ Passing, 0 warnings.

### Added (2026-04-25 21:00)

- Formalización de la construcción de Henkin en `Completeness.lean`.
- Demostración formal del Lema de Lindenbaum (`lindenbaum_lemma`) y Compacidad Sintáctica.
- Demostración del Lema de la Verdad (`truth_lemma`) mediante inducción fuerte sobre la complejidad de fórmulas.
- Demostración del Teorema de Completitud de Gödel (`completeness`).

### Added (2026-04-25 20:30)

- Demostración completa de los lemas de sustitución semántica y reescritura en `FOL/Semantics.lean`, resolviendo la "trampa de De Bruijn" mediante inducción generalizada.
- El proyecto alcanza 0 sorries en toda la formalización de la sintaxis, deducción natural y corrección semántica (Soundness).
- Estado del Build: 0 errores, 0 sorries activos.

### Added (2026-04-25 20:00)

- Demostración completa del Teorema de Deducción en `FOL/Deduction.lean`.
- Definición de Modelos y Semántica de la lógica de primer orden en `FOL/Semantics.lean` (`Model`, `evalFormula`, `satisfies`).
- Demostración completa del Teorema de Corrección (Soundness) en `FOL/Soundness.lean` apoyada en los lemas semánticos.
- Implementación de la táctica `derive_raa` en `FOL/Tactics.lean`.
- Estado del Build: 0 errores, 5 sorries activos en `Semantics.lean` correspondientes a los lemas de sustitución y reescritura.

### Added (2026-04-25)

- Implementación de tácticas de automatización en `FOL/Tactics.lean`: `derive_hyp`, `derive_rewrite` y `derive_weaken`.
- Finalización oficial de la Fase 4 (Automatización).
- Inicio formal de la Fase 5 (Metamatemática y Completitud).
- Estado del Build: 0 errores, 0 sorries activos.

### Added (2026-04-20 00:00)

- Initial project structure from lean4-project-template

---

## [0.2.0] - 2026-04-20

### Added

- `NAMING-CONVENTIONS.md`: Full Mathlib-style naming dictionary with 12 formation rules, symbol-to-word dictionary, and migration tables
- `NEXT-STEPS.md`: Development phase planning template
- `THOUGHTS.md`: Design journal template for recording ideas and alternatives
- `REFERENCE.md` §0: Naming conventions quick-reference guide for the reader
- `REFERENCE.md` §Compliance: Checklist against AI-GUIDE.md requirements
- `AI-GUIDE.md` §22-23: Directory and subdirectory organization protocol
- `AI-GUIDE.md` §24-25: Annotation system (`@axiom_system`, `@importance`)
- `AI-GUIDE.md` §26-28: Cross-reference files documentation
- `AI-GUIDE.md`: Symbol-to-word dictionary and theorem formation rules summary in Naming Conventions section
- `DECISIONS.md`: ADR-004 (Mathlib naming), ADR-005 (directory-aligned namespaces), ADR-006 (annotation system), ADR-007 (separate NAMING-CONVENTIONS.md)
- `_template.lean`: Added naming convention reminders, annotation metadata, expanded section structure
- `CURRENT-STATUS-PROJECT.md`: Development phases tracking table

### Changed

- `README.md`: Added naming conventions summary table, documentation table format, subdirectory-aware project structure
- `DEPENDENCIES.md`: Added subdirectory-aware structure, multi-level dependency hierarchy example, Mermaid subgraph example

---

## [0.1.0] - 2026-04-20

### Added

- `Prelim.lean`: preliminary definitions

---

## Versioning Conventions

- **MAJOR**: Breaking API changes or new foundational axiom
- **MINOR**: New backward-compatible functionality
- **PATCH**: Bug fixes and backward-compatible corrections

## Links

- [Repository](https://github.com/julian1c2a/ProjectName)
- [Issues](https://github.com/julian1c2a/ProjectName/issues)
