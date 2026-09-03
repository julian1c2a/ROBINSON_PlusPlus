# REFERENCE — Incompletitud Nivel D · Gödel I/II, D1–D3, Σ₁-completitud provable · ROBINSON_PlusPlus

> **Nodo temático** del sistema REFERENCE (árbol; ver `AI-GUIDE.md` §0.5). Es el subsistema **activo**
> del proyecto. Índice raíz: [REFERENCE.md](../REFERENCE.md).
> **Nodos relacionados:** [Gödelización](REFERENCE-Godelization.md) (`formCode`/`provCodeC'`, base de
> todo Nivel D), [Núcleo](REFERENCE-Kernel.md) (esquemas del verificador `lineWF`/`premsOf`, axiomas
> `lenc`/`nthc`/`ax_lineWF_inv`/`ax_lineWF_cons`), [Full](REFERENCE-Full.md) (`ax_induction`/`numeral`
> → reglas `ind`/`listInd`).
> **Ficheros `.lean`:** la cadena `Meta/` (86 módulos en el build, barrel
> [Meta.lean](../ROBINSON_PlusPlus/Meta.lean)) más los **0 módulos en `cuarentena/`**, que **NO están
> en el build** (ver [cuarentena/README.md](../cuarentena/README.md)).

**Contenido:** la aritmetización real de las condiciones de Hilbert-Bernays sobre el cálculo finitario
`Prf` — Gödel I (`goedel_first_numeral`), D1 (`repr_pos'_prf`), D2 (`d2_prf`), Gödel II núcleo
(`goedel_second'`, módulo `axiom d3`), y la construcción **en curso** de D3.
**Last updated:** 2026-08-23 (repatriación completa) · Lean v4.31.0.

> ## ⚠️ ESTADO REAL — 2026-08-23 · repatriación paso 1 hecha
>
> **Build 122 jobs · 108 módulos activos** (Minimal 11 + Meta 86 + Full 11) **+ 0 en `cuarentena/`
> + 10 `sondeos/` · 7 `axiom` de Lean · 141 axiomas objeto · 0 errores / 0 warnings / 0 sorrys.**
>
> ### Dos cambios estructurales que este nodo documenta a partir de §3.24
>
> 1. **La REPARACIÓN (2026‑08‑18/19, [ADR‑012](../DECISIONS.md)).** `ax_tc_cons` **retirado** de
>    `axioms`: hacía la teoría objeto **inconsistente**. Los códigos de Gödel pasan a escribirse como
>    **NUMERALES** (`numeral (codeNat φ)`), no como árboles `cons`. En consecuencia:
>    * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO
>      EXISTEN.** Gödel I es hoy **`goedel_first_numeral`** (§3.24.2), sobre la sentencia `godelCN`.
>    * 21 módulos a **cuarentena** ([ADR‑013](../DECISIONS.md)) — sus teoremas eran formalmente
>      correctos pero **vacuos**, probados sobre una teoría que probaba ⊥.
>    * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
> 2. **La ESCALERA (a.2, 2026‑08‑19/22).** La Σ₁‑completitud **internalizada** que devuelve la
>    cuarentena: `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (§3.25). **Completa.**
>
> **Secciones §3.15–§3.23 son ANTERIORES a la reparación.** Lo que describen sobre la capa rastreada
> (los 21 tags, `hI_dot`, el chasis, el KIT) sigue siendo una descripción fiel del **código en
> `cuarentena/`**, pero **ese código no está en el build** y sus enunciados cambiarán al repatriarse
> (los códigos estáticos pasan de `termCode (formCode φ)` a `termCode (numeral (codeNat φ))`).

---

## Descripción de módulos

### 3.15 `Meta/Incompleteness.lean` — Incompletitud Nivel D (Fase 19) — 🗑️ **MÓDULO ELIMINADO**

> ⚠️ **Registro histórico, no código vigente.** El fichero se **borró en F7a** (2026‑07‑09, commit
> `f03eacf`) junto con sus 7 postulados legacy. Ninguna de las declaraciones que siguen existe hoy.
> Se conserva la sección porque el libro (`PLAN-LIBRO.md` Parte IV) la cita como registro del
> episodio: `provFormula_repr` era **falso en general**, y de ahí venía la mitad `⊬¬G` de Gödel I
> que hubo que retirar. **No revertir F7a** — fue un arreglo de solidez.

**Namespace**: `ROBINSON_PlusPlus.Meta.Incompleteness` *(inexistente)*
**Status**: 🗑️ Eliminado en F7a — Gödel I (mitad esencial) + Gödel II, postulando D2/D3
**@importance**: `high`
**Last updated**: 2026-06-12
**Dependencias**: `Axioms`, `Meta/Godel`, `Meta/Provability`, `FOL.*`.

Deriva los teoremas de incompletitud a partir de las condiciones de demostrabilidad del Nivel C (D1 vía `provFormula_repr`; diagonalización vía `goedelSentence_fixedpoint`) + D2/D3 postuladas.

```lean
noncomputable def provCode (φ) : Formula := substFormula 0 (formCode φ) provFormula   -- Prov(⌜φ⌝)
def Consistent : Prop := ¬ (axioms ⊢ Formula.bottom)
-- Primer Teorema (mitad esencial):
theorem goedel_first_unprovable (hcon : Consistent) : ¬ (axioms ⊢ goedelSentence)
theorem goedel_first_true (hcon) : ¬ Provable (formCode goedelSentence)   -- G verdadera-pero-indemostrable
theorem incompleteness (hcon) : ∃ φ, ¬ (axioms ⊢ φ)
-- Segundo Teorema (postulando D2, D3):
axiom D2 (A B) : axioms ⊢ (provCode (A ⇒ B) ⇒ (provCode A ⇒ provCode B))
axiom D3 (A)   : axioms ⊢ (provCode A ⇒ provCode (provCode A))
noncomputable def consistencyFormula : Formula := neg (provCode Formula.bottom)   -- Con := ¬Prov(⌜⊥⌝)
theorem con_imp_goedelSentence : axioms ⊢ (consistencyFormula ⇒ goedelSentence)   -- Gödel I formalizado
theorem goedel_second (hcon : Consistent) : ¬ (axioms ⊢ consistencyFormula)       -- ⊬ Con
```

**Clave**: toda la cadena HBL de Gödel II (incl. la contrapositiva) se construye con `imp_intro`/`mp`, **sin DNE object-level**.

> ⚠️ **Corrección de auditoría (2026-07-13).** Aquí se afirmaba que la otra mitad de Gödel I (`⊬ ¬G`)
> quedó cerrada el 2026-06-13 vía `dne` clásica (`goedel_first_unrefutable`/`goedel_first_undecidable`).
> **Eso era cierto sólo en la capa LEGACY** (`Meta/Incompleteness.lean`, que postulaba D2/D3), y esa capa
> se **RETIRÓ en F7a** (`f03eacf`): **esos dos teoremas ya no existen en el código**. La cadena real
> establece **sólo `⊬G`**. La **indecidibilidad de `G` está PENDIENTE** de re‑derivar sobre la cadena
> real (tarea abierta, independiente de D3).
>
> ↻ **Actualización 2026‑08‑23:** el `goedel_first_real'` que esta nota citaba como «la cadena real»
> **tampoco existe ya** — cayó con la reparación (ADR‑012). Hoy `⊬G` es **`goedel_first_numeral`**
> (§3.24.5). El diagnóstico de la nota sigue siendo válido palabra por palabra: falta `NegVerifier`.

---

### 3.16 Nivel D REAL — aritmetización de D1–D3 (Fases 0–2.2t)

Conversión de D1/D2/D3 de **postulados** a **teoremas** sobre un cálculo de Hilbert finitario nuevo. Plan: [GODEL-D-ARITHMETIZATION.md](../GODEL-D-ARITHMETIZATION.md). El `axioms ⊢` del proyecto usa la ω-regla (no r.e.), así que Gödel se aplica a `Prf` (finitario, paralelo); el ω-sistema queda intacto.

**`Meta/Hilbert.lean`** (Fase 0) — namespace `…Meta.Hilbert`:

```lean
theorem subst_lift_same (f) (c) (s) : substFormula c s (liftFormula c f) = f
inductive Prf₀ : Formula → Prop   -- Hilbert intuicionista (P1/P2, C, J, efq, Q1-3, refl, leibniz, thy, mp, gen)
inductive Prf  : Formula → Prop   -- clásico: incl (Prf₀) + p3 (DNE) + mp + gen
theorem prf0_to_derives : Prf₀ φ → axioms ⊢ φ   -- SOLO constructores de Derives (sin dne)
theorem prf_to_derives  : Prf φ → axioms ⊢ φ    -- + dne en un único punto (esquema p3)
theorem consistentH_of_omega : ¬(axioms ⊢ ⊥) → ¬ Prf ⊥
-- #print axioms: prf0 sin dne; prf con FOL.MetaRules.dne (diferencia exacta = {dne})
```

**`Meta/HilbertSeq.lean`** (Fase 1) — namespace `…Meta.HilbertSeq`:

```lean
inductive Rule   -- líneas anotadas (evita invertir la sustitución)
def checkProof : List Rule → Option (List Formula)   -- verificador decidible (DecidableEq Term/Formula)
def Derivation (rs) (φ) : Prop := ∃ L, checkProof rs = some L ∧ φ ∈ L
theorem derivation_to_prf : Derivation rs φ → Prf φ            -- solidez
theorem prf_to_derivation : Prf φ → ∃ rs, Derivation rs φ       -- completitud (checkAux_append/_shift)
theorem prf_iff_derivation : Prf φ ↔ ∃ rs, Derivation rs φ
def ruleCode : Rule → Term ;  def rulesCode : List Rule → Term  -- coding de Gödel
def Dem (d x : Term) : Prop  -- "d codifica derivación válida con la fórmula de código x" (concreto)
def ProvableH (x : Term) : Prop := ∃ d, Dem d x
theorem dem_tracks (φ) : ProvableH (formCode φ) ↔ Prf φ         -- reemplaza dem_iff_provable
```

**`Meta/CodeArith.lean`** (Fase 2.1) — namespace `…Meta.CodeArith`:

```lean
theorem numeral_bridge (n) : Meta.Godel.numeral n = Full.numeral n
theorem gnum_ne {a b} (h : a ≠ b) : axioms ⊢ neg (numeral a =eq numeral b)   -- separación
theorem gnum_lt {a b} (h : a < b) : axioms ⊢ lt (numeral a) (numeral b)
theorem gnum_add (a b) : axioms ⊢ (add (numeral a) (numeral b) =eq numeral (a+b))   -- + gnum_mul, gnum_refl
```

**`Minimal/Axioms.lean`** (extensión definicional para coding): `varc`/`funcc` (códigos de `Term.var`/`Term.func`), `substtc`/`substtsc` (sustitución aritmetizada), `forall_4`, y 6 ecuaciones recursivas `ax_substtc_*`/`ax_substtsc_*` añadidas a `axioms`.

**`Meta/SubstArith.lean`** (Fase 2.2 nivel término) — namespace `…Meta.SubstArith`:

```lean
theorem congr_cons_head / congr_cons_tail   -- congruencia de cons (patrón eq_congr)
theorem pred_numeral (m) : axioms ⊢ (pred (numeral (m+1)) =eq numeral m)
theorem substTerm_liftLiftLift   -- cancelación de triple lift (para instanciar forall_4)
-- ecuaciones recursivas re-derivadas como TEOREMAS (de Minimal.axioms, vía ax+spec):
theorem substtc_var_eq / _var_gt / _var_lt / _func ;  theorem substtsc_nil / _cons
theorem substTerm_arith (v) (s) (t) : axioms ⊢ (substtc (numeral v) (termCode s) (termCode t) =eq termCode (substTerm v s t))
theorem substTerms_arith ...   -- mutuo; cómputo object de la sustitución (nivel término)
theorem liftTerm_arith / liftFormula_arith ; theorem substFormula_arith   -- nivel fórmula (con binders)
-- lemas de lift: substTerm_liftLiftLift (3-lift), substTerm_liftLiftLiftLift (4-lift)
-- #print axioms substFormula_arith = solo axiomas estándar de Lean (0 postulados nuevos)
```

**`Meta/StepArith.lean`** (Fase 2.3) — `…Meta.StepArith`:

```lean
theorem q1_concl_code / q2_concl_code / leibniz_concl_code   -- el código de la conclusión de
  -- los esquemas de sustitución, reconstruido con substfc, coincide con formCode (vía substFormula_arith)
```

**`Meta/CheckArith.lean`** (Fase 2.4) — `…Meta.CheckArith`:

```lean
theorem numeralM_eq (n) : numeralM n = Godel.numeral n
theorem carc_cons / cdrc_cons   -- cómputo de los extractores cabeza/cola
-- 17 step lemmas del verificador (re-derivadas de Minimal.axioms):
theorem vpf_nil/p1/p2/c1/c2/c3/j1/j2/j3/efq/q1/q2/q3/eqrefl/leibniz/p3   -- incondicionales
theorem vpf_mp (… h1 h2) / vpf_gen (… h1)   -- condicionales por pertenencia In
def provFormulaC : Formula := Formula.ex (In (var 1) (validProofFn nil (var 0)))   -- demostrabilidad Σ₁
noncomputable def provCodeC (φ) := substFormula 0 (formCode φ) provFormulaC
```

---

### 3.17 Gödel II finitario en `Prf` — cadena HBL sobre `provCodeC'` (Fases 3–5)

Re-nivelación de la cadena Hilbert-Bernays-Löb al cálculo finitario `Prf` (Gödel II es
`¬ Prf Con'`; `provCodeC'` rastrea `Prf`, no ω). Predicado estructural fiel
`provCodeC' φ := ∃p, chainOk nil p ∧ In ⌜φ⌝ (runFn nil p)` (`Meta/ProofChain.lean`).

**`Meta/HilbertDeduction.lean`** — namespace `…Meta.HilbertDeduction`:

```lean
inductive PrfH : List Formula → Formula → Prop   -- cálculo con contexto (espejo de Prf + hyp)
theorem deduction_aux {Δ B} (h : PrfH Δ B) : ∀ A Γ, Δ = A :: Γ → PrfH Γ (A ⇒ B)
theorem prf_deduction {A B} (h : PrfH [A] B) : Prf (A ⇒ B)
theorem prf_ex_elim_imp {A C} (h : PrfH [A] (liftFormula 0 C)) : Prf (Formula.ex A ⇒ C)
theorem prf_to_prfH {φ} (h : Prf φ) : ∀ Γ, PrfH Γ φ  ;  theorem prfH_hyp_self (A) : PrfH [A] A
theorem PrfH_ex_intro {Γ A} (t) (h : PrfH Γ (substFormula 0 t A)) : PrfH Γ (Formula.ex A)   -- q2
theorem PrfH_ex_elim {Γ A C} (hex : PrfH Γ (Formula.ex A))
  (hbody : PrfH (A :: Γ.map (liftFormula 0)) (liftFormula 0 C)) : PrfH Γ C                   -- q3+gen
-- #print axioms prf_deduction/prf_ex_elim_imp = [propext, Classical.choice, Quot.sound]
```

**`Meta/ArithPrf.lean`** / **`Meta/Representability2Prf.lean`** / **`Meta/ReprPrf.lean`** (Fase 3, D1):

```lean
theorem prf_substTerm_arith / prf_substTerms_arith / prf_liftTerm_arith   -- aritmética de códigos en Prf
theorem prf_congr_substfc_arg2 / _arg3   -- congruencias de substfc
theorem provCodeC'_intro_prf (φ) (p) (h1 : Prf (chainOk nil p)) (h2 : Prf (In (formCode φ) (runFn nil p)))
  : Prf (provCodeC' φ)
theorem repr_pos'_prf {φ} (h : Prf φ) : Prf (provCodeC' φ)   -- D1 finitaria (necesitación)
-- ReprPrf: prf_runFn_nil/cons, prf_congr_runFn_1/2, prf_chainOk_nil/cons/subst1, prf_allIn_nil/cons,
--   prf_in_cons_head/tail, prf_eq_trans/symm, prf_concat_nil_eq/cons_eq, prf_carc_cons, 32 lineWF/premsOf
-- #print axioms repr_pos'_prf = [propext, Classical.choice, Quot.sound, prf_inAxC]
```

**`Meta/ChainPrf.lean`** (Fase 4, paso 8) — namespace `…Meta.ChainPrf`: **10 lemas de cadena en `Prf`**
vía el eliminador de inducción de listas + normalización De Bruijn + confinación.

```lean
theorem prf_list_induction (Φ) (base : Prf (substFormula 0 nil Φ)) (step) : Prf (Formula.forall Φ)
theorem norm21 (s t) : substTerm 0 s (liftTerm 2 (liftTerm 1 (liftTerm 0 t))) = liftTerm 1 (liftTerm 0 t)
theorem norm32 (z t) : substTerm 1 z (liftTerm 3 (liftTerm 2 (liftTerm 0 (liftTerm 0 t))))
  = liftTerm 2 (liftTerm 0 (liftTerm 0 t))                       -- profundidad 2 (para ∀c interno)
theorem norm_s (z s) : substTerm 0 z (liftTerm 1 (liftTerm 2 (liftTerm 0 (liftTerm 0 s))))
  = liftTerm 2 (liftTerm 0 (liftTerm 0 s))                       -- cancela lift de confinación
theorem prf_concat_nil_right (X) : Prf (concat X nil =eq X)  ;  theorem prf_concat_assoc (M N L)
theorem prf_In_mono (x c c0) (h : Prf (In x c)) : Prf (In x (concat c0 c))  ;  prf_In_mono_imp
theorem prf_In_mono_right (x M L) (h : Prf (In x L)) : Prf (In x (concat L M))  ;  prf_In_mono_right_imp
theorem prf_allIn_mono_imp / prf_lineOk_mono_imp / prf_chainOk_subst2
theorem prf_runFn_concat (c p s) : Prf (runFn c (concat p s) =eq runFn (runFn c p) s)   -- keystone
theorem prf_chainOk_mono_imp (c0 c p) : Prf (chainOk c p ⇒ chainOk (concat c0 c) p)
theorem prf_runFn_weaken (c p) : Prf (runFn c p =eq concat c (runFn nil p))
theorem prf_chainOk_concat (c p s) : Prf (chainOk c (concat p s) ⇔ land (chainOk c p) (chainOk (runFn c p) s))
-- helpers PrfH: PrfH_spec, PrfH_and_intro/elim, PrfH_iff_mp/mpr, PrfH_eq_trans/symm,
--   PrfH_or_elim, PrfH_congr_cons_head/tail/concat_left, PrfH_chainOk_subst1/2, PrfH_allIn_subst2,
--   PrfH_eq_subst_in, PrfH_in_cons_head/tail
-- #print axioms de todos = [propext, Classical.choice, Quot.sound]
```

**`Meta/DerivCondPrf.lean`** (Fase 4, D2) — namespace `…Meta.DerivCondPrf`:

```lean
theorem liftTerm_numeral / liftTerm_charsCode / liftTerm_strCode / liftTerm_termCode / liftTerm_formCode
  -- clausura: los códigos de Gödel son cerrados (invariantes bajo liftTerm)
theorem liftFormula_provCodeC' (c) (φ) : liftFormula c (provCodeC' φ) = provCodeC' φ
theorem d2_prf (A B) : Prf (provCodeC' (A ⇒ B) ⇒ (provCodeC' A ⇒ provCodeC' B))   -- D2 finitaria real
-- #print axioms d2_prf = [propext, Classical.choice, Quot.sound]   (sin postulados, ni prf_inAxC)
```

**`Meta/ReflectionPrf.lean`** (Fase 5, D3 reducida) — namespace `…Meta.ReflectionPrf`:

```lean
theorem PrfH_pcc_mp {Γ A B} (h1 : PrfH Γ (provCodeC' (A ⇒ B))) (h2 : PrfH Γ (provCodeC' A))
  : PrfH Γ (provCodeC' B)                                        -- MP interno (D2), versión PrfH
theorem PrfH_pcc_prf {Γ φ} (h : Prf φ) : PrfH Γ (provCodeC' φ)   -- D1 interno
theorem PrfH_pcc_andIntro / PrfH_pcc_exIntro                     -- ∧-intro (c1) / ∃-intro (q2) internos
theorem d3_prf_of_sigma1 (φ)
  (hC : ∀ p, Prf (chainOk nil p ⇒ provCodeC' (chainOk nil p)))
  (hI : ∀ x L, Prf (In x L ⇒ provCodeC' (In x L)))
  : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ))               -- D3 reducida a la Σ₁-completitud
-- #print axioms d3_prf_of_sigma1 = [propext, Classical.choice, Quot.sound, prf_inAxC]
```

**`Meta/Sigma1Prf.lean`** (Fase 5, núcleo de D3) — namespace `…Meta.Sigma1Prf`: infraestructura de
reflexión Σ₁ (hacia `hC`/`hI`).

```lean
theorem pcc_imp {A B} (h : Prf (A ⇒ B)) : Prf (provCodeC' A ⇒ provCodeC' B)   -- MP interno como esquema
theorem pcc_imp2 {A B C} (h : Prf (A ⇒ (B ⇒ C))) : Prf (provCodeC' A ⇒ (provCodeC' B ⇒ provCodeC' C))
def provFromCode (c : Term) : Formula := substFormula 0 c provFormulaC'   -- demostrabilidad de un código
theorem provCodeC'_eq_provFromCode (φ) : provCodeC' φ = provFromCode (formCode φ)
theorem prf_provCode_congr {c₁ c₂} (h : Prf (c₁ =eq c₂)) : Prf (provFromCode c₁ ⇒ provFromCode c₂)
  -- la demostrabilidad respeta la igualdad de códigos (Leibniz object; [propext, choice, Quot.sound])
theorem pcc_eq_of_codeEq (x y)
  (hcode : Prf ((x =eq y) ⇒ (formCode (Formula.eq x x) =eq formCode (Formula.eq x y))))
  : Prf ((x =eq y) ⇒ provCodeC' (x =eq y))   -- reflexión de igualdad REDUCIDA a la igualdad de códigos
theorem pcc_in_head (x t) : Prf (provCodeC' (In x (cons x t)))   -- reflexión de In (base cabeza)
theorem pcc_in_tail (hd x t) : Prf (provCodeC' (In x t) ⇒ provCodeC' (In x (cons hd t)))
theorem pcc_in_head_eq (hd x t) : Prf (provCodeC' (x =eq hd) ⇒ provCodeC' (In x (cons hd t)))
theorem pcc_in_nil (x) : Prf (In x nil ⇒ provCodeC' (In x nil))
theorem pcc_chainOk_nil (c) : Prf (provCodeC' (chainOk c nil))
theorem pcc_chainOk_cons (c line rest) : Prf (provCodeC' (lineOk c line) ⇒
  (provCodeC' (chainOk (concat c (cons (carc line) nil)) rest) ⇒ provCodeC' (chainOk c (cons line rest))))
theorem pcc_allIn_nil (c) : Prf (provCodeC' (allIn c nil))
theorem pcc_allIn_cons (c x t) : Prf (provCodeC' (In x c) ⇒
  (provCodeC' (allIn c t) ⇒ provCodeC' (allIn c (cons x t))))
-- #print axioms pcc_imp = [propext, Classical.choice, Quot.sound, prf_inAxC]
-- NOTA (núcleo duro pendiente): la reflexión de igualdad universal `∀x y` es indemostrable
--   (obstrucción Tarski: `termCode` es meta, no object; solo vale para términos-código vía tcFn).
--   La Σ₁-completitud real (`hC`/`hI`) debe reformularse al nivel del código object (tcFn/substfc).
```

**`Meta/TcArithPrf.lean`** (Fase 5, cimiento código object) — namespace `…Meta.TcArithPrf`: porte
finitario de la cadena `tc_arith` de `Diagonal.lean` (ω) → `Prf`. `tcFn` (función object,
`Minimal/Axioms.lean`) computa `termCode`.

```lean
theorem prf_tc_zero : Prf (tcFn zero =eq termCode zero)
theorem prf_tc_succ (x) : Prf (tcFn (succ x) =eq cons (numeral 1) (cons (strCode succ_sym) (cons (cons (tcFn x) nil) nil)))
theorem prf_tc_cons (a b) : Prf (tcFn (cons a b) =eq ⌜::·⌝[tcFn a, tcFn b])
theorem prf_tc_numeral (n) : Prf (tcFn (numeral n) =eq termCode (numeral n))   -- inducción meta
theorem prf_tc_of_cons {a b} (ha : Prf (tcFn a =eq termCode a)) (hb : Prf (tcFn b =eq termCode b))
  : Prf (tcFn (cons a b) =eq termCode (cons a b))
theorem prf_tc_chars / prf_tc_str / prf_tc_term / prf_tc_terms   -- mutuas
theorem prf_tc_form (φ) : Prf (tcFn (formCode φ) =eq termCode (formCode φ))   -- código del código
theorem prf_congr_tcFn {t₁ t₂} (h : Prf (t₁ =eq t₂)) : Prf (tcFn t₁ =eq tcFn t₂)   -- congruencia Leibniz object
-- #print axioms = [propext, Classical.choice, Quot.sound]
-- Cimiento del enfoque de código object: `tcFn` es función object con congruencia Leibniz
-- (a diferencia de la `termCode` meta que causa la obstrucción Tarski).
```

**`Meta/Sigma1CorePrf.lean`** (Fase 5, capa de código object para `In`) — namespace `…Meta.Sigma1CorePrf`:
primera piedra de la reformulación de `hI` al nivel del código object. El obstáculo es que
`formCode (In x L)` contiene `termCode L` (**meta**, stuck para `L` abstracta); la salida es
construir el código del átomo con una **función object** de los códigos de sus argumentos, para
que la demostrabilidad respete su igualdad (Leibniz object vía `provFromCode`).

```lean
def inFormCodeFn (xc Lc : Term) : Term := cons (numeral 3) (cons (strCode in_sym) (cons (cons xc (cons Lc nil)) nil))
  -- constructor object del código del átomo In: ⟨3, ⌜∈⌝, [xc, Lc]⟩
theorem inFormCodeFn_termCode (x L) : inFormCodeFn (termCode x) (termCode L) = formCode (In x L)   -- puente rfl
theorem provCodeC'_In_eq (x L) : provCodeC' (In x L) = provFromCode (inFormCodeFn (termCode x) (termCode L))   -- rfl
theorem prf_congr_inFormCodeFn {xc xc' Lc Lc'} (hx : Prf (xc =eq xc')) (hL : Prf (Lc =eq Lc'))
  : Prf (inFormCodeFn xc Lc =eq inFormCodeFn xc' Lc')   -- congruencia en ambos args
theorem prf_provFromCode_In_congr {xc xc' Lc Lc'} (hx : Prf (xc =eq xc')) (hL : Prf (Lc =eq Lc'))
  : Prf (provFromCode (inFormCodeFn xc Lc) ⇒ provFromCode (inFormCodeFn xc' Lc'))   -- transporte por igualdad de códigos
theorem prf_provCodeC'_In_of_tracked {x L xc Lc} (hx : Prf (xc =eq termCode x)) (hL : Prf (Lc =eq termCode L))
  (h : Prf (provFromCode (inFormCodeFn xc Lc))) : Prf (provCodeC' (In x L))   -- puente rastreado → provCodeC'
theorem prf_provCodeC'_In_formCode_of_tracked {φ L} (hL : Prf (tcFn L =eq termCode L))
  (h : Prf (provFromCode (inFormCodeFn (tcFn (formCode φ)) (tcFn L)))) : Prf (provCodeC' (In (formCode φ) L))
  -- especialización x=⌜φ⌝ (1er arg cerrado por prf_tc_form)
-- — Reflexión de In sobre listas explícitas + tracking runFn→objList (testigos CONCRETOS) —
def objList : List Term → Term            -- objList [] = nil ; objList (e::es) = cons e (objList es)
theorem pcc_in_objList_of_mem (x) (elems) : List.Mem x elems → Prf (provCodeC' (In x (objList elems)))
  -- reflexión de In por META-pertenencia (cabeza = pcc_in_head INCONDICIONAL; sortea reflexión de igualdad)
theorem prf_runFn_objList (lines c) : Prf (runFn c (objList lines) =eq concat c (objList (lines.map carc)))
theorem prf_runFn_nil_objList (lines) : Prf (runFn nil (objList lines) =eq objList (lines.map carc))  -- axiomas puros
theorem pcc_in_runFn_objList (x lines) (hmem : List.Mem x (lines.map carc))
  : Prf (provCodeC' (In x (runFn nil (objList lines))))   -- = hI para testigos CONCRETOS
-- — A‑F1: tcFn = termCode sobre la forma de la lista de conclusiones —
theorem prf_tc_objList (cs) (h : ∀ c, List.Mem c cs → Prf (tcFn c =eq termCode c))
  : Prf (tcFn (objList cs) =eq termCode (objList cs))
theorem prf_tc_objList_formCode (φs) : Prf (tcFn (objList (φs.map formCode)) =eq termCode (objList (φs.map formCode)))
-- — A‑F2: puente RASTREADO→real (mecanismo central de la Opción A) —
theorem prf_provCodeC'_of_tracked_witness (A p) (hp : Prf (tcFn p =eq termCode p))
  (h : Prf (provFromCode (substfc (numeral 0) (tcFn p) (formCode A)))) : Prf (provCodeC' (substFormula 0 p A))
  -- reflexión rastreada con testigo-código = provCodeC' real; el tcFn NO se absorbe (slot-término genuino)
-- #print axioms = [propext, Classical.choice, Quot.sound]  (pcc_* añaden prf_inAxC, ancla de coding benigna)
theorem prf_lineOk_q2 (c Ac w) : Prf (lineOk c (cons (implc (substfc zero w Ac) (exc Ac))
  (cons (numeralM 10) (cons Ac (cons w nil)))))   -- línea-axioma Q2 válida en cualquier contexto (A‑F3 base)
```

**`Meta/ExIntroCodePrf.lean`** (A‑F3/A‑F4) — namespace `…Meta.ExIntroCodePrf`: ∃‑intro de la
regla Q2 al nivel de CÓDIGO + clausuras De Bruijn.

```lean
theorem liftTerm_exc (Ac) (hAc : ∀ c, liftTerm c Ac = Ac) : ∀ c, liftTerm c (exc Ac) = exc Ac
theorem liftFormula_provFromCode_exc (Ac) (hAc) : liftFormula 0 (provFromCode (exc Ac)) = provFromCode (exc Ac)
theorem liftTerm_substfc (Ac w) (hAc) (hw) : ∀ c, liftTerm c (substfc zero w Ac) = substfc zero w Ac
theorem pcc_exIntro_code (Ac w) (hAc : ∀ c, liftTerm c Ac = Ac) (hw : ∀ c, liftTerm c w = w)
  : Prf (provFromCode (substfc zero w Ac) ⇒ provFromCode (exc Ac))
  -- ∃-intro Q2 a nivel código, testigo-código arbitrario CERRADO; ensamblaje p ++ [q2line, mpline]
  -- (tipo d2_prf). #print axioms = [propext, Classical.choice, Quot.sound] (sin postulados)
```

**`Meta/Sigma1TrackedPrf.lean`** (verificación RIESGO‑1) — namespace `…Meta.Sigma1TrackedPrf`:
el ∃‑intro rastreado (`pcc_exIntro_code`, L1) cierra hasta `provCodeC'(∃A)` para testigo CERRADO.

```lean
theorem pcc_exIntro_code_bridge (A p) (hpc : ∀ c, liftTerm c p = p)
  (h : Prf (provFromCode (substfc zero (tcFn p) (formCode A)))) : Prf (provCodeC' (Formula.ex A))
  -- reconciliación definicional exc ⌜A⌝ = ⌜∃A⌝ (numeral 9 = succ⁹ zero)
theorem pcc_exIntro_code_objList (A lines) (hclosed) (h) : Prf (provCodeC' (Formula.ex A))
-- #print axioms = [propext, Classical.choice, Quot.sound]
-- MURO (testigo ABSTRACTO): tcFn #0 NO es cerrado (hw falla) y todo combinador base produce
--   termCode meta (transporte a tcFn stuck para lista abstracta) → hI_tracked abstracto exige la
--   Opción A DE RAÍZ (provFormulaC'ₜ/provCodeC'ₜ con tcFn + D1ₜ). Ver GODEL-D3-TRACKED-DESIGN.md §4.2.
--   Limpieza F7 BLOQUEADA hasta goedel_second_prf real (GodelTwo.goedel_second' aún usa axiom d3).
```

> **NOTA (2026‑07‑05c/d):** el enfoque `tcFn` (§3.17 arriba, Opción A §10 del diseño) quedó
> **DESCARTADO** para el testigo abstracto (investigación §11–§12 de `GODEL-D3-TRACKED-DESIGN.md`;
> el caso cabeza/cola de la inducción exige `tcFn L =eq termCode L`, stuck para `L` abstracta). Se
> verificó además que **no hay atajo** por teorema de deducción (D1 exige `Prf` cerrado). Vía
> genuina = **Σ₁‑completitud provable estándar (12‑A: capa numérica Δ₀ del verificador)**. Los
> constructores `atom2CodeFn` y `pcc_exIntro_code` siguen siendo infraestructura válida.

**`Meta/TrackedCorePrf.lean`** — namespace `…Meta.TrackedCorePrf`: clausura genérica de `provFromCode`

+ constructores de código object para átomos binarios (generaliza `inFormCodeFn`).

```lean
theorem liftFormula_provFromCode (k c) (hc : ∀ lvl, liftTerm lvl c = c)
  : liftFormula k (provFromCode c) = provFromCode c   -- clausura genérica (código cerrado arbitrario)
def atom2CodeFn (s a b : Term) : Term := ⟨3, strCode s, [a, b]⟩   -- código de Formula.atom s [a,b]
theorem atom2CodeFn_termCode (s a b) : atom2CodeFn s (termCode a)(termCode b) = formCode (.atom s [a,b])  -- rfl
theorem inFormCodeFn_eq_atom2 (xc Lc) : inFormCodeFn xc Lc = atom2CodeFn in_sym xc Lc   -- rfl
theorem liftTerm_atom2CodeFn (s a b) (ha hb) : ∀ lvl, liftTerm lvl (atom2CodeFn s a b) = atom2CodeFn s a b
theorem prf_congr_atom2CodeFn {s a a' b b'} (ha : Prf (a =eq a')) (hb : Prf (b =eq b'))
  : Prf (atom2CodeFn s a b =eq atom2CodeFn s a' b')
theorem prf_provFromCode_atom2_congr {s a a' b b'} (ha) (hb)
  : Prf (provFromCode (atom2CodeFn s a b) ⇒ provFromCode (atom2CodeFn s a' b'))
theorem liftFormula_provFromCode_atom2 (k s a b) (ha hb) : liftFormula k (provFromCode (atom2CodeFn s a b)) = provFromCode (atom2CodeFn s a b)
def chainOkCodeFn (cc pc) := atom2CodeFn "chainOk" cc pc   -- + chainOkCodeFn_termCode (rfl)
def allInCodeFn (cc Lc) := atom2CodeFn "allIn" cc Lc        -- + allInCodeFn_termCode (rfl)
```

**`Meta/NumListPrf.lean`** — namespace `…Meta.NumListPrf`: capa numérica de listas en `Prf`
(D3 vía Σ₁‑completitud, §12‑A fase 1a). Ecuaciones `Prf` de `lenc`/`nthc` (re‑derivadas de `axioms`).

```lean
theorem prf_lenc_nil : Prf (lenc nil =eq zero)
theorem prf_lenc_cons (h t) : Prf (lenc (cons h t) =eq succ (lenc t))
theorem prf_nthc_zero (h t) : Prf (nthc (cons h t) zero =eq h)
theorem prf_nthc_succ (h t i) : Prf (nthc (cons h t) (succ i) =eq nthc t i)
```

**Nuevas defs/axiomas en `Minimal/Axioms.lean`** (extensión definicional conservadora, capa numérica
de listas para D3, §12‑A): `lenc l := func "lenc" [l]`, `nthc l i := func "nthc" [l, i]`; axiomas
`ax_lenc_nil` (`lenc nil = 0`), `ax_lenc_cons` (`lenc (cons h t) = σ (lenc t)`), `ax_nthc_zero`
(`nthc (cons h t) 0 = h`), `ax_nthc_succ` (`nthc (cons h t) (σ i) = nthc t i`). Añadidos a `axioms`
y `codingAxioms` (`axioms_eq` rfl preservado; verificador/`prf_iff_derivation`/D1 intactos).

---

### 3.18 Σ₁‑completitud provable — capa numérica Δ₀ del verificador (plan 12‑A)

**Por qué existe esta capa.** El núcleo duro de D3 es la Σ₁‑completitud *provable* del verificador
(`hC`/`hI` de `d3_prf_of_sigma1`). La construcción estándar exige que el cuerpo `δ` del predicado
Σ₁ sea **Δ₀ sobre números** (cuantificadores acotados por términos). Pero el verificador de este
proyecto es **estructural sobre listas** (`carc`/`cdrc`, sin `len`/`nth`) — de ahí el hallazgo
central de §12.1 de `GODEL-D3-TRACKED-DESIGN.md`: **codificar el testigo ≡ representar el
verificador**. La Opción 12‑A construye la capa numérica que falta.

Fases y estado:

| Fase | Contenido | Estado |
|------|-----------|--------|
| 1a | `lenc`/`nthc` (long./índice de lista‑código): defs + 4 axiomas + ecuaciones `Prf` | ✅ |
| 1b | toolkit aritmético de `<` en `Prf` → `In x L ⇔ ∃ i < lenc L. nthc L i =eq x` | ✅ |
| 2 | forma Δ₀ del verificador: `In · (runFn nil p)` y `chainOk c p` | ✅ |
| 3 | `num` (numeral‑de) + evaluación provable | ⏳ |
| 4 | Δ₀‑completitud atómica (aquí entran las ecuaciones de variable de `substfc`) | ⏳ |
| 5 | inducción estructural `⊢ ∀p (δ → Prov ⌜δ(ṗ)⌝)` → `d3_prf` → `goedel_second_prf` | ⏳ |

**`Meta/NumListPrf.lean`** — ver §3.17 (ecuaciones `Prf` de `lenc`/`nthc`).

---

**`Meta/NatArithPrf.lean`** (fase 1b, cimiento) — namespace `…Meta.NatArithPrf`: **toolkit aritmético
de `<` en `Prf`**. Fue el descubrimiento de escala de la fase 1b: como `lt a b := ∃k. a + σk = b`
(`ax13_lt_def`) y `add` recurre **por la derecha** (`ax4`/`ax5`), la identidad izquierda `0 + n = n`
**no es teorema de Q** — hay que reconstruirla con `Prf.ind`. Todo lo demás cuelga de ahí.

```lean
theorem prf_nat_induction (Φ) (base : Prf (substFormula 0 zero Φ))
  (step : Prf (∀ (Φ ⇒ substFormula 0 (succ #0) (liftFormula 1 Φ)))) : Prf (Formula.forall Φ)
  -- eliminador de inducción natural (envuelve `Prf.ind` / `Full.inductionFormula`)
theorem norm11 (s t) : substTerm 0 s (liftTerm 1 (liftTerm 0 t)) = liftTerm 0 t  -- norm De Bruijn 1 binder
theorem prf_add_zero_left  (n)   : Prf (add zero n =eq n)            -- NO es teorema de Q: usa Prf.ind
theorem prf_add_succ_left  (m n) : Prf (add (succ m) n =eq succ (add m n))
theorem prf_lt_iff (a b) : Prf (lt a b ⇔ ∃ (add ↑a (succ #0) =eq ↑b))   -- despliegue de ax13
theorem PrfH_lt_intro {Γ} (a b k) (h : PrfH Γ (add a (succ k) =eq b)) : PrfH Γ (lt a b)
theorem prf_lt_intro (a b k) (h : Prf (add a (succ k) =eq b)) : Prf (lt a b)
theorem prf_succ_ne_zero (n) : Prf ((succ n =eq zero) ⇒ ⊥)   ;  theorem prf_succ_inj (m n)
theorem prf_zero_or_succ (n) : Prf (lor (n =eq zero) (∃ (↑n =eq succ #0)))
theorem prf_zero_lt_succ (n)          : Prf (lt zero (succ n))
theorem prf_succ_lt_succ_of_lt (m n)  : Prf (lt m n ⇒ lt (succ m) (succ n))
theorem prf_lt_of_succ_lt_succ (m n)  : Prf (lt (succ m) (succ n) ⇒ lt m n)
theorem prf_not_lt_zero (n)           : Prf (lt n zero ⇒ ⊥)
theorem PrfH_eq_congr_succ {Γ t₁ t₂} (h : PrfH Γ (t₁ =eq t₂)) : PrfH Γ (succ t₁ =eq succ t₂)
-- #print axioms de todos = [propext, Classical.choice, Quot.sound]
```

**Lección De Bruijn (reusar):** para eliminar un `∃` de una **hipótesis** usar `prf_ex_elim_imp`
(lift simple, casa con el `↑a`/`↑b` que ya trae el cuerpo del `∃`), **nunca `PrfH_ex_elim`** (liftea
además el contexto → doble lift). Y al desplegar `ax13_lt_def` hay que incluir `add` en el simp‑set.

---

**`Meta/BoundedInPrf.lean`** (fase 1b, objetivo) — namespace `…Meta.BoundedInPrf`: la
**caracterización acotada de `In`**.

```lean
def boundedIn (x L : Term) : Formula :=            -- ∃ i < lenc L. nthc L i =eq x   (i = #0)
  Formula.ex (land (lt #0 ↑(lenc L)) (nthc ↑L #0 =eq ↑x))
theorem liftFormula_boundedIn / liftFormula_boundedIn_gen / substFormula_boundedIn
  -- NO son defeq: bajo el ∃, `liftFormula 1` da `liftTerm 1 (liftTerm 0 ·)` y `boundedIn ↑x ↑L`
  -- da `liftTerm 0 (liftTerm 0 ·)`; los iguala `FOL.liftTerm_comm_zero` (teorema)
theorem prf_lt_subst2 / PrfH_lt_subst2 / PrfH_lt_subst1 / PrfH_eq_congr_nthc2   -- congruencias de lt/nthc
theorem prf_boundedIn_head (x hd t) : Prf ((x =eq hd) ⇒ boundedIn x (cons hd t))   -- testigo i = 0
theorem prf_boundedIn_tail (x hd t) : Prf (boundedIn x t ⇒ boundedIn x (cons hd t)) -- testigo i = σj
theorem prf_boundedIn_nil  (x)      : Prf (boundedIn x nil ⇒ ⊥)
theorem prf_boundedIn_cons (x hd t) : Prf (boundedIn x (cons hd t) ⇒ lor (x =eq hd) (boundedIn x t))
theorem prf_pred_succ (n) : Prf (pred (succ n) =eq n)  ;  prf_eq_congr_pred / PrfH_eq_congr_pred
theorem prf_zero_or_eq_succ_pred (n) : Prf (lor (n =eq zero) (n =eq succ (pred n)))
theorem prf_boundedIn_of_In / prf_In_of_boundedIn
theorem prf_In_iff_boundedIn (x L) : Prf (In x L ⇔ boundedIn x L)     -- ← objetivo de la fase 1b
-- #print axioms = [propext, Classical.choice, Quot.sound]
```

**TRUCOS clave (reusar):** (1) los `∃`‑elim van en **lemas `Prf` autónomos** (`prf_ex_elim_imp`) y se
aplican con `PrfH.mp` dentro de la inducción. (2) Para partir por casos un índice dentro de un
contexto `PrfH` **sin `∃`**, usar el **predecesor** (`prf_zero_or_eq_succ_pred`): el testigo del caso
`i = σ(pred i)` es directamente `pred i`.

---

**`Meta/RunFnBoundedPrf.lean`** (fase 2, lado `In`) — namespace `…Meta.RunFnBoundedPrf`.

**Hallazgo que abarató la fase 2 (§13 del diseño): NO hace falta β‑función.** `runFn nil p` **no es
una recursión con acumulador: es el *map* de `carc` sobre `p`**. La cadena
`prf_runFn_cons` → `prf_concat_nil_eq` → **`prf_runFn_weaken`** (saca el acumulador fuera) →
`prf_concat_cons_eq` lo demuestra. En consecuencia el acumulador **nunca hay que construirlo**, y la
pertenencia a las conclusiones queda acotada por `lenc p` directamente.

```lean
theorem prf_eq_congr_lenc / PrfH_eq_congr_lenc / PrfH_eq_congr_carc / PrfH_eq_congr_nthc1
theorem prf_runFn_nil_cons (line rest) :                     -- ← lema decisivo (§13)
  Prf (runFn nil (cons line rest) =eq cons (carc line) (runFn nil rest))
theorem prf_lenc_runFn (p) : Prf (lenc (runFn nil p) =eq lenc p)
def nthRunPred : Formula                                     -- Ψ(p) = ∀i. (i < lenc p ⇒ …)  (∀i INTERNO)
theorem nthRunPred_base / nthRunPred_step                    -- step: Prf.qconf + PrfH_spec + pred
theorem prf_nthc_runFn (p i) : Prf (lt i (lenc p) ⇒ (nthc (runFn nil p) i =eq carc (nthc p i)))
def boundedCarcIn (y p : Term) : Formula := ∃ k < lenc p. carc (nthc p k) =eq y
theorem liftFormula_boundedCarcIn
theorem prf_In_runFn_of_boundedCarcIn / prf_boundedCarcIn_of_In_runFn
theorem prf_In_runFn_iff (y p) : Prf (In y (runFn nil p) ⇔ boundedCarcIn y p)   -- ← PAYOFF, cota `lenc p`
-- #print axioms = [propext, Classical.choice, Quot.sound]
```

---

**`Meta/ChainOkBoundedPrf.lean`** (fase 2, lado `chainOk`) — namespace `…Meta.ChainOkBoundedPrf`:
**el acumulador desaparece**.

```lean
-- (b) absorción de una conclusión en el acumulador
theorem prf_in_concat_iff (x L M) : Prf (In x (concat L M) ⇔ lor (In x L) (In x M))   -- cierre de ax_L3
theorem prf_in_cons_nil_iff (y x) : Prf (In y (cons x nil) ⇔ (y =eq x))
theorem prf_in_concat_singleton_iff (y c x) : Prf (In y (concat c [x]) ⇔ lor (In y c) (y =eq x))

-- (0) cota ARBITRARIA (en `chainOk` la cota es el índice de la línea, no `lenc p`)
def boundedCarcLt (y p b : Term) : Formula := ∃ k < b. carc (nthc p k) =eq y
theorem boundedCarcIn_eq_boundedCarcLt (y p) : boundedCarcIn y p = boundedCarcLt y p (lenc p)   -- rfl
theorem liftFormula_boundedCarcLt / liftFormula_boundedCarcLt_gen / substFormula_boundedCarcLt
theorem prf_boundedCarcLt_zero (y p) : Prf (boundedCarcLt y p zero ⇒ ⊥)

-- (c) split del ∃k<σj sobre `cons`
theorem prf_boundedCarcLt_cons_of_head (y line rest j) : Prf ((carc line =eq y) ⇒ boundedCarcLt y (cons line rest) (succ j))
theorem prf_boundedCarcLt_cons_of_tail (y line rest j) : Prf (boundedCarcLt y rest j ⇒ boundedCarcLt y (cons line rest) (succ j))
theorem prf_boundedCarcLt_cons_succ_iff (y line rest j) :
  Prf (boundedCarcLt y (cons line rest) (succ j) ⇔ lor (carc line =eq y) (boundedCarcLt y rest j))

-- (a) forma acotada de `allIn`
def boundedAllIn (c L : Term) : Formula := ∀ j < lenc L. In (nthc L j) c
theorem PrfH_eq_subst_in1 {Γ x₁ x₂ L} (h : PrfH Γ (x₁ =eq x₂)) (hin : PrfH Γ (In x₁ L)) : PrfH Γ (In x₂ L)
  -- congruencia de `In` en el ELEMENTO (la previa `PrfH_eq_subst_in` sustituye la LISTA)
theorem liftFormula_boundedAllIn_gen / substFormula_boundedAllIn / liftFormula_allIn / substFormula_allIn
theorem prf_boundedAllIn_nil / _cons_head / _cons_tail / _cons     -- todo el ∀j confinado aquí (Prf.qconf)
theorem prf_boundedAllIn_of_allIn / prf_allIn_of_boundedAllIn      -- las dos inducciones de lista
theorem prf_allIn_iff_boundedAllIn (c L) : Prf (allIn c L ⇔ boundedAllIn c L)      -- ← (a)

-- (d) el teorema de la fase 2
theorem prf_premOk_cons_iff (y c line rest i) :                    -- ← LEMA PUNTUAL: fusiona (b) y (c)
  Prf (lor (In y c) (boundedCarcLt y (cons line rest) (succ i))
    ⇔ lor (In y (concat c [carc line])) (boundedCarcLt y rest i))
def boundedPremsIn (c p i L : Term) : Formula   -- ∀ j < lenc L. (In (nthc L j) c ∨ ∃ k < i. carc (nthc p k) =eq nthc L j)
def lineOkB (c p i : Term) : Formula := land (lineWF (nthc p i)) (boundedPremsIn c p i (premsOf (nthc p i)))
def chainOkB (c p : Term) : Formula := ∀ i < lenc p. lineOkB c p i
def lineOkBAt (c p i X : Term) : Formula     -- línea DESACOPLADA del índice (para Leibniz)
theorem lineOkB_eq_at (c p i) : lineOkB c p i = lineOkBAt c p i (nthc p i)   -- rfl
theorem PrfH_congr_lineOkBAt / PrfH_congr_lineOkB_i                          -- Leibniz en X / en i
theorem liftFormula_boundedPremsIn / substFormula_boundedPremsIn
theorem liftFormula_lineOkB / substFormula_lineOkB / liftFormula_chainOkB / substFormula_chainOkB
theorem prf_boundedPremsIn_zero_iff (c p L) : Prf (boundedPremsIn c p zero L ⇔ boundedAllIn c L)
theorem prf_lineOkB_zero_iff (c line rest) : Prf (lineOkB c (cons line rest) zero ⇔ lineOk c line)
theorem prf_boundedPremsIn_cons_succ_iff (c line rest i L) :
  Prf (boundedPremsIn c (cons line rest) (succ i) L ⇔ boundedPremsIn (concat c [carc line]) rest i L)
theorem prf_lineOkB_cons_succ_iff (c line rest i) :
  Prf (lineOkB c (cons line rest) (succ i) ⇔ lineOkB (concat c [carc line]) rest i)
theorem prf_chainOkB_nil (c) : Prf (chainOkB c nil)
theorem prf_chainOkB_cons_head / _cons_tail / _cons_intro
theorem prf_chainOkB_cons_iff (c line rest) :                       -- espejo exacto de ax_chainOk_cons
  Prf (chainOkB c (cons line rest) ⇔ land (lineOk c line) (chainOkB (concat c [carc line]) rest))
def chainBPred : Formula := ∀c. (chainOk c #1 ⇔ chainOkB c #1)      -- acumulador ∀c INTERNO
theorem prf_chainOk_iff_chainOkB (c p) : Prf (chainOk c p ⇔ chainOkB c p)   -- ← (d), FASE 2 COMPLETA
-- #print axioms de todos = [propext, Classical.choice, Quot.sound]
```

Desplegando las definiciones, (d) dice exactamente:

```text
chainOk c p  ⇔  ∀ i < lenc p.  lineWF (nthc p i)
                             ∧ ∀ j < lenc (premsOf (nthc p i)).
                                 ( In (nthc (premsOf (nthc p i)) j) c
                                 ∨ ∃ k < i. carc (nthc p k) =eq nthc (premsOf (nthc p i)) j )
```

— la formulación Δ₀ de libro: *cada premisa está en el contexto inicial o es la conclusión de una
línea anterior*. La demostración generaliza el acumulador como `∀c` **interno** e instancia la HI en
`c ++ [carc line]`; el paso `cons` se apoya en el lema puntual `prf_premOk_cons_iff`.

**Lecciones De Bruijn acumuladas (§14.4 del diseño, REUSAR):**

- `∃`‑elim de una **hipótesis** → lema `Prf` autónomo con `prf_ex_elim_imp` (nunca `PrfH_ex_elim`).
- `∀`‑intro como **consecuente** → `Prf.qconf` (nunca `PrfH.gen`); `∀`‑elim de hipótesis → `PrfH_spec`.
- Case‑split de un índice bajo `PrfH` sin `∃` → `prf_zero_or_eq_succ_pred` (testigo `pred i`).
- Empujar `lift`/`subst` a través de un predicado con `∃`/`∀` interno **necesita lema propio**
  (no es defeq; los iguala `FOL.liftTerm_comm_zero` / `FOL.substTerm_lift_comm_zero`).
- En un `have`, `PrfH _ (…)` no infiere `Γ` → nombrar el contexto con `let`.
- `liftFormula 0 (lor A B)` **no se destapa con `rw`** → introducir un `have hlor : … := rfl` explícito
  antes de reescribir el lema de lift del predicado.
- `prfH_weaken` **no** es debilitamiento de contexto (es `Γ ⊢ B → Γ ⊢ A ⇒ B`); para usar una HI en un
  contexto extendido, re‑derivarla con `PrfH_spec` sobre la hipótesis en posición `tail`.

---

### 3.19 Fase 3 — D3 reducida a la forma acotada + reflexión atómica rastreada

Con la fase 2 completa (§3.18), la Σ₁‑completitud provable (`hI`/`hC` de `d3_prf_of_sigma1`) se
ataca sobre la forma **Δ₀ acotada** y por reflexión de sus **átomos**.

**`Meta/Sigma1BoundedPrf.lean`** (fase 3, puente) — namespace `…Meta.Sigma1BoundedPrf`. Como la
fase 1/2 dio los `⇔` y `pcc_imp` sube implicaciones object a `provCodeC'` (D2+D1), `hI`/`hC` se
reducen a reflejar la forma acotada `boundedIn`/`chainOkB`.

```lean
prf_hI_of_reflect_boundedIn (hbI : ∀ x L, Prf (boundedIn x L ⇒ provCodeC' (boundedIn x L)))
  : ∀ x L, Prf (In x L ⇒ provCodeC' (In x L))
prf_hC_of_reflect_chainOkB (hbC : ∀ p, Prf (chainOkB nil p ⇒ provCodeC' (chainOkB nil p)))
  : ∀ p, Prf (chainOk nil p ⇒ provCodeC' (chainOk nil p))
d3_prf_of_reflect_bounded (φ) (hbC) (hbI) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ))  -- = d3_prf
-- #print axioms = [propext, Classical.choice, Quot.sound, prf_inAxC]
```

**`Meta/Sigma1AtomPrf.lean`** (fase 3, núcleo) — namespace `…Meta.Sigma1AtomPrf`. Toolkit
**rastreado** del átomo de igualdad `t =eq u` (átomo base de `boundedIn`: `nthc L i =eq x`), espejo
exacto del toolkit de `In` (`prf_provCodeC'_In_of_tracked`, §3.17).

**Por qué rastreado (Tarski):** reflejar `t =eq u` para `t`, `u` **abstractos** es imposible libre
de muro — `provCodeC'(t=eq u)` contiene `termCode t` (meta, sin congruencia object) y `termCode t
=eq termCode u` no se sigue de `t=eq u`. Se codifican los argumentos con `tcFn` (que SÍ tiene
congruencia Leibniz object, `prf_congr_tcFn`); el puente `tcFn t =eq termCode t` lo descarga la
inducción de fase 5 cuando `t` es numeral (`prf_tc_numeral`).

```lean
def eqCodeFn (a b : Term) : Term := cons (numeral 4) (cons a (cons b nil))   -- ⟨4, a, b⟩
theorem eqCodeFn_termCode (t u) : eqCodeFn (termCode t) (termCode u) = formCode (Formula.eq t u)  -- rfl
theorem provCodeC'_eq_eq (t u) : provCodeC' (Formula.eq t u) = provFromCode (eqCodeFn (termCode t) (termCode u))  -- rfl
theorem prf_congr_eqCodeFn (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) : Prf (eqCodeFn a b =eq eqCodeFn a' b')
theorem prf_provFromCode_eq_congr (ha) (hb) : Prf (provFromCode (eqCodeFn a b) ⇒ provFromCode (eqCodeFn a' b'))
theorem liftTerm_eqCodeFn / liftFormula_provFromCode_eq   -- clausuras De Bruijn (args cerrados)
theorem prf_provCodeC'_eq_of_tracked {t u tc uc}
  (ht : Prf (tc =eq termCode t)) (hu : Prf (uc =eq termCode u)) (h : Prf (provFromCode (eqCodeFn tc uc)))
  : Prf (provCodeC' (Formula.eq t u))                     -- reflexión rastreada (espejo de In)
theorem prf_provFromCode_eqCodeFn_refl_of_tracked {t tc} (ht : Prf (tc =eq termCode t))
  : Prf (provFromCode (eqCodeFn tc tc))                   -- reflexividad rastreada (superada, ver abajo)
```

**Reflexividad LIBRE DE MURO** (§15.4 del diseño). El verificador comprueba `lineWF`
**estructuralmente**: `prf_lineWF_eqrefl (concl t) : lineWF ⟨concl, 12, t⟩ ⇔ (concl =eq eqc t t)`,
y `eqc a b` es **literalmente** `eqCodeFn a b` (`numeral 4 = σ⁴0`). Con `concl := eqCodeFn c c`,
`t := c`, la condición es **pura reflexividad** para `c` **arbitrario** — sin `termCode`. Testigo:
la cadena de **una sola línea** `[⟨eqCodeFn c c, 12, c⟩]`.

```lean
theorem eqCodeFn_eq_eqc (a b) : eqCodeFn a b = eqc a b   -- rfl
def eqreflLine (c) : Term := cons (eqCodeFn c c) (cons (numeralM 12) (cons c nil))
theorem prf_lineOk_eqrefl / prf_chainOk_eqrefl / prf_in_runFn_eqrefl
theorem prf_provFromCode_intro (d p) (h1 : Prf (chainOk nil p)) (h2 : Prf (In d (runFn nil p)))
  : Prf (provFromCode d)                                  -- introductor a nivel de código arbitrario
theorem prf_provFromCode_eqCodeFn_refl (c) : Prf (provFromCode (eqCodeFn c c))   -- ← LIBRE DE MURO
theorem PrfH_congr_tcFn / PrfH_congr_eqCodeFn
theorem pcc_eq_tracked (t u) : Prf ((t =eq u) ⇒ provFromCode (eqCodeFn (tcFn t) (tcFn u)))  -- LIBRE DE MURO
theorem pcc_eq_of_tc_bridge (t u) (ht : Prf (tcFn t =eq termCode t)) (hu)
  : Prf ((t =eq u) ⇒ provCodeC' (Formula.eq t u))          -- muro confinado al puente (numerales, fase 5)
-- #print axioms de los tres = [propext, Classical.choice, Quot.sound]  (¡ni siquiera prf_inAxC!)
```

Al no pasar ya por `repr_pos'`, **desaparece incluso la dependencia de `prf_inAxC`**. El **muro de
Tarski queda confinado al último paso**: el puente `tcFn t =eq termCode t`, descargable con
**numerales** (`prf_tc_numeral`) en la inducción de fase 5 — exactamente como predice
Hilbert‑Bernays.

**Estado de fase 3‑5** (plan en `GODEL-D3-TRACKED-DESIGN.md` §15.5): ✅ puente + átomo `=eq` cerrado
libre de muro; ⏳ átomos `<`/`lineWF` (`atom1CodeFn`; `<` se reduce a `=eq` + `∃` acotado), reflexión
de cuantificadores acotados (∀/∃), e inducción estructural sobre `boundedIn`/`chainOkB` → `hbI`/`hbC`
→ `d3_prf` → `goedel_second_prf`.

---

### 3.20 Fase 3 (continuación) — sistema de prueba interno, evaluación provable y **ruta B dotada**

Tras el arranque de fase 3 (§3.19), la Σ₁‑completitud provable se ataca construyendo un **sistema de
prueba interno a nivel de código** y la **evaluación provable** de las funciones del verificador,
reformulando el target sobre la **notación‑punto de Feferman** (`num = tcFn`, "ruta B") — la
formulación canónica para fórmulas con variables libres. Plan en `GODEL-D3-TRACKED-DESIGN.md`
§19–§38. **Estado 2026‑07‑12 (HEAD `05fe7c3`, 91 jobs, 0 sorrys).**

#### 3.20.1 Sistema de prueba interno a nivel de código (§19, §25, §26)

`Meta/ExIntroCodePrf`, `Meta/ForallElimCodePrf`, `Meta/MpCodePrf`. Las cuatro reglas del cálculo,
todas con **testigo/código abierto** (los artefactos de clausura `hw`/`hAc`/`hBc` eran innecesarios;
se arrastran los lifts vía `liftFormula_provFromCode_open`).

```lean
theorem pcc_exIntro_code' (Ac w) (hAc : ∀ c, liftTerm c Ac = Ac) : Prf (provFromCode (substfc zero w Ac) ⇒ provFromCode (exc Ac))
theorem pcc_exIntro_code_open (Ac w) : Prf (provFromCode (substfc zero w Ac) ⇒ provFromCode (exc Ac))   -- SIN clausura (keystone §31)
theorem pcc_forallElim_code_open (Ac w) : Prf (provFromCode (forallc Ac) ⇒ provFromCode (substfc zero w Ac))
theorem pcc_mp_code_open (Ac Bc) : Prf (provFromCode (implc Ac Bc) ⇒ provFromCode Ac ⇒ provFromCode Bc)
theorem pcc_thm_inst  (φ) (h : Prf (Formula.forall φ)) (w) : Prf (provFromCode (substfc zero w (formCode φ)))
theorem pcc_thm_inst2 (φ) (h : Prf (forall_2 φ)) (w₁ w₂)   -- + pcc_thm_inst3, corolarios pcc_axiom_inst/inst2/inst3
theorem pcc_leibniz_code (Ac t₁ t₂) : Prf (provFromCode (eqc t₁ t₂) ⇒ provFromCode (substfc zero t₁ Ac) ⇒ provFromCode (substfc zero t₂ Ac))
```

Con `pcc_leibniz_code` + `pcc_mp_code_open` sale la **lógica ecuacional interna** (`pcc_leibniz_apply`,
`pcc_eq_trans_code`, `pcc_congr_succ_code`), con la restricción de que el código fijo sea
`substtc`‑invariante (`substtc_inv_tcFn`, `substtc_inv_succcT`, `substtc_inv_addcT`).

#### 3.20.2 Sustitución de código con testigo abierto (§20) y código de numeral cerrado (§23)

`Meta/SubstCodeOpenPrf`, `Meta/NumCodeClosedPrf`.

```lean
def substCodeT (v w) : Term → Term       -- función meta: sustitución-de-código sobre términos
def substCodeF (v w) : Formula → Term     -- ídem sobre fórmulas (bajo binder el testigo se lifta: liftc zero w)
theorem prf_substfc_arith_open (v w f) : Prf (substfc (numeral v) w (formCode f) =eq substCodeF v w f)   -- testigo-código ARBITRARIO
theorem substCodeT_termCode (v s) : ∀ t, substCodeT v (termCode s) t = termCode (substTerm v s t)
theorem substCodeT_closed (v w) : ∀ t, (∀ c, liftTerm c t = t) → substCodeT v w t = termCode t   -- NUEVO (§38): substCodeT de término cerrado = termCode
theorem prf_liftc_tcFn (a)    : Prf (liftc zero (tcFn a) =eq tcFn a)      -- «el código de un numeral es cerrado» (1ª inducción interna)
theorem prf_substtc_tcFn (W a) : Prf (substtc zero W (tcFn a) =eq tcFn a)
```

#### 3.20.3 Evaluación provable (§21, §24, §27, §28, §35, §37)

`Meta/EvalArithPrf`, `Meta/EvalListPrf`, `Meta/EvalLtPrf`, `Meta/EvalBoundedPrf`, `Meta/EvalRunFnPrf`,
`Meta/EvalNthcPrf`, `Meta/EvalCarcNthcPrf`. Asimetría clave: el lado izquierdo del código es el
**término simbólico**; el derecho, el **numeral del valor**; coinciden porque la teoría prueba la
ecuación y `tcFn` tiene congruencia.

```lean
theorem pcc_eval_add (a b) : Prf (provFromCode (eqCodeFn (addcT (tcFn a) (tcFn b)) (tcFn (add a b))))   -- ⌜ȧ+ḃ = (a+b)˙⌝
theorem pcc_eval_carc / pcc_eval_cdrc / pcc_eval_lenc                                                     -- listas (§28)
def bdExCode (B Phic) : Term := exc (andc (ltCodeFn (varc (numeral 0)) B) Phic)                           -- código de ∃i<B. φ(i)
theorem pcc_bdEx_intro (B Phic K) (hBcl hBinv hPcl hlt hphi) : Prf (provFromCode (bdExCode B Phic))       -- ∃i<B-intro (cerrado)
theorem pcc_bdAll_elim (B Phic K) (hBinv hall hlt) : Prf (provFromCode (substfc zero K Phic))             -- ∀i<B-elim
theorem pcc_eval_nthc (p i) : Prf (lt i (lenc p) ⇒ provFromCode (evalNthcCode p i))                       -- nthc(ṗ,ı̇)=(nthc p i)˙ (inducción acotada, §35)
theorem pcc_eval_carc_nthc (p i) : Prf (chainOk nil p ⇒ lt i (lenc p) ⇒                                   -- carc(nthc(ṗ,ı̇))=(carc(nthc p i))˙ (§37)
  provFromCode (eqCodeFn (carcT (nthcT (tcFn p) (tcFn i))) (tcFn (carc (nthc p i)))))
```

#### 3.20.4 Reflexión Δ₀ atómica y composicional (§29–§32)

`Meta/Delta0ReflectPrf`, `Meta/Sigma1AtomPrf`. Reflexiones `⊢ (átomo) ⇒ provFromCode (código tracked)`
para términos arbitrarios, más los casos composicionales.

```lean
theorem pcc_eq_tracked (t u) : Prf ((t =eq u) ⇒ provFromCode (eqCodeFn (tcFn t) (tcFn u)))     -- átomo = (libre de muro)
theorem pcc_lt_tracked (s t) : Prf ((lt s t) ⇒ provFromCode (ltCodeFn (tcFn s) (tcFn t)))       -- átomo < (∃-elim + pcc_lt_intro_open)
theorem pcc_reflect_and / pcc_reflect_or (φ ψ Ac Bc) (hφ hψ)                                     -- composicional ∧/∨ (agnóstico del código)
theorem pcc_gen_code (Ac) (h : ∀ w, Prf (provFromCode (substfc zero w Ac))) : Prf (provFromCode (forallc Ac))
```

#### 3.20.5 Ruta B dotada — D3 reducida a las reflexiones **punteadas** (§33–§38)

`Meta/D3DottedPrf`, `Meta/LineWFConsPrf`, `Meta/D3InDotPrf`. **Keystone:** `formCode (provCodeC' φ) =
exc (formCode (bodyF φ))` con `bodyF φ = chainOk nil #0 ∧ In ⌜φ⌝ (runFn nil #0)`; el `∃`‑intro dotado
(`pcc_exIntro_code_open`, testigo `tcFn #0`) lleva la reflexión punteada del cuerpo al target de D3.

```lean
def bodyF (φ) : Formula := land (chainOk nil #0) (In (formCode φ) (runFn nil #0))
abbrev inDot (φ) : Term := substfc zero (tcFn #0) (formCode (In (formCode φ) (runFn nil #0)))    -- código punteado del átomo In
theorem d3_prf_of_dotted_atoms (φ) (hC : Prf (chainOk nil #0 ⇒ provFromCode chainOkDot))
  (hI : Prf (In (formCode φ) (runFn nil #0) ⇒ provFromCode (inDot φ))) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ))  -- = d3_prf
theorem prf_line_is_cons (p i) : Prf (chainOk nil p ⇒ lt i (lenc p) ⇒                            -- vía ax_lineWF_cons (sancionado)
  (nthc p i =eq cons (carc (nthc p i)) (cdrc (nthc p i))))
```

**`hI_dot` — COMPLETO ✅** (`Meta/D3InDotPrf`). El átomo `In` está cerrado, y con él **D3 queda
reducida a UN SOLO lema**: la reflexión punteada de `chainOk`.

```lean
theorem pcc_bdEx_intro_open (B Phic K) (hBinv) (hlt) (hphi) : Prf (provFromCode (bdExCode B Phic))   -- ∃i<B-intro SIN clausura (p libre dotado)
theorem PrfH_eq_symm_code (X Y) (hX) (heq) : PrfH Γ (provFromCode (eqc Y X))                          -- SIMETRÍA interna (nueva; la exige la cota)
theorem PrfH_bdEx_intro_open (B Phic K) (hBinv) (hlt) (hphi) : PrfH Γ (provFromCode (bdExCode B Phic))
theorem pcc_bddDot_imp_inDot_at (φ p) : Prf (provFromCode (implc (bddCarcDotAt φ p) (inDotAt φ p)))   -- Step A (testigo arbitrario)
theorem prf_bddCarcDot_eq_at (φ p) : Prf (bddCarcDotAt φ p =eq bdExCode (bdCarcBAt p) (bdCarcPhicAt φ p))
theorem pcc_bddCarcDot_reflect (φ p) :                                                                 -- ★ NÚCLEO de Step B
  Prf (chainOk nil p ⇒ boundedCarcIn (formCode φ) p ⇒ provFromCode (bddCarcDotAt φ p))
theorem hI_dot (φ) : Prf (chainOk nil #0 ⇒ In ⌜φ⌝ (runFn nil #0) ⇒ provFromCode (inDot φ))
theorem d3_prf_of_chainOkDot (φ) (hC : Prf (chainOk nil #0 ⇒ provFromCode chainOkDot)) :
  Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ))                                                       -- ★ D3 ⇐ hC_dot SOLO
```

**Tres hallazgos del núcleo** (patrón `pcc_lt_tracked` con la implicación objeto codificada):

1. El **`PrfH_ex_elim` liftea `p`** (`#0`→`#1`) ⇒ los lemas fijados en `#0` no aplican después: hubo que
   **generalizar todo lo dotado sobre `p` arbitrario**. Clave: el `formCode` codifica siempre el
   **esquema** (con `#0` en el hueco de `p`); lo único que varía es el testigo `tcFn p`, así que la
   computación de `substCodeF` no cambia. Con `liftFormula_provFromCode_open` + `liftTerm_bddCarcDotAt`
   la meta lifteada es *la misma con `↑p`*.
2. La **COTA exigió SIMETRÍA INTERNA** (que no existía): `pcc_lt_tracked` da la cota con `tcFn (lenc ↑p)`,
   pero el código dotado pide `lencT (liftc 0 ↑ṗ)` — y **sólo son iguales DENTRO de `Prov`** (es la
   evaluación provable `pcc_eval_lenc`), en la dirección contraria a la que transporta Leibniz. De ahí
   `PrfH_eq_symm_code` + `prf_substfc_ltCodeFn_snd` (hueco `⌜v₀⌝` en 2ª posición).
3. El **CUERPO NO necesita simetría**: la hipótesis del `∃` es una igualdad **objeto**, así que basta
   congruencia objeto (`PrfH_congr_tcFn` + `prf_tc_form` + `prf_liftc_tcFn`) + `PrfH_provCode_congr`
   sobre `pcc_eval_carc_nthc` — que consume `chainOk`, y por eso `hI` debe recibirlo (`hbody_of_atoms`
   reestructurado).

#### 3.20.6 LÓGICA PROPOSICIONAL e INDUCCIÓN **internas** a nivel de código (§39)

`Meta/PropCodePrf.lean`. **Hallazgo:** las líneas‑axioma proposicionales del verificador **y la de
INDUCCIÓN** son TODAS **estructurales** (bicondicional `lineWF` con códigos **arbitrarios** y
`premsOf = nil`, igual que EQREFL/Q1/Q2/LEIBNIZ, §3.20.1) ⇒ cada una se demuestra con un testigo de
**una sola línea** (`pcc_axline`) y sale **libre de muro** (`[propext, choice, Quot.sound]`).

| tag | línea | esquema |
|:---:|:------|:--------|
| 0 | `p1` | `A ⇒ (B ⇒ A)` (K) |
| 1 | `p2` | `(A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))` (S) |
| 7 | `j3` | `(A ∨ B) ⇒ ((A ⇒ C) ⇒ ((B ⇒ C) ⇒ C))` — **`∨`‑elim** |
| 8 | `efq` | `⊥ ⇒ A` |
| 18 | `ind` | `A[0] ⇒ (∀x. A[x] ⇒ A[σx]) ⇒ ∀x. A[x]` — **inducción** |

```lean
theorem pcc_p1_code (Ac Bc) : Prf (provFromCode (implc Ac (implc Bc Ac)))
theorem pcc_p2_code (Ac Bc Cc) : Prf (provFromCode (implc (implc Ac (implc Bc Cc)) (implc (implc Ac Bc) (implc Ac Cc))))
theorem pcc_j3_code (Ac Bc Cc) : Prf (provFromCode (implc (orc Ac Bc) (implc (implc Ac Cc) (implc (implc Bc Cc) Cc))))
theorem pcc_efq_code (Ac) : Prf (provFromCode (implc botc Ac))
noncomputable def indConcl (Ac) : Term                      -- A[0] ⇒ (∀x. A[x] ⇒ A[σx]) ⇒ ∀x. A[x]
theorem pcc_ind_code (Ac) : Prf (provFromCode (indConcl Ac))   -- ★ INDUCCIÓN interna, código arbitrario
-- derivadas del cálculo implicacional (P1 + P2 + MP):
theorem pcc_weaken_code (Ac Bc) (h : Prov(⌜Bc⌝)) : Prf (provFromCode (implc Ac Bc))
theorem pcc_imp_trans_code (Ac Bc Cc) (h1 h2) : Prf (provFromCode (implc Ac Cc))   -- silogismo hipotético
theorem pcc_or_elim_imp_code (Ac Bc Cc) (h1 h2) : Prf (provFromCode (implc (orc Ac Bc) Cc))
theorem pcc_or_elim_code (Ac Bc Cc) (hor h1 h2) : Prf (provFromCode Cc)
```

**Consecuencia:** junto con lo ya existente (MP, `∀`‑elim, `∃`‑intro, gen, Leibniz, `∧`, `∨`‑intro),
**`Prov` dispone YA de lógica completa**. `pcc_ind_code` es el desbloqueo de `hC_dot`.

#### 3.20.7 INTRODUCCIÓN del `∀` acotado (§40) — keystone de `hC_dot`

`Meta/BdAllIntroPrf.lean`. La pieza que §3.20.3 dejó pendiente (`pcc_bdAll_elim` existía; la **intro**
NO) y que `hC_dot` necesita.

```lean
theorem pcc_bdAll_base (Psi) : Prf (provFromCode (implc (ltCodeFn ⌜v₀⌝ (tcFn zero)) Psi))   -- vacuo (EFQ)
def splitSchema : Formula                                                                    -- #0 = i, #1 = b
theorem pcc_lt_succ_split_code (b) :                                                         -- split codificado (VOLTEADO)
  Prf (provFromCode (implc (ltCodeFn ⌜v₀⌝ (tcFn (succ b))) (orc (ltCodeFn ⌜v₀⌝ (tcFn b)) (eqCodeFn (tcFn b) ⌜v₀⌝))))
theorem pcc_bdAll_step  (Psi b) (hPsiId) (hIH) (hb) : …
theorem PrfH_bdAll_step (Psi b) (hPsiId) (hIH) (hb) : …          -- el paso vive bajo contexto
noncomputable def bdAllPred (CF bndF PsiF p) : Formula            -- predicado de la inducción (b = #0, p lifteado)
theorem pcc_bdAll_intro (CF bndF PsiF p) (…conmutaciones lift/subst…) (hPsiId) (hbody) :
  Prf (CF p ⇒ provFromCode (bdAllCode (tcFn (bndF p)) (PsiF p)))  -- ★ LA INTRO
-- auxiliares
theorem prf_lt_succ_of_lt (m n) : Prf (lt m n ⇒ lt m (succ n))
theorem prf_lt_succ_self (n)    : Prf (lt n (succ n))
theorem prf_lt_succ_split' (i b) : Prf (lt i (succ b) ⇒ lor (lt i b) (Formula.eq b i))   -- VOLTEADO: `b = i`
theorem pcc_eq_symm_code_internal (X Y) (hX) : Prf (provFromCode (implc (eqc X Y) (eqc Y X)))
theorem prf_congr_orc / prf_congr_substfc3 / PrfH_congr_substfc3
theorem PrfH_weaken_code / PrfH_imp_trans_code / PrfH_or_elim_imp_code
```

**Las cinco decisiones/obstrucciones que costaron:**

1. **NO se induce sobre el testigo** (`Ac[x] ⇒ Ac[σx]` es **FALSO**: `φ(σx)` no se sigue de `φ(x)`),
   sino sobre la **COTA**, a nivel **objeto**, con guarda `b < σbnd`: la guarda da `b < bnd` y de ahí
   `hbody` entrega el `Prov(⌜φ(ḃ)⌝)` que el paso necesita.
2. La **disyunción finita de casos** (Hájek‑Pudlák, `i=0̄ ∨ … ∨ i=(n−1)̄`) **NO sirve**: la cota
   `lenc p` con `p` **abstracto** **no es un numeral concreto** ⇒ hay que inducir de verdad.
3. `pcc_gen_code` toma el body **abierto** ⇒ se induce sobre el **CUERPO ABIERTO** y se aplica `gen`
   **una sola vez al final** (evita el *round‑trip* `∀`‑elim).
4. **Obstrucción `hPsiId`**: `substfc` **DECREMENTA** las variables superiores (`prf_substtc_var_gt`),
   luego `substfc 0 ⌜v₀⌝ Psi` **sólo es la identidad** si la única code‑var de `Psi` es `⌜v₀⌝`. Se pasa
   como hipótesis y se descarga estructuralmente. (Por lo mismo, el split se **voltea en el objeto**:
   la simetría interna exige el 1er arg `substtc`‑invariante, y `⌜v₀⌝` no lo es.)
5. **Obstrucción De Bruijn del ensamblaje**: el binder de la inducción **desplaza** las variables
   libres ⇒ dentro del `gen` hace falta `hbody` en **`↑p`**, no en `p`. Resuelto **parametrizando
   sobre `p`** (`CF`/`bndF`/`PsiF` como funciones + conmutación de `liftTerm`/`substTerm`) — mismo
   patrón que resolvió el `∃`‑elim de `hI_dot`.

#### 3.20.8 Lo que FALTA para cerrar D3

**Toda la maquinaria existe ya**; lo que queda es composición, pero es mucha.

```text
chainOkB c p  = ∀i<lenc p. lineOkB c p i                        ← ∀ acotado  ✅ pcc_bdAll_intro
lineOkB c p i = lineWF (nthc p i) ∧ boundedPremsIn c p i (premsOf (nthc p i))
boundedPremsIn c p i L = ∀j<lenc L. ( In (nthc L j) c  ∨  ∃k<i. carc (nthc p k) = nthc L j )
                          ↑ ∀ acotado ANIDADO    ↑ ∨       ↑ ∃ acotado
```

* **∀i** y **∀j (anidado)**: `pcc_bdAll_intro` ✅ (dos aplicaciones) · **∧**: `pcc_reflect_and` ✅ ·
  **∨**: `pcc_reflect_or` ✅ · **∃k**: `pcc_bdEx_intro_open` ✅ (de `hI_dot`).
* **`In x nil`** es **refutable** ⇒ el disyunto izquierdo sale por **ex falso** (barato).
* **átomo `carc (nthc p k) = nthc L j`**: `pcc_eq_tracked` + `pcc_eval_carc_nthc` + `pcc_eval_nthc` ✅.
* ⚠️ **átomo `lineWF` — SUBPROYECTO**: reflejarlo dotado exige recorrer los **21 casos de tag**
  (`prf_lineWF_inv` da la disyunción `tagDisj`; en cada caso hay que reflejar su **ecuación
  estructural** y aplicar el **bicondicional codificado** `ax_lineWF_<tag>` vía `pcc_thm_inst`).
* Faltan además las **evaluaciones de `premsOf`** (y `lenc`/`nthc` sobre él) y los **cómputos
  `substCodeF`** de `chainOkB`/`lineOkB`/`boundedPremsIn` (patrón `substCodeT_closed`).

Luego `d3_prf := d3_prf_of_chainOkDot φ hC_dot` → `goedel_second_prf` → **F7b retira `axiom d3` (7→6)**.
Detalle vivo en `NEXT-STEPS.md` y memoria `project-d3-evaluacion-provable`.

---

### 3.21 `⊬¬G` — Gödel I COMPLETO (§41) y `axiomsCodeT` concretado (§42)

Paralelo a D3 (independiente de él): **la otra mitad de Gödel I**, la indecidibilidad de `G`.

#### 3.21.1 `Meta/OmegaReflect.lean` (§41) — `G` INDECIDIBLE, sin postulados gödelianos

La cadena real daba **sólo `⊬G`** (`goedel_first_real'`); la mitad `⊬¬G` vivía en la capa legacy
(sobre el postulado **falso** `provFormula_repr`) y se retiró en F7a. Se reconstruye **con la reflexión
como hipótesis META explícita** (no escondida en un postulado):

```lean
abbrev Reflects (G) : Prop := (axioms ⊢ provCodeC' G) → Prf G          -- representabilidad NEGATIVA
theorem goedel_first_unrefutable_real' (hcon) (hfp) (hrefl : Reflects G) : ¬ Prf (neg G)
theorem goedel_first_undecidable_real'  (hcon) (hrefl : Reflects godelC') : ¬ Prf godelC' ∧ ¬ Prf (neg godelC')
-- reducción de la hipótesis a piezas honestas:
def OmegaConsistent : Prop := …   -- ω-consistencia CLÁSICA (NO es ConsistentOmega); testigos ESTÁNDAR = objList de canónicos
def NegVerifier    : Prop := ∀ φ, ¬ Prf φ → ∀ l, StdChain l → axioms ⊢ neg (Verifies φ (objList l))
theorem reflects_of_omega (hω : OmegaConsistent) (hneg : NegVerifier) (φ) : Reflects φ
theorem goedel_first_undecidable_omega (hcon) (hω) (hneg) : ¬ Prf godelC' ∧ ¬ Prf (neg godelC')
```

`#print axioms goedel_first_undecidable_real'` = `[propext, choice, Quot.sound, MetaRules.{dne,gen,
imp_intro}, ax_induction, ax_list_induction, ax_axiomsCodeT_eq]` — **ni un postulado gödeliano**.

> ⛔ **`repr_neg` NO se sigue de la consistencia (cerrado por Gödel).** `⊢ ¬provCodeC' φ` para `φ`
> indemostrable es, con `φ = ⊥`, **`Con(T)`** — indemostrable por Gödel II. Por eso la reflexión es
> **hipótesis META** (la ω‑consistencia clásica), no un teorema interno. Descargarla (`NegVerifier`)
> es un enunciado **Δ₀** sobre testigos concretos — plan en `PLAN-NEGVERIFIER.md`.

#### 3.21.2 `Meta/AxiomListCode.lean` + anclaje (§42) — `axiomsCodeT` concretado

El sondeo de solidez (`PLAN-NEGVERIFIER.md` §🔬) halló que **`axiomsCodeT` era opaco** (sólo dirección
positiva `ax_inAxC`), lo que impedía refutar `In v0 axiomsCodeT` y **bloqueaba `NegVerifier`**. Opción
1: concretar el anclaje, **net‑0 axiomas de Lean**.

```lean
-- Minimal/Axioms.lean:  axiom ax_inAxC  →  axiom ax_axiomsCodeT_eq : axioms ⊢ (axiomsCodeT =eq listFormCodeM axioms)
theorem ax_inAxC (a) (h : a ∈ axioms) : axioms ⊢ In (formCodeM a) axiomsCodeT   -- AHORA teorema (del ancla)
theorem prf_In_listFormCodeM (f) : ∀ L, List.Mem f L → axioms ⊢ In (formCodeM f) (listFormCodeM L)  -- positivo, no materializa
-- Meta/AxiomListCode.lean:
theorem prf_not_In_listFormCodeM (φ) : ∀ L, ¬ List.Mem φ L → axioms ⊢ neg (In (formCode φ) (listFormCodeM L))
theorem neg_In_axiomsCodeT (φ) (hnp : ¬ Prf φ) : axioms ⊢ neg (In (formCode φ) axiomsCodeT)   -- ★ espejo NEGATIVO de ax_inAxC
```

**Clave de rendimiento:** el término gigante `listFormCodeM axioms` (que costaba ~40 s materializado y
motivó retirar el `axiomsCodeT` concreto en `7ae7b7b`) **no se expande** — la pertenencia se decide por
**recursión estructural sobre la lista abstracta** (`ax_L1`/`ax_L2` + `formCode_ne`); y `φ ∉ axioms` se
obtiene de `¬Prf φ` vía `prf_ax`, **sin comparación sintáctica** (medido: 4 s). `neg_In_axiomsCodeT` es
la pieza que **desbloquea el módulo D de `NegVerifier`**.

### 3.22 `Meta/CodeDecode.lean` + `Meta/ChainDecode.lean` (§43) — el DECODIFICADOR (módulo A de `NegVerifier`)

Inversos **computables** de los codificadores de Gödel y de prueba. Es el puente **objeto → meta** que
`VerifierSound` (módulo E) necesita: de un testigo aceptado se recupera —de forma verificada— la
derivación real. Plan: `PLAN-NEGVERIFIER.md` §4.

#### 3.22.1 `Meta/CodeDecode.lean` (§43·A.1) — `decodeForm` es una BIYECCIÓN

Recursión estructural directa sobre `Term` (terminación inferida). Cada decodificador tiene su
**round‑trip** (`decode ∘ code = some`) y su **inyectividad** (`decode c = some v → c = code v`); juntas
dan la biyección.

```lean
def decodeNat   : Term → Option Nat            -- σⁿ0 ↦ n
def decodeChars : Term → Option (List Char)    -- guard (Char.ofNat code).toNat == code  ⟵ imprescindible
def decodeStr   : Term → Option String         -- (decodeChars ·).map String.ofList
mutual def decodeTerm : Term → Option Term  def decodeTerms : Term → Option (List Term) end
def decodeForm  : Term → Option Formula        -- los 9 tags (⊥ 2 · atom 3 · =eq 4 · ⇒ 5 · ∀ 6 · ∧ 7 · ∨ 8 · ∃ 9)

theorem decodeNat_numeralM (n)  : decodeNat  (numeralM n)  = some n
theorem decodeStr_strCodeM (s)  : decodeStr  (strCodeM s)  = some s
theorem decodeTerm_termCodeM(t) : decodeTerm (termCodeM t) = some t   -- mutuo con decodeTerms_termsCodeM
theorem decodeForm_formCodeM(φ) : decodeForm (formCodeM φ) = some φ
theorem decodeNat_inj  {t n} : decodeNat  t = some n → t = numeralM n
theorem decodeStr_inj  {c s} : decodeStr  c = some s → c = strCodeM s
theorem decodeTerm_inj {c t} : decodeTerm c = some t → c = termCodeM t   -- mutuo con decodeTerms_inj
theorem decodeForm_inj {c φ} : decodeForm c = some φ → c = formCodeM φ    -- ★ la «dirección crítica»
```

> **No hizo falta la hipótesis `IsCodeShaped c`** que el plan anticipaba: los decodificadores son
> estructuralmente rígidos ⟹ la inyectividad vale para **todo** `c : Term`.
>
> ⚠️ **Dos trampas reales** (ver [[feedback-lean-kernel-ite-string]]):
> 1. **Kernel + `DecidableEq String`.** `split`/`rw`/`simp only [decodeX]` **manuales** sobre `if s == sym`
>    fabrican un cast `congrFun'` que **el núcleo RECHAZA**. Se sortea con **inducción funcional**
>    (`fun_induction`; para las mutuas `decodeTerm.induct` con `motive_2` explícito) + `unfold … at h`.
> 2. **`Char.ofNat` CLAMPA** ⟹ `decodeChars` no es inyectiva sin el guard `(Char.ofNat code).toNat == code`
>    (el round‑trip lo cumple gratis por `Char.ofNat_toNat`).

#### 3.22.2 `Meta/ChainDecode.lean` (§43·A.2) — decodificador de CADENAS + solidez

Invierte `lineJustif`/`lineCode'`/`proofCode'` (`Representability2.lean`). El justif se **pela** a
`List Term` (`peelArgs`) para matchear `(tag : Nat, args)` — un `match` sobre las 21 formas anidadas de
`Term` reventaría el `whnf` (`String.decEq`).

```lean
def peelArgs   : Term → List Term                              -- cons a (cons b nil) ↦ [a, b]
def decodeRule : List Formula → Formula → Term → Option Rule   -- inverso de lineJustif (dada la conclusión)
def decodeLine : List Formula → Term → Option (Formula × Rule) -- ⟵ VERIFICA stepConcl acc r = some f
def decodeChain: Term → Option (List Rule)                     -- inverso de proofCode' (hila el acumulador)

-- Igualdad decidible y buscador de índices (Term/Formula sólo derivan BEq anidado; sin DecidableEq/LawfulBEq):
instance : DecidableEq Term      -- construido a mano (mutuo);  deriving instance DecidableEq for Formula
def findIdx (f) : List Formula → Option Nat                     -- buscador propio con `=` (no List.idxOf?/BEq)
theorem findIdx_sound / findIdx_isSome_of_getElem              -- corrección del buscador

theorem decodeRule_lineJustif_clean (acc f r) (hcl : cleanRule r) :   -- RETRACT de los 18 tags limpios
    decodeRule acc f (lineJustif acc r) = some r
theorem decodeRule_{thy,mp,gen}_section (acc f …) (hstep : stepConcl acc r = some f) :   -- SECCIÓN de los 3 lossy
    ∃ r', decodeRule acc f (lineJustif acc r) = some r'
        ∧ stepConcl acc r' = some f ∧ lineJustif acc r' = lineJustif acc r
```

**Ensamblado (la pieza que consume el módulo E):**

```lean
theorem decodeLine_sound        : decodeLine acc lineT = some (f,r) → stepConcl acc r = some f
theorem decodeChain_checkProof  : decodeChain t = some rs → ∃ L, checkProof rs = some L   -- ★ SOLIDEZ
theorem decodeChain_prf         : decodeChain t = some rs →
                                    (∀ L, checkProof rs = some L → φ ∈ L) → Prf φ         -- vía derivation_to_prf
```

> ⚠️ **HALLAZGO que corrige el plan.** `lineJustif` es **LOSSY** para `thy`/`mp`/`gen` (descarta los
> índices: `thy k ↦ cons 15̇ nil`; `mp`/`gen` guardan la premisa resuelta, no el índice). Por tanto el
> round‑trip `decodeChain (proofCode' rs) = some rs` (**retract**) es **FALSO**. Lo que el módulo E
> necesita **no** es el retract sintáctico `proofCode' rs = t` (que `peelArgs` no da para códigos con
> «cola basura»), sino la **SOLIDEZ**: una cadena que `decodeChain` acepta es una **derivación válida**,
> y de ahí `Prf` de cada conclusión vía `derivation_to_prf` (solidez meta ya existente). La pieza que lo
> hace cierto es que `decodeLine` **verifica** `stepConcl acc r = some f` (con `DecidableEq Formula`).

**Dependencias:** `CodeDecode` ⇐ `Minimal.Axioms`. `ChainDecode` ⇐ `CodeDecode` + `Representability2`
(`Rule`/`stepConcl`/`checkProof`/`Derivation`/`derivation_to_prf`, `lineJustif`/`proofCode'`) + los
puentes `formCodeM_eq`/`termCodeM_eq` (`Representability`). Todo `[propext, choice, Quot.sound]`.

### 3.23 `Meta/LineWFCases.lean` + `Meta/LineWFDerives.lean` (§44) — los 21 TAGS (módulo B de `NegVerifier`)

Módulo B del plan: la tabla **ejecutable** de los 21 esquemas de línea, indexada por la etiqueta `k`.
Es la pieza de **mayor apalancamiento** porque está **COMPARTIDA** por los dos frentes, en direcciones
opuestas: **D3/`hC_dot`** (positiva: `lineWF X ⇒ Prov ⌜lineWF Ẋ⌝`) y **`NegVerifier`/módulo C**
(negativa: `¬lineWF X ⇒ ⊢ ¬lineWF X`).

> 🔎 **La revisión previa evitó rehacer trabajo**: los 21 `prf_lineWF_<tag>`/`prf_premsOf_<tag>` **ya
> existían** (`Meta/ReprPrf.lean`), y `prf_lineWF_inv` (inversión a `tagDisj`, los 21 disyuntos)
> también (`Meta/Sigma1AtomPrf.lean`). Módulo B **no era** «construir los 21 esquemas» sino
> **uniformizarlos**: la tabla permite a sus consumidores un case‑split mecánico sobre `k` en vez de
> escribir 21 casos cada uno.

#### 3.23.1 `Meta/LineWFCases.lean` — la tabla y sus dos direcciones

```lean
def tagArity : Nat → Nat                               -- aridad del justif por tag
def tagConcl : Nat → List Term → Option Term           -- reconstrucción estructural (19 tags)
def tagPrems : Nat → Term → List Term → Option Term    -- premisas de contexto (los 21)
theorem prf_lineWF_tag  (h : tagConcl k args = some e) :
    Prf (lineWF (cons concl (cons (numeralM k) (objList args))) ⇔ (concl =eq e))
theorem prf_premsOf_tag (h : tagPrems k concl args = some L) :
    Prf (premsOf (cons concl (cons (numeralM k) (objList args))) =eq L)
-- dirección NEGATIVA (módulo C). En `⊢` además de en `Prf`: los inputs reales
-- (`formCode_ne`, `neg_In_axiomsCodeT`) son de nivel `⊢`.
theorem prf_imp_trans / derives_imp_trans                     -- silogismo hipotético (no existían)
theorem derives_lineWF_neg_of_tag (h : tagConcl k args = some e)
    (hne : axioms ⊢ neg (concl =eq e)) : axioms ⊢ neg (lineWF ⟨concl,k,args⟩)
theorem derives_lineWF_neg_thy_of_not_prf (φ) (hnp : ¬ Prf φ) :   -- ★ compone con `neg_In_axiomsCodeT`
    axioms ⊢ neg (lineWF (cons (formCode φ) (cons (numeralM 15) nil)))
```

> ⚠️ **Los 21 esquemas NO son uniformes — `tagConcl` cubre 19, no 21.**
> * **19 estructurales** (los 18 de esquema **y `gen`**): `lineWF ⟨concl,k,args⟩ ⇔ (concl =eq <expr>(args))`.
> * **`thy` (15)**: su RHS es `In concl axiomsCodeT` — una **pertenencia**, no una ecuación.
> * **`mp` (16)**: `lineWF` es **INCONDICIONAL**; queda ligado por `premsOf`.
>
> **Ojo al matiz**: NO es el mismo corte que en el módulo A, donde los «raros» eran `thy`/`mp`/`gen`
> (codificación *lossy*); aquí **`gen` sí es estructural**. `tagPrems` sí cubre los 21.
>
> ⚠️ **`mp` NO se puede refutar por `lineWF`** (su esquema es incondicional ⟹ `lineWF ⟨concl,16,a⟩` es
> SIEMPRE demostrable). Refutar una línea `mp` mala **tiene que ir por `premsOf`/`boundedPremsIn`**.
> Condiciona el árbol de casos del módulo C.

#### 3.23.2 `Meta/LineWFDerives.lean` — des-duplicación del nivel `⊢`

Los 42 enunciados (21 `lineWF_*` + 21 `premsOf_*`) vivían en `Meta/ProofChain.lean` **probados por
segunda vez desde los mismos axiomas** que sus gemelos `prf_*`. Aquí son lo que siempre fueron: el
transporte por **`prf_to_derives : Prf φ → axioms ⊢ φ`**. Enunciados **idénticos**; namespace
`ProofChain` conservado ⟹ los consumidores (`Representability2` = D1, `DerivCond` = D2) sólo cambian un
`import`. `ProofChain`: 870 → 540 líneas. `repr_pos'_prf`/`d2_prf` conservan sus axiomas exactos.

#### 3.23.3 Paso 3 — los esquemas a ACCESORES (`ax_lineWF_<tag>` **B.3b HECHO**) → `pcc_lineWF_tracked` (B.3c)

La reflexión punteada del átomo (lo que `hC_dot` espera) debe tratar `lineWF (nthc p i)` con `p`,`i`
**abstractos** (`pcc_bdAll_intro` introduce el `∀i` con el cuerpo **abierto**). Y con los axiomas en su
forma **explícita** original **la teoría no podía recuperar la forma de una línea abstracta**:

| Axioma | Da | Falta |
|:--|:--|:--|
| `ax_lineWF_inv` | el tag es uno de los 21 | — |
| `ax_lineWF_cons` | `line =eq cons (carc line) (cdrc line)` | sólo el cons de **primer nivel** |
| `ax_carc`/`ax_cdrc`/`ax_nthc_*` | computan **sólo sobre `cons` explícitos** | no reducen sobre `t` abstracto |
| los 21 `ax_lineWF_<tag>` | LHS con la **forma exacta** | inaplicables a `t` abstracto |

De `lineWF t` se obtiene `t = cons (carc t) (cdrc t)` y `carc (cdrc t) = k̇`, pero **no** que `cdrc t`
sea un `cons` ⟹ `ax_lineWF_<k>` no se puede instanciar en `t`. (La nota de `Sigma1AtomPrf.lean` que
dice que `prf_lineWF_inv` «desbloquea» la reflexión abstracta está **incompleta**: el tag es necesario
pero **no suficiente**; falta la forma.)

**Salida SANCIONADA (net‑0 axiomas):** reformular los 21 `ax_lineWF_<tag>` a **forma con ACCESORES**:

```lean
-- en vez de:  ∀concl a b. lineWF (cons concl (cons 0̇ (cons a (cons b nil)))) ⇔ (concl =eq implc a (implc b a))
-- pasa a:     ∀line. (lineTag line =eq 0̇) ⇒
--                (lineWF line ⇔ (carc line =eq implc (nthc line 2̇) (implc (nthc line 3̇) (nthc line 2̇))))
```

Los accesores **sortean la aridad** (están definidos para toda línea), que es justo lo que bloqueaba.
Es sólido por **realidad hereditaria** (§🔬 A del plan) y los 21 `prf_lineWF_<tag>` conservan su
enunciado, pasando a ser teoremas del nuevo axioma.

**B.3a HECHO** (`d536f19`): des-duplicación de §3.23.2 (reduce la reformulación de 42 re‑pruebas a 21 y
de 2 toolkits a 1). **B.3b HECHO** (`e33eef0`, `5bc0dbc`): **los 19 esquemas estructurales reformulados
a accesores** (`p1 p2 c1 c2 c3 j1 j2 j3 efq q1 q2 q3 eqrefl leibniz p3 ind qconf listInd gen`; `thy` va
por `In` y `mp` es incondicional ⟹ NO se reforman). Net‑0 axiomas; los 21 `prf_lineWF_<tag>` conservan
su enunciado (`[propext, choice, Quot.sound]`); D1/D2 con axiomas intactos. Generados mecánicamente.
Toolkit en `ReprPrf`: `prf_lineWF_iff_transport` (vale para los 21 — `lineWF L` es un **átomo sin
binders** ⟹ el cancel lift/subst va por `substTerm_liftTerm`; ⚠️ **el cancel general a nivel fórmula es
FALSO**, `FOL/Theorems/Quantifiers.lean`), `prf_congr_bin1/bin2/un/bin` (des‑duplicadas de `ArithPrf`),
copias privadas `prf_congr_substfc_a2/a3_loc`/`prf_congr_liftfc_a2_loc`/`prf_nthc_zero/succ_loc`.
Escollos: `ind`/`listInd` (términos gigantes) exigieron `have hy` explícito + `maxRecDepth 16000`.

**B.3c EN CURSO — `pcc_lineWF_tracked`** (el átomo `lineWF` punteado que `hC_dot` consume). Desbloqueado
por B.3b. Enunciado (refinado al arrancar — la **forma dotada** `substfc zero (tcFn t) (formCode …)`,
análoga exacta a `inDot`, NO `lineWFCodeFn (tcFn t)`):
`Prf (lineWF t ⇒ provFromCode (substfc zero (tcFn t) (formCode (lineWF #0))))`. Plan (diseño §16),
21 casos: (1) `prf_lineWF_inv t` da `⋁_{k} (lineTag t =eq k̇)` → `PrfH_or_elim`; (2) en la rama `k`, el
bicondicional‑accesor reduce `lineWF t` a `carc t =eq expr_k`; (3) reflejar ese `=eq`; (4) **transportar
de vuelta** por el bicondicional codificado (el corazón denso, «subproyecto de 21 casos»).

**Arranque de `eqrefl` (tag 12), progreso:**
* **Pasos 1–3 validados** (inversión + bicondicional‑accesor + `pcc_eq_tracked`).
* **PASO 4 — columna vertebral CONSTRUIDA y compilando** (`[propext, choice, Quot.sound, prf_inAxC]`),
  confirmando la plantilla `pcc_bddDot_imp_inDot`: **`hbwd`** = `∀.(tag ⇒ (=eq ⇒ lineWF))` (dirección ⇐
  currificada bajo el tag: `Prf.gen` + `prf_deduction`×2 + `iff.mpr` interno vía `Prf₀.c3`); y
  **`paso6_backbone`** = `Prov(⌜implc TAG_dot (implc EQ_dot LWF_dot)⌝)` (reflejar `hbwd` con
  `pcc_thm_inst` testigo `tcFn t` → distribuir `substfc` con `prf_substfc_impl`×2 → `prf_provCode_congr`).
  Código exacto en `NEXT-STEPS.md`.
* **FALTA (capa densa restante):** reflejar `TAG_dot`/`EQ_dot` (= `Prov(⌜nthc t 1 =eq 12⌝)` y
  `Prov(⌜carc t =eq …⌝)`) vía **evaluación provable** (`pcc_eval_nthc`/`pcc_eval_carc_nthc`, DENTRO de
  `Prov` bajo cota `i<lenc` — NO `pcc_eq_tracked` directo, que sería **Tarski**); dos `pcc_mp_code_open`;
  y envolver con la inversión (`PrfH_or_elim`×21). Es un bloque denso en sí (como `bddCarcDot`).

---

### 3.24 La REPARACIÓN — códigos como NUMERALES (ADR‑012)

**Last updated**: 2026-08-22 23:55 · **@importance**: `foundational`
**Módulos**: `Meta/NatOrderPrf.lean`, `Meta/NatMulPrf.lean`, `Meta/CantorMonoPrf.lean`,
`Meta/Div2ParityPrf.lean`, `Meta/CodeNumeralPrf.lean`, `Meta/DiagonalNumeral.lean`,
`Meta/StrongInductionPrf.lean` (+ refundación de `Meta/Sigma1CorePrf.lean`).

#### 3.24.1 La enfermedad, y por qué el numeral la cura

`tcFn` («código del código») tenía dos ecuaciones que recurren sobre estructuras **incompatibles**:
`ax_tc_zero`/`ax_tc_succ` sobre la estructura **NUMERAL**, y `ax_tc_cons` sobre la estructura de
**CÓDIGO**. Como `ax_L0_cons_def` identifica `cons h t = pair h (σt)`, en ℕ el mismo valor es ambas
cosas (`cons 0 nil = 2 = σσ0`), luego `tcFn` de ese valor debía ser dos códigos distintos a la vez ⇒
`axioms ⊢ ⊥`, verificado en el compilador.

**El diagnóstico de fondo:** `tcFn` pide a la teoría objeto ver información **intensional** que los
números no llevan — *qué término escribimos* para denotar N. Con `⌈φ⌉` como **numeral** esa
información no se pierde, porque el numeral **es** canónico.

#### 3.24.2 `Meta/CodeNumeralPrf.lean` — la aritmética del código, SIN división

**Namespace**: `ROBINSON_PlusPlus.Meta.CodeNumeralPrf` · **@importance**: `foundational`
**Dependencias**: `Div2ParityPrf`, `CantorMonoPrf`, `NatMulPrf`.

La pieza clave del diseño: `consN` se define con **números triangulares**, de modo que
`2·consN a b = cpOf ā b̄` es una identidad `Nat` **directa** — no hay que razonar sobre divisibilidad.

| Notación matemática | Firma Lean 4 |
|---|---|
| `triN n = 0+1+…+n` | `def triN : Nat → Nat` |
| `2·triN n = n(n+1)` | `theorem two_mul_triN : ∀ n : Nat, 2 * triN n = n * (n + 1)` |
| `consN a b = triN(a+b+1) + (b+1)` | `def consN (a b : Nat) : Nat := triN (a + (b + 1)) + (b + 1)` |
| `2·consN a b = (a+b+1)(a+b+2) + 2(b+1)` | `theorem two_mul_consN (a b : Nat) : …` |
| `⊢ ā + b̄ = (a+b)‾` | `theorem prf_gnum_add (a b : Nat) : Prf (add (numeral a) (numeral b) =eq numeral (a+b))` |
| `⊢ cons(ā, b̄) = consN a b‾` | `theorem prf_cons_eval (a b : Nat) : Prf (cons (numeral a) (numeral b) =eq numeral (consN a b))` |
| ídem, con premisas | `theorem prf_cons_eval_of {A B : Term} {a b : Nat} (ha …) (hb …) : Prf (cons A B =eq numeral (consN a b))` |
| `codeNat φ ∈ ℕ` (espejo meta de `formCode`) | `def codeNat : Formula → Nat` |
| **`⊢ formCode φ = codeNat φ‾`** | **`theorem prf_formCode_numeral : ∀ φ : Formula, Prf (formCode φ =eq numeral (codeNat φ))`** |

`codeNat` va acompañado de `codeNatChars`/`codeNatStr`/`codeNatTerm`/`codeNatTerms`, y cada uno de su
lema de evaluación (`prf_charsCode_numeral`, `prf_strCode_numeral`, `prf_termCode_numeral`,
`prf_termsCode_numeral`). `prf_formCode_numeral` es **meta‑recursión** sobre la estructura de `φ`.

**Hecho de magnitud medido** (`sondeos/S3S5.lean`): Lean **nunca reduce** `codeNat φ` — se mantiene
simbólico incluso con `φ` concreta. La vía es viable del lado de Lean.

#### 3.24.3 `Meta/Div2ParityPrf.lean` — `div2` sobre numerales, y la paridad de Cantor

**Namespace**: `ROBINSON_PlusPlus.Meta.Div2ParityPrf` · **@importance**: `high`
**Dependencias**: `CantorMonoPrf`, `NatMulPrf`, `NatOrderPrf`.

Todo en forma **OBJETO** (argumentos abstractos ⇒ vale para todo numeral) y **net‑0**
(`[propext, choice, Quot.sound]`).

| Notación matemática | Firma Lean 4 |
|---|---|
| `x < y ⇒ x·2 < y·2` | `theorem prf_mul_two_lt_mono (x y : Term) : Prf (lt x y ⇒ lt (mul x two) (mul y two))` |
| `x·2 = y·2 ⇒ x = y` | `theorem prf_mul_two_cancel (x y : Term) : Prf ((mul x two =eq mul y two) ⇒ (x =eq y))` |
| `mod2(x·2) = 0` | `theorem prf_mod2_double (x : Term) : Prf (mod2 (mul x two) =eq zero)` |
| `div2(x·2) = x` | `theorem prf_div2_double (x : Term) : Prf (div2 (mul x two) =eq x)` |
| **`div2(2m‾) = m̄`** | **`theorem prf_div2_numeral (m : Nat) : Prf (div2 (numeral (2 * m)) =eq numeral m)`** |
| `mod2(S·σS) = 0` (consecutivos) | `theorem prf_mod2_consec (S : Term) : Prf (mod2 (mul S (succ S)) =eq zero)` |
| `mod2(cpOf h t) = 0` | `theorem prf_mod2_cpOf (h t : Term) : Prf (mod2 (cpOf h t) =eq zero)` |
| **`(cons h t)·2 = cpOf h t`** | **`theorem prf_cons_double (h t : Term) : Prf (mul (cons h t) two =eq cpOf h t)`** |

Álgebra auxiliar portada aquí porque **eran axiomas objeto, no teoremas**: `prf_mul_distrib` (ax12),
`prf_mul_assoc` (ax11), `prf_mul_distrib_right`, `prf_swap_mul2`, más los homomorfismos
`prf_numeral_mul`/`prf_gnum_mul` (el de `·` sólo existía en la capa ω) y las congruencias
`prf_eq_congr_div2`/`prf_eq_congr_mod2`.

⚠️ `prf_cons_double` es **el puente** de la fase C de `pcc_dot_cons` (§3.25.3): es un teorema OBJETO,
luego se «dota» con `prf_congr_tcFn` **sin coste**.

#### 3.24.4 `Meta/NatOrderPrf.lean` · `Meta/NatMulPrf.lean` · `Meta/CantorMonoPrf.lean`

**@importance**: `high` · net‑0 (`[propext, choice, Quot.sound]`).

⚠️ **La asociatividad/conmutatividad de `+` y las leyes de `·` son AXIOMAS de la teoría objeto**
(`ax6`/`ax7`, `ax8`–`ax12`) — **no** hay que probarlas por inducción; estos módulos las **portan** al
cálculo finitario `Prf` y construyen encima.

* **`NatOrderPrf`** — orden `≤`: `prf_le_of_lt`, `prf_le_of_eq`, `prf_le_refl`, la cadena de
  transitividades (`prf_lt_trans`, `prf_lt_le_trans`, `prf_le_lt_trans`, `prf_le_trans`),
  sustitución bajo `≤`/`<` (`prf_le_subst1/2`, `PrfH_lt_subst1/2`) y `prf_add_assoc`/`prf_add_comm`.
* **`NatMulPrf`** — producto: `prf_mul_zero`, `prf_mul_succ`, `prf_mul_comm`, `prf_zero_mul`,
  `prf_mul_one`; monotonía aditiva y multiplicativa (`prf_add_le_mono_*`, `prf_mul_le_mono_right`);
  **cancelación** `prf_lt_of_mul_lt_mul_right`; tricotomía `prf_lt_trichotomy` e irreflexividad
  `prf_lt_irrefl`; `div2`/`mod2` (`prf_div_mod_eq` = ax17, `prf_mod2_range` = ax21).
* **`CantorMonoPrf`** — **`prf_cantor_mono_left (h t) : Prf (lt h (cons h t))`** y
  `prf_cantor_mono_right`: *el sub‑código es estrictamente menor que el código*. 13 pasos troceados.
  Aquí vive `abbrev cpOf (h t : Term) : Term` ( `= cantor_poly h (σt)` ) y `prf_cons_div2`,
  `prf_cons_div_mod`.

#### 3.24.5 `Meta/DiagonalNumeral.lean` — el lema diagonal rehecho, y **Gödel I**

**Namespace**: `ROBINSON_PlusPlus.Meta.DiagonalNumeral` · **@importance**: `foundational`
**Dependencias**: `CodeNumeralPrf`, `Diagonal`, `DiagonalTwo`, `OmegaReflect`.

| Notación matemática | Firma Lean 4 |
|---|---|
| `⊢ codeNat φ‾ = formCode φ` | `theorem hFN (φ : Formula) : axioms ⊢ (numeral (codeNat φ) =eq formCode φ)` |
| `ψ[⌈ψ⌉]` con el código NUMERAL | `noncomputable def selfAppN (ψ : Formula) : Formula` |
| `Prov` sobre el código numeral | `noncomputable def provCodeN (φ : Formula) : Formula` |
| la sentencia de Gödel numeral | `noncomputable def godelCN : Formula` |
| diagonalización | `theorem diag_arith_num (ψ : Formula) : …` |
| **punto fijo** | **`theorem godelCN_fixedpoint : axioms ⊢ (godelCN ⇔ neg (provCodeC' godelCN))`** |
| puente entre representaciones | `theorem provCode_transfer (φ : Formula) : axioms ⊢ (provCodeN φ ⇔ provCodeC' φ)` |
| **Gödel I — `⊬G`** | **`theorem goedel_first_numeral (hcon : ConsistentOmega) : ¬ Prf godelCN`** |
| Gödel I — indecidibilidad | `theorem goedel_first_undecidable_numeral (hcon : ConsistentOmega) (hrefl : Reflects godelCN) : (¬ Prf godelCN) ∧ (¬ Prf (neg godelCN))` |

**Por qué la refundación fue barata (~30 líneas):** `substFormula_arith (v) (s) (f)` toma **`s`
arbitrario**, luego traga un numeral sin más; y `godelPred`, `godelBeta`, `diagTerm` y `godel_comp`
**no cambian** — ninguno menciona la representación. Y **`provCode_transfer` es literalmente
`subst_eq_iff provFormulaC' (hFN φ)`** ⇒ D1 y la cadena existente se transfieren **componiendo con
ese bicondicional, sin re‑demostrarse**.

**Footprint de `goedel_first_numeral`** (verificado con `#print axioms`):
`[propext, Classical.choice, Quot.sound, dne, gen, imp_intro, ax_induction, ax_list_induction,
ax_axiomsCodeT_eq]` — la base sancionada de siempre, **menos `tc_cons`**.

⚠️ `goedel_first_undecidable_numeral` toma `Reflects` como **hipótesis META explícita**. La reducción
a ω‑consistencia (`reflects_of_omega`, §3.21) sigue vigente, pero **`NegVerifier` sigue abierto**:
`⊬¬G` **no** está cerrado en la cadena real. Ver `PLAN-NEGVERIFIER.md`.

#### 3.24.6 `Meta/StrongInductionPrf.lean` — inducción fuerte en `Prf`

**Namespace**: `ROBINSON_PlusPlus.Meta.StrongInductionPrf` · **@importance**: `medium`

`theorem prf_strong_induction (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ)
(step : Prf (Formula.forall (Formula.impl (PSI Φ) Φ))) : ∀ t : Term, Prf (substFormula 0 t Φ)`

con `PSI Φ` = el `∀m<n. Φ[m]` acotado, `prf_le_of_lt_succ (m n) : Prf (lt m (succ n) ⇒ le m n)`
(sin análisis de casos) y el andamiaje De Bruijn (`liftTerm_swap`, `psi_lift_eq_subst`, …).
⚠️ Distinto de `Full/StrongInduction.lean`, que está sobre `Derives` (capa ω) y **no es importable**
desde aquí — es un guion, no un módulo reutilizable.

#### 3.24.7 Refundación de `Meta/Sigma1CorePrf.lean` (el keystone de (a.1))

Tres declaraciones cambiaron de **enunciado**, no sólo de prueba:

| antes | ahora |
|---|---|
| `prf_provCodeC'_In_formCode_of_tracked` vía `prf_tc_form` | vía `prf_tc_numeral`; ⚠️ concluye sobre `In (numeral (codeNat φ)) L` |
| `prf_tc_objList` vía `prf_tc_of_cons` | `prf_objList_numeral` vía `prf_cons_eval_of` |
| `prf_tc_objList_formCode` | `prf_objList_formCode_numeral`, con `termCode (numeral N)` a la derecha |

Refundar el keystone **devolvió 10 módulos** de la cuarentena de golpe (31 → 21), entre ellos
`MpCodePrf` (`pcc_axiom_inst`) y `Sigma1AtomPrf` (`eqCodeFn`) — el prerrequisito para poder siquiera
**enunciar** la escalera (§3.25).

---

### 3.25 La ESCALERA (a.2) — Σ₁‑completitud INTERNALIZADA

**Last updated**: 2026-08-22 23:55 · **@importance**: `foundational`
**Módulos**: `Meta/EvalArithPrf.lean` (`+`), `Meta/EvalMulPrf.lean` (`·`), `Meta/DotConsPrf.lean`
(`cons`). Todos con footprint `[propext, Classical.choice, Quot.sound, prf_axiomsCodeT_eq]` — la
base sancionada, **sin `tc_cons`**.

**Qué es.** Los cuatro peldaños que llevan la evaluación aritmética **dentro de `Prov`**, para
argumentos **ABSTRACTOS** (no `numeral a` concretos). Es lo que devuelve la cuarentena: el viejo
`pcc_eval_carc` cerraba con `prf_tc_cons'`, el puente que la reparación mató, y `pcc_dot_cons` es su
sustituto — verificado en `sondeos/CarcPayoff.lean`.

| peldaño | teorema | dónde |
|---|---|---|
| `⊢ Prov(⌜ ȧ + ḃ = (a+b)˙ ⌝)` | `pcc_eval_add (a b : Term) : Prf (provFromCode (evalAddCode a b))` | §3.25.1 |
| `⊢ Prov(⌜ ȧ · ḃ = (a·b)˙ ⌝)` | `pcc_eval_mul (a b : Term) : Prf (provFromCode (evalMulCode a b))` | §3.25.2 |
| `div2` | `pcc_thm_inst` sobre `Prf.gen (prf_div2_double (.var 0))` — **sin inducción** | §3.25.3 |
| `⊢ Prov(⌜ cons(ḣ,ṫ) = (cons h t)˙ ⌝)` | `pcc_dot_cons (h t : Term) : …` | §3.25.3 |

#### 3.25.1 `Meta/EvalArithPrf.lean` — la suma, y la lógica ecuacional INTERNA

**@importance**: `foundational`. Además del peldaño `+`, este módulo aporta el **toolkit reutilizable**
de razonamiento ecuacional dentro de `Prov`:

| Notación | Firma Lean 4 |
|---|---|
| Leibniz codificado, aplicado | `theorem pcc_leibniz_apply (Ac t₁ t₂ : Term) (heq : Prf (provFromCode (eqc t₁ t₂))) (h1 : Prf (provFromCode (substfc zero t₁ Ac))) : Prf (provFromCode (substfc zero t₂ Ac))` |
| transitividad interna de `=` | `theorem pcc_eq_trans_code (X Y Z : Term) (hX : ∀ W, Prf (substtc zero W X =eq X)) …` |
| congruencia interna de `σ` | `theorem pcc_congr_succ_code (X Y : Term) …` |
| invariancias `substtc` | `substtc_inv_tcFn`, `substtc_inv_succcT`, `substtc_inv_addcT` |
| formas IMPLICACIÓN (para `prf_nat_induction`) | `pcc_leibniz_apply_imp`, `pcc_eq_trans_code_imp`, `pcc_congr_succ_code_imp` |

La restricción real del toolkit: al sustituir en el código‑contexto `Ac`, el `substtc` alcanza también
los subtérminos ya presentes ⇒ los lemas piden que el código fijo sea **`substtc`‑invariante**
(`∀ W, substtc zero W X =eq X`), hipótesis que (A) `prf_substtc_tcFn` y las ecuaciones de `funcc`
descargan para todos los códigos que se construyen.

#### 3.25.2 `Meta/EvalMulPrf.lean` — el producto

**Namespace**: `ROBINSON_PlusPlus.Meta.EvalMulPrf` · **Dependencias**: `EvalArithPrf`, `NatMulPrf`.

Espejo de `+` con `prf_nat_induction` como cierre. **La diferencia estructural:** `ax9_mul_succ` da
`x·σy = (x·y) + x`, cuyo lado derecho es un `add`, **no un `succ`** — por eso el paso inductivo
necesita dos piezas que `+` no tenía: `pcc_congr_addcT1_code_imp` (congruencia de `addcT` en el
**primer** argumento, para meter la HI) y `pcc_eq_subst2_code_imp` (sustitución en el **segundo**
argumento de `=` con la igualdad cerrada, que permite encadenar con `pcc_eval_add`).

`def mulcT (x y : Term) : Term` (código de `mul x y`), `def evalMulCode (a b : Term) : Term :=
eqCodeFn (mulcT (tcFn a) (tcFn b)) (tcFn (mul a b))`, más congruencia/`substtc`/invariancia
(`prf_congr_mulcT`, `prf_substtc_mulcT`, `substtc_inv_mulcT`).

#### 3.25.3 `Meta/DotConsPrf.lean` — **`pcc_dot_cons`**, el último peldaño

**Namespace**: `ROBINSON_PlusPlus.Meta.DotConsPrf` · **@importance**: `foundational`
**Dependencias**: `EvalMulPrf`, `Div2ParityPrf`, `CantorMonoPrf`, `MpCodePrf`, `SubstCodeOpenPrf`,
`NumCodeClosedPrf`.

```lean
theorem pcc_dot_cons (h t : Term) :
    Prf (provFromCode (eqc (consT (tcFn h) (tcFn t)) (tcFn (cons h t))))
```

**Sin inducción nueva.** `cons` no tiene ecuaciones recursivas propias: `ax_L0_cons_def` lo define
como `div2 (cantor_poly h (σt))`, o sea `+`, `·` y `div2`, los tres ya internalizados. Es
**ensamblaje**, en tres fases:

| fase | qué | pieza |
|---|---|---|
| **A** | la instancia codificada de `ax_L0_cons_def` **computa por `rfl`** (igual que `ax5`/`ax9`) | `prf_axL0_body_computes`, `pcc_axL0_computed` |
| **B** | el polinomio de Cantor se evalúa dentro de `Prov` en **cinco** pasos | `pcc_rw`, `pcc_rw_div2` |
| **C** | el `div2` se cancela contra `prf_div2_double`; puente `prf_cons_double` | `pcc_div2_cons` |

**API pública:**

| Notación | Firma Lean 4 |
|---|---|
| código de `cons x y` | `def consT (x y : Term) : Term` |
| código de `div2 x` | `def div2cT (x : Term) : Term` |
| código del polinomio de Cantor | `def cpOfT (X Y : Term) : Term` · variante plegada `def cpOfT' (X Y1 : Term) : Term` |
| **reescritura interna en un hueco** | `theorem pcc_rw (G : Term → Term) (hG : ∀ s, Prf (substfc zero s (G (varc (numeral 0))) =eq G s)) (X Y : Term) (heq : Prf (provFromCode (eqc X Y))) (hbase : Prf (provFromCode (G X))) : Prf (provFromCode (G Y))` |
| su molde para `L = div2(D ·)` | `theorem pcc_rw_div2 (L : Term) (hL …) (D : Term → Term) (hD …) …` |
| fase A | `theorem pcc_axL0_computed (h t : Term) : Prf (provFromCode (eqCodeFn (consT (tcFn h) (tcFn t)) (div2cT (cpOfT (tcFn h) (tcFn t)))))` |
| fase C | `theorem pcc_div2_cons (h t : Term) : Prf (provFromCode (eqc (div2cT (tcFn (cpOf h t))) (tcFn (cons h t))))` |
| `⌜2⌝ = 2˙` | `theorem prf_tc_two : Prf (tcFn two =eq termCode two)` |
| congruencias / `substtc` | `prf_congr_consT`, `prf_congr_div2cT`, `prf_congr_cpOfT`, `prf_congr_cpOfT2`, `prf_substtc_consT`, `prf_substtc_div2cT`, `prf_substtc_cpOfT`, `prf_substtc_two`, `substtc_inv_consT`, `substtc_inv_div2cT` |

##### 🔑 Las dos técnicas — reutilizables para cualquier evaluación dentro de `Prov`

1. **Todo teorema OBJETO se «dota» GRATIS.** `tcFn` es un símbolo de función, luego `prf_congr_tcFn`
   transporta cualquier `Prf (a =eq b)` a `Prf (ȧ =eq ḃ)` **a nivel de código, sin entrar en `Prov`**.
   Por eso `prf_cons_double` sirve de puente sin coste y los pasos `σ(ẋ) ⟶ (σx)˙` son libres
   (`prf_tc_succ'`). **Antes de razonar dentro de `Prov`, comprobar si el paso es objeto.**
2. **`substfc` sustituye TODAS las ocurrencias del hueco.** El polinomio `(x+y)·σ(x+y)+2y` menciona
   `x+y` **dos veces**; reescribir por posiciones exigiría congruencias a cada profundidad. Con el
   contexto `Ac := C[v₀]` un **único** `pcc_leibniz_apply` cierra las dos. De ahí que la fase B sean
   5 pasos y no 15. `pcc_rw` empaqueta el patrón.

##### El rédito, verificado

`sondeos/CarcPayoff.lean` reconstruye **`pcc_eval_carc`** con el mismo enunciado y el mismo footprint.
El viejo (`cuarentena/EvalListPrf.lean:123`) cerraba con `prf_tc_cons'`; la sustitución es **un único
`pcc_rw` con `pcc_dot_cons`**, y los pasos 1‑3 (instancia de `ax_carc` + los dos `substfc` computados)
quedan **intactos**. ⇒ el keystone `EvalListPrf` es repatriable, y el patrón de arreglo es mecánico.
⚠️ El transporte pasa de ser **de código** (fuera de `Prov`) a ser **interno** (dentro), así que hay
que dar el contexto `G` y su ecuación de `substfc`.

---

---

### 3.26 LA REPATRIACIÓN — los 31 módulos de vuelta (2026-08-23)

**Last updated**: 2026-08-23 · **@importance**: `foundational`
**Módulos**: los 21 que quedaban en `cuarentena/` + las piezas nuevas que los hicieron posibles.

La reparación (§3.24) apartó 31 módulos porque dependían de la **lectura sintáctica de `tcFn`**.
Todos han vuelto, **con el footprint sancionado** y **sin cambiar ningún enunciado público**.

#### 3.26.1 Las tres sub‑familias muertas, y su sustituto

| familia | por qué murió | sustituto |
|---|---|---|
| `prf_tc_cons'` | consecuencia directa de `ax_tc_cons`; **falsa** para argumentos abstractos bajo la lectura numeral | **`pcc_dot_cons`** (§3.25.3) — la misma ecuación, **dentro de `Prov`** |
| `prf_tc_form` | meta‑recursión con paso `prf_tc_of_cons` (muerto) | `prf_tc_form_numeral` + **conversión en la FRONTERA** |
| KIT `prf_tc_nul`/`_un`/`_bin` | composición pura de `prf_tc_cons'` | `pcc_dot_nul`/`_un`/`_bin`, **por composición de `pcc_dot_cons`** |

#### 3.26.2 Las herramientas nuevas

| notación | firma Lean 4 | dónde |
|---|---|---|
| reescritura interna, forma **implicación** | `theorem pcc_rw_imp (G : Term → Term) (hG : ∀ s, Prf (substfc zero s (G (varc (numeral 0))) =eq G s)) (X Y : Term) (heq : Prf (provFromCode (eqc X Y))) : Prf (provFromCode (G X) ⇒ provFromCode (G Y))` | `DotConsPrf` |
| molde unario (`Prf`) | `theorem pcc_rw_dot_cons_un (F : Term → Term) (hFs …) (hFc …) (R : Term) (hR …) (h t : Term) (hbase …) : Prf (provFromCode (eqCodeFn (F (tcFn (cons h t))) R))` | `EvalListPrf` |
| molde binario (`PrfH`) | `theorem pcc_rw_dot_cons_nthc {Γ} (h t IDX RHS : Term) (hI …) (hR …) (hbase …) : PrfH Γ (provFromCode (eqCodeFn (nthcT (tcFn (cons h t)) IDX) RHS))` | `EvalNthcPrf` |
| sustituto de `prf_tc_form` | `theorem prf_tc_form_numeral (φ : Formula) : Prf (tcFn (formCode φ) =eq termCode (numeral (codeNat φ)))` | `D3InDotPrf` |
| **convertidor de frontera** | `theorem pcc_to_formCode_imp (φ : Formula) (G : Term → Term) (hG …) : Prf (provFromCode (G (termCode (numeral (codeNat φ)))) ⇒ provFromCode (G (termCode (formCode φ))))` | `D3InDotPrf` |
| KIT internalizado | `pcc_dot_nul (m)` · `pcc_dot_un (m a)` · `pcc_dot_bin (m a b)` (+ `_symm`) | `CodeCtorKit` |
| ecuación `tc` del árbol `eqc` | `theorem pcc_dot_eqc (a b : Term) : Prf (provFromCode (eqCodeFn (eqcT (tcFn a) (tcFn b)) (tcFn (eqc a b))))` | `LineWFTrackedPrf` |
| código del código del árbol | `theorem pcc_tc_objAt (t : Term) : ∀ T : CTree, Prf (provFromCode (eqc (tcFn (T.objAt t)) (T.dotV t)))` | `CodeTreeReflect` |
| los dos códigos de `formCode f` | `theorem pcc_tc_formCode_internal (f : Formula) : Prf (provFromCode (eqCodeFn (tcFn (formCode f)) (termCode (formCode f))))` | `InAxiomsCodePrf` |

#### 3.26.3 El punto delicado: `pcc_to_formCode` y por qué el lado derecho NO era negociable

`inDot φ` está fijado por `D3DottedPrf` —activo y net‑0— como
`substfc 0 (tcFn #0) (formCode (In (formCode φ) (runFn nil #0)))`. Ese código lleva
`termCode (formCode φ)`, **no** la forma numeral, y **es el objetivo de D3**: sale de la definición
de `provCodeC'`. Cambiarlo no sería refundar un enunciado, sería **cambiar el teorema**.

La salida: los dos códigos son los de dos términos objeto **provablemente iguales**
(`prf_formCode_numeral`), y **D1 dota cualquier teorema `Prf`**. El puente sale gratis dentro de
`Prov`: `repr_pos'_prf (prf_eq_symm (prf_formCode_numeral φ))` es exactamente el `heq` que `pcc_rw`
pide. ⇒ **probar por dentro en forma numeral y convertir en la frontera**, dejando los enunciados
públicos intactos.

#### 3.26.4 El trabajo voluminoso: `pcc_tc_objAt`

`prf_tc_objAt` era **recursión estructural sobre `CTree`** produciendo una igualdad **de código**.
Con sustitutos internos, la recursión entera se muda **dentro de `Prov`**. La conversión resultó
**literal, pieza por pieza**, y todas las piezas existían:

| antes | ahora |
|---|---|
| `prf_eq_trans` | `pcc_eq_trans_code` (`EvalArithPrf`) |
| `prf_congr_unT` / `prf_congr_binT` | `pcc_congr_unT_code` / `pcc_congr_binT_1_code` / `_2_code` (`CodeCtorKit`) — **sobrevivieron intactas** y ya venían en forma implicación |
| `prf_refl` | `prf_provFromCode_eqCodeFn_refl` |
| ecuaciones `tc` del kit | `pcc_dot_nul_symm` / `_un_symm` / `_bin_symm` |

⚠️ Único cambio de forma: en el caso binario hacen falta **dos** congruencias encadenadas donde
antes bastaba una simultánea — **dentro de `Prov` los argumentos se reescriben de uno en uno**.

#### 3.26.5 Estado tras la repatriación

**D3 está reducida a UN SOLO lema**, ahora sobre la teoría **reparada**:

```lean
d3_prf_of_chainOkDot (φ) : Prf (chainOk nil #0 ⇒ provFromCode chainOkDot)
                         → Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ))
```

Y `pcc_lineWF_tracked_modulo_7` verifica que cerrar `pcc_lineWF_tracked` es **exactamente** cerrar
los **7 reflectores** que faltan (`q1 q2 q3 leibniz ind qconf listInd`).

⚠️ Esos 7 son **el muro de `substfc`**: llevan `substfc`/`liftfc` sobre argumento **abstracto** y
necesitan `pcc_eval_substfc`, que **no existe**. Requiere sancionar un predicado de buena‑formación
(`isFormCode`, <12 axiomas) — **decisión pendiente**, con objeciones de conservatividad sin resolver.
**La repatriación devuelve el proyecto a donde estaba antes de la inconsistencia; no lo lleva más lejos.**


---

## §3.27 · EL FRENTE `substfc` POR LA VÍA DE **CERO AXIOMAS** (2026‑08‑24 → 08‑29)

> ⚠️ **Supersede el cierre de §3.26.** Aquélla terminaba diciendo que los 7 tags «requieren
> sancionar un predicado de buena‑formación (`isFormCode`, <12 axiomas) — decisión pendiente».
> **La decisión se tomó, y fue la contraria**: la buena‑formación se define en vocabulario objeto
> **EXISTENTE**, con **cero axiomas nuevos**. Todo lo de abajo está compilado y vive en `sondeos/`.

### 3.27.1 · Por qué (1) no era «más cara» sino **otro teorema**

> ## ⛔ APARTADO **REFUTADO** — leer §3.32.1 antes de citarlo
>
> El razonamiento de abajo concluye que un axioma nuevo **cambiaría la sentencia G**. **Es falso**,
> medido el 2026‑08‑31 sobre el `Environment` de Lean: `godelCN` tiene **483 dependencias
> transitivas y NINGUNA es `axioms`**, porque `axiomsCodeT`/`lineWF`/`chainOk`/`runFn` son **átomos
> opacos** que `provFormulaC'` menciona sólo por su nombre.
>
> Lo que sí es cierto y se conserva: cambiar `axioms` **cambia la teoría de la que G habla** — la
> fórmula es la misma, lo que cambia es **qué demuestra `Prov`**. Eso puede seguir siendo motivo
> para no hacerlo, pero **es un argumento distinto** del que se escribió aquí, y mucho más débil
> como razón de coste. Se conserva el texto como registro del razonamiento del 08‑26.

La comparación se cerró con un dato de fuente, no de estimación: `ax_axiomsCodeT_eq`
(`Minimal/Axioms.lean:1376`) ancla a **`axioms`** (los 141, `:1199`) y **no** a `coreAxioms`
(`:922`). Luego los axiomas de la opción (1) **tienen** que entrar en `axioms` para funcionar,
`axiomsCodeT` los absorbe, el verificador interno los cita y **`provCodeC'` cambia ⇒ G cambia**
(141 → ~159). Ningún ahorro de líneas compra eso.
Corolario registrado: **aunque se sancionara (1), los sondeos de (2) serían su certificado de
conservatividad** — la prueba NO vacua que `ax_lineWF_inv` sólo afirma de palabra.

### 3.27.2 · La PARTICIÓN en tres — y el cuadre que la hace necesaria

| predicado | disyuntos | ecuaciones de su sustitución |
|---|--:|---|
| `isFormCode` | **8** | `substfc`: **8** (`Axioms.lean:497‑520`) |
| `isTermCode` | **2** | `substtc`: **2** |
| `isTermsCode` | **2** | `substtsc`: **2** |

🔑 `pcc_eval_substfc` se atasca **porque 12 ≠ 8**. Partido, cada mitad encaja. El total **no crece**
(12 = 8+2+2): es **partición**, no recubrimiento. ⇒ **partir no repara un defecto: es la CONDICIÓN
para que la inducción exista.**
Y **discrimina**: `crit_isFC_junk_REFUTED` es net‑0 — el `implc ⌜x₀⌝ₜ ⌜x₀⌝ₜ` que el predicado
**fusionado** aceptaba, el partido lo **refuta**. (`sondeos/ParticionTresPredicados.lean`,
`sondeos/ParticionDiscrimina.lean`.)

### 3.27.3 · Los teoremas, con firma

```lean
-- A1/A2 (sondeos/InTracked.lean) · el reflector de `In` sobre lista ABSTRACTA, que no existía
pcc_boundedIn_tracked (x w : Term) : Prf (boundedIn x w ⇒ provFromCode (bdInDot x w))
pcc_In_tracked        (x w : Term) : Prf (In x w ⇒ provFromCode (bdInDot x w))
pcc_binOk_tracked (w X : Term) (k : Nat) : Prf (binOk w X k ⇒ provFromCode (binOkDot w X k))

-- A3 (sondeos/A3IsFCBTracked.lean) · el reflector COMPLETO
pcc_isFCB_tracked (w c : Term) : Prf (isFCB w c ⇒ provFromCode (isFCBDot w c))

-- hito (i) (sondeos/SubCodesWitness.lean) · todo φ tiene testigo explícito
prf_isFCB_subCodes (φ : Formula) : Prf (isFCB (objList (subCodes φ)) (formCodeM φ))
prf_isFC (φ : Formula)           : Prf (∃w. isFCB w ⌜φ⌝)

-- ① (sondeos/DiscriminaEcuacional.lean) · UN solo lema cubre los 12 disyuntos
prf_shape_strengthens (X C : Term) (k n : Nat)
    (hcarc : Prf (carc C =eq numeralM k)) (hlenc : Prf (lenc C =eq numeralM n))
    (hcons : Prf (consOk C)) :
    Prf (X ≐ C ⇒ consOk X ∧ (carc X ≐ k̄ ∧ lenc X ≐ n̄))

-- ② (sondeos/DiscriminaTestigoAbierto.lean) · discriminación con testigo ABIERTO
crit_junk_var0_witness         : el junk refutado con testigo LITERALMENTE `#0`
crit_isFCB3_no_termcode_var0   : ídem en la cara de FÓRMULA

-- ③ paso 1 (sondeos/CtorDotados.lean) · los constructores de código dotados
substfcT / substtcT / substtscT / liftcT / liftfcT / liftscT   -- DEFINICIONES, cero axiomas
pcc_congr_substfcT_arg1/2/3_code    -- las congruencias INTERNAS

-- ③ paso 2, caso ∀ (sondeos/Paso2CasoForall.lean)
paso2_caso_forall (v s f : Term) (hIH …) (hLift …) : …   -- cierra salvo `hLift`

-- la clausura, SIN axiomas (sondeos/ClausuraLiftSinWTs.lean)
prf_isTC1_lift (w c : Term) : Prf (isTC1 w c ⇒ isTC1 (liftsc 0 w) (liftc 0 c))
CRIT_hasWit_lift (c : Term) : Prf (hasWit c ⇒ hasWit (liftc 0 c))
```

### 3.27.4 · Las cuatro ideas reutilizables

1. **Dotar un átomo COMO ÁTOMO** en vez de desplegarlo (`inFormCodeFn`, y luego `allInFn`): el
   cuerpo queda **sin binder** y el problema De Bruijn **se disuelve**. Pagó dos veces —en A3 y en
   el reflector del predicado sin‑`wTs`.
2. **Probar contra la lista COMPLETA** (generalizar sobre un superconjunto) en vez de usar
   monotonía: ahorra un or‑elim de 12 casos por composición.
3. **Llevar el lift en vez de quitarlo**: `wfAllT` ya lo lleva en su definición;
   `FOL.substTerm_liftTerm` hace el trabajo **para cualquier `p`**, cerrado o no.
4. **Poner el lift en el OBJETIVO, no en la hipótesis**: no existe lema de lifting de
   **derivaciones**, así que el testigo va **dentro del objetivo** del `∃`‑elim, donde el
   `liftFormula 0` lo aplica uno mismo.

### 3.27.5 · Lo ABIERTO, y lo que NO se sabe

> ⚠️ **APARTADO SUPERADO — leer §3.28.** El `DESCENSO` que aquí se declara abierto quedó
> **PROBADO** el 2026‑08‑30 (`2f27a29`), y con él `pcc_eval_liftc`. Se conserva este texto como
> registro de la medición del 08‑29, no como estado vigente. De los cuatro puntos «sin determinar»
> de abajo, **el cuarto quedó medido** (§3.28.3); los otros tres siguen abiertos.

**Abierto, y es PLANO** (ni `provFromCode` en la hipótesis ni `bdAllCode` en la estructura):
```lean
DESCENSO : ∀ w s, Prf (isTC1 w s) → Prf (targetLift s)
```
con `targetLift s := provFromCode (eqc (liftcT ⌜0⌝ ṡ) (tcFn (liftc 0 s)))`, que **es**
`pcc_eval_liftc`. Base y paso ya cerrados (`refl_lista_nil`, `refl_lista_cons`, los casos
`varc`/`funcc`). ⚠️ `prf_strong_induction` exige `liftFormula 1 Φ = Φ` ⇒ **`w` cuantificado DENTRO
de `Φ`**.

**SIN DETERMINAR**, dicho explícitamente:
* **El puente a forma ECUACIONAL de la imagen punteada.** El reflector entrega `shapeDot` en forma
  `carc`/`lenc`, **sin `consOk`** ⇒ `wfAll1Dot w ≠ formCode (wfAll1 w)`: el consecuente es
  estrictamente **más débil** que la imagen del predicado objeto. Convención heredada de A3.
* **Los DOS reconocedores están DESCONECTADOS**: el reflejado (con `wTs`) y el plano (sin `wTs`,
  con **cero** imagen punteada). Nada los relaciona.
* La composición con el reconocedor de **FÓRMULA** llevando esta carga: **no hecha**.
* De `pcc_eval_substfc` sólo está medido el caso `∀`. Los otros 7 constructores: **sin medir**.

### 3.27.6 · Tres correcciones al propio registro (material de método)

* **`d783b9f` estaba mal cerrado.** Decía «`pcc_eval_liftc` NO hace falta». **Sí hace falta**:
  `paso2_caso_forall` la deja como única hipótesis colgando. Se refutó la **razón** del gate, no su
  **conclusión**. Modo de fallo: **generalizar de META a OBJETO**, que es donde vive la HI.
* **La recomendación «acotar» era circular**: acotar y la clausura de un paso son
  **inter‑construibles**, probado en las dos direcciones (`sondeos/AcotarEsLaMismaObligacion.lean`).
* **«Ningún descenso de `substfc` cruza un binder de código» es FALSO** (hay 12 descensos a nivel 1).
  El enunciado correcto: **ninguno corre sobre código de fórmula OPACO**.

---

## §3.28 · EL **DESCENSO**, CERRADO — `pcc_eval_liftc` existe (2026‑08‑30)

Cierra el único lema que §3.27 dejaba abierto. Todo en `sondeos/`, **cero axiomas de Lean nuevos,
cero `sorry`**, recompilado a mano (`EXIT=0`, build 118 jobs). Commits `2f27a29` y `c8f100f`.

### 3.28.1 · Los teoremas, con firma

`sondeos/DescensoLiftc.lean` (2011 l.):

```lean
-- :79    el objetivo, como definición
def targetLift (s : Term) : Formula :=
  provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))

-- :1362  la forma implicativa
theorem DESCENSO_imp (w s : Term) : Prf (Formula.impl (isTC1 w s) (targetLift s))
-- :1371  el DESCENSO, con w y s ABSTRACTOS
theorem DESCENSO (w s : Term) (h : Prf (isTC1 w s)) : Prf (targetLift s)
-- :1379  y su identidad: ES pcc_eval_liftc, no una aproximación
theorem pcc_eval_liftc (w s : Term) (h : Prf (isTC1 w s)) :
    Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))) :=
  DESCENSO w s h
-- :1388  LA FORMA QUE CONSUME EL PASO 2: el testigo, cuantificado
theorem DESCENSO_hasWit (s : Term) : Prf (Formula.impl (hasWit s) (targetLift s))
```

Con su gemela sobre listas de argumentos (`DESCENSO_lista`, `:1374`) y los controles positivos que
impiden que sea vacuo: `CRIT_targetLift_real` (`:1904`), `CRIT_real_A`/`_B` sobre términos
concretos, y `CRIT_hasWit_real` (`:1964`) — **todo `t` tiene testigo**.

### 3.28.2 · El motivo: **una** inducción, con conclusión **conjuntiva**

Tres estrategias independientes, verificadas adversarialmente, **3 de 3 confirmadas**. Lo
interesante es que **las tres convergieron por separado en el mismo motivo, y no era el previsto**:

```lean
PHI := ∀. ∀w. (isTC1 w #0 ⇒ targetLift #0) ∧ (isTsC1 w #0 ⇒ targetLiftsc #0)
```

No dos inducciones mutuas, sino **UNA** inducción fuerte cuya conclusión es una **conjunción**, con
`w` cuantificado **dentro** de `Φ` (lo que exige el gate `liftFormula 1 Φ = Φ`, `hPHI` en `:1199`).
**La mutua explícita resultó innecesaria** — el término y la lista de argumentos viajan juntos.

🔑 **Y la tercera vía se respondió a sí misma en NEGATIVO, con prueba.** Se planteó si bastaba
probar `hLift` sólo para el `s` concreto que aparece en el caso `∀`. La respuesta es que **ese `s`
es `#0`**: pedirlo para él **es pedirlo para todo `s`**. No había atajo, y quedó **demostrado en
vez de supuesto** — que es la diferencia entre cerrar una vía y abandonarla.

### 3.28.3 · El residuo de acople, también resuelto

Los tres intentos señalaron, sin que se les preguntara, el mismo defecto de encaje: `pcc_eval_liftc`
llega con **guarda** (`hasWit s`) y el `Φ` del consumidor (`Paso2Ind.PHI`,
`sondeos/Paso2CasoForall.lean:689`) no la tenía. Medido en `sondeos/GateGuardaEnriquecida.lean`:

```lean
-- :119
def PHI_guarded : Formula :=
  Formula.forall (Formula.forall (Formula.impl (hasWit (.var 0))
    (provFromCode (evalSubstfcCode (.var 1) (.var 0) (.var 2)))))

-- :126  EL GATE, SUPERADO
theorem PHI_guarded_lift : liftFormula 1 PHI_guarded = PHI_guarded
```

🔑 **Y pasa sin binder nuevo**, porque `hasWit c := ∃. isTC1 #0 ↑c` es un `∃` **interno**: el número
de binders **exteriores** no cambia, que es lo único que mira el gate. La propagación de la guarda
al subcódigo ya existía: `CRIT_hasWit_lift` (`sondeos/ClausuraLiftSinWTs.lean:1392`),
`Prf (hasWit c ⇒ hasWit (liftc zero c))`.

El fichero incluye además el control negativo de que la guarda **no es decorativa**
(`fail_if_success` contra `PHI_guarded = PHI_actual`, `:177`) y la fontanería De Bruijn nueva
(`liftF_hasWit` `:88`, `substF_hasWit` `:159`, `PHI_guarded_at` `:167`).

### 3.28.4 · ⚠️ Dónde está el siguiente muro — y **no es donde se miraba**

De los **8** constructores de `substfc` sólo está hecho `pcc_substfc_forall_dot`
(`Paso2CasoForall.lean:282`). **CINCO** de los siete restantes son **mecánicos** (`botc` `implc` `andc` `orc` `exc`). Los DOS distintos son
`eqc` y `atomc`, que recurren a `substtc`/`substtsc` (ya lo anticipaba `ec_objeto_eq`, `:662`:
*«el `substfc` recurre a `substtc` ⇒ el teorema es MUTUO»*).

**`pcc_eval_substtc` es ESTRICTAMENTE MÁS DURO que el DESCENSO**, por dos razones verificadas en el
código y no conjeturadas:

| | `pcc_eval_liftc` (hecho) | `pcc_eval_substtc` (pendiente) |
|---|---|---|
| **la guarda** | **CERRADA**: `liftc zero` ⇒ la condición es `zero < σn`, se descarga **de una vez** | **ABIERTA**: `substtc v s (varc n)` tiene **tres** cláusulas guardadas (`<`, `=`, `>`) con **`v` abstracto** ⇒ hay que reflejar la **tricotomía DENTRO de `Prov`** |
| **la salida** | se mantiene en el mismo vocabulario | `ax_substtc_var_gt` devuelve **`varc (pred n)`** ⇒ pide la evaluación **dotada de `pred`**, que **no existe** |

⇒ el trabajo pendiente del frente **no** es «siete casos más como el `∀`»: son **CINCO mecánicos**
(`botc` nulario, `implc`/`andc`/`orc` binarios sin `liftc`, y `exc` que es el **espejo** del `∀` ya
hecho) **y DOS con obstrucción propia** (`eqc` y `atomc`). Conviene atacarlo sabiéndolo.

⚠️ **Corrección aritmética (2026‑08‑30)**: la primera redacción de este apartado decía «seis de los
siete restantes son mecánicos» a la vez que nombraba **dos** como distintos — 7 − 2 = **5**, no 6.
Contado contra la fuente (`Minimal/Axioms.lean:498‑520`, las ocho `ax_substfc_*`): `bottom` `atom`
`eq` `impl` `forall` `and` `or` `ex`.

### 3.28.5 · 💰 Coste de promoción (medido, no estimado)

`targetLift`, `isTC1`, `wfAll1` y `argsIn` viven **sólo en `sondeos/`**. Promover el DESCENSO a
`Meta/EvalLiftcPrf.lean` obliga a promover **antes** `ReflectorDesdeConsumidor` y
`ClausuraLiftSinWTs`. Piezas sueltas que van con ello: `PrfH_mono`/`PrfH_w1` →
`Meta/HilbertDeduction.lean`; `prf_nil_or_cons` → `Meta/ChainPrf.lean`. Nada de esto es difícil,
pero **no es gratis** y no figuraba en ninguna estimación previa.

### 3.28.6 · ✅ `paso2_caso_forall` REHECHO en forma `PrfH Γ` — la hipótesis colgante desaparece

`sondeos/Paso2Guardado.lean`, recompilado a mano (`EXIT=0`):

```lean
theorem paso2_caso_forall_guarded (v s f : Term)
    (hIH : Prf (Formula.impl (hasWit (liftc zero s))
                 (provFromCode (evalSubstfcCode (succ v) (liftc zero s) f)))) :
    Prf (Formula.impl (hasWit s) (provFromCode (evalSubstfcCode v s (forallc f))))
```

**Una sola hipótesis**: la HI legítima sobre el subcódigo `f`. `hLift` ha desaparecido —
`DESCENSO_hasWit` la descarga desde la guarda, y `CRIT_hasWit_lift` pasa la guarda a la HI.
Footprint **idéntico** al de `Paso2.paso2_caso_forall`, reprobado en el mismo fichero
(`[propext, Classical.choice, Quot.sound, prf_axiomsCodeT_eq]`) ⇒ **la reescritura no añade nada**.
Controles de no‑vacuidad: `CRIT_guarda_no_vacua` y `paso2_caso_forall_guarded_real` (sobre código
real la guarda se descarga y queda la ecuación **pelada**).

#### ⚠️ Dos correcciones a lo que decía la versión anterior de este apartado

1. **El obstáculo anunciado no era tal.** Se dijo que la cadena se monta con `pcc_eq_trans_code`,
   que toma sus dos eslabones como `Prf`, y que bajo `PrfH Γ` haría falta un helper nuevo.
   **`PrfH_eq_trans_code` ya existía en producción** (`Meta/EvalCarcNthcPrf.lean:66`, exportado en
   `:142`) con la firma exacta ⇒ la cadena se reescribe **1:1**. El mismo bloque trae
   `PrfH_mp_code_apply` (`:53`) y `PrfH_leibniz_apply` (`:59`).
2. **Trampa real y nueva: `hasWit` son DOS CONSTANTES DISTINTAS.** `DESCENSO_hasWit` habla de
   `DescMutua.hasWit` (`DescensoLiftc.lean:1386`) y `CRIT_hasWit_lift` de `SinWTs.hasWit`
   (`ClausuraLiftSinWTs.lean:1389`): definiciones **literalmente iguales**, constantes diferentes,
   que Lean **no identifica en el enunciado**. Sin puente, los dos sondeos **no componen**. Cerrado
   con `hasWit_bridge := rfl`, **net‑0** (`does not depend on any axioms`), lo que certifica que la
   coincidencia es **definicional** y no un apaño. ⇒ para `hasWit`, los dos reconocedores ya **no**
   están desconectados (§3.27.5 sigue valiendo para el resto).

#### ⚠️ Límite de alcance

El descargue de la guarda está verificado para códigos **REALES** (`CRIT_hasWit_real` da testigo
para todo `termCodeM t`). Los **7 reflectores de `lineWF` llevan argumento ABSTRACTO** ⇒
necesitarán `hasWit` de ese argumento abstracto para quitarse la guarda. No es un defecto de este
teorema, pero **no está resuelto**.

#### Pieza genérica de propina

`sondeos/EqTransCodeImp2.lean`: `pcc_eq_trans_code_imp2 (X Y Z) (hX) : Prf (⌜X=Y⌝ ⇒ ⌜Y=Z⌝ ⇒ ⌜X=Z⌝)`
—la transitividad interna con **ambos** eslabones como antecedentes, que no existía— y
**`prfH_deduction`**, deducción dentro de `PrfH`, que tampoco. Resultaron **innecesarias** para el
objetivo, pero son genéricas y reutilizables.

### 3.28.7 · ▶ El paso siguiente

Los **5 constructores mecánicos** restantes de `pcc_eval_substfc` (`botc` `implc` `andc`
`orc`, más el espejo del `∀`), y después **`pcc_eval_substtc`** con la obstrucción propia de
§3.28.4.

---

## §3.29 · LOS CONSTRUCTORES DE `substfc` (2026‑08‑30)

> ## ⛔ CORRECCIÓN 2026‑08‑31 — **son SEIS, no ocho**
>
> Este apartado se tituló «los OCHO constructores, cubiertos». **Es falso, y el error es mío.**
> Verificado por grep sobre todo el árbol: los casos montados sobre `evalSubstfcCode` son
> `paso2_caso_bottom`, `paso2_caso_bin` (que cubre `implc`/`andc`/`orc`), `paso2_caso_forall` y
> `paso2_caso_ex_guarded` ⇒ **`botc` `implc` `andc` `orc` `forallc` `exc` = SEIS**.
> **`eqc`(4) y `atomc`(3) NO están montados en ningún sitio** (`paso2_caso_eq`/`paso2_caso_atom`:
> **0 hits**).
>
> **El error de razonamiento**: conté como «caso cubierto» lo que sólo era su **INGREDIENTE**.
> `pcc_eval_substtc'` y `pcc_eval_substtsc'` existen, son net‑0 y son correctos — pero están
> enunciados sobre `substtc`/`substtsc`, **no sobre `evalSubstfcCode`**. Montarlos es un paso
> aparte, y es trabajo real.
>
> Lo detectaron **dos agentes del ensamblaje por separado**, y lo confirmé yo por grep.
> Los apartados de abajo son correctos salvo por esa cuenta.

Cuatro sondeos nuevos, **todos net‑0**, recompilados a mano desde su ubicación final (`EXIT=0`),
build de producción intacto en 118 jobs. **3 CONFIRMADOS + 1 PARCIAL**, y el `PARCIAL` no es por la
matemática — es por un **hallazgo falso** que el verificador cazó (§3.29.5).

⚠️ **Cubiertos ≠ ensamblado.** Tener los ocho casos **no** es tener `pcc_eval_substfc`: falta la
inducción que los junta. Y todo vive en `sondeos/`, con el coste de promoción de §3.28.5 sin pagar.

### 3.29.1 · El cuadro completo

| # | constructor | estado | dónde |
|--:|---|---|---|
| 2 | `botc` | ✅ nulario, 4 eslabones | `sondeos/SubstfcPlanos.lean` |
| 5,7,8 | `implc` `andc` `orc` | ✅ **una prueba, no tres** | `sondeos/SubstfcPlanos.lean` |
| 6 | `forallc` | ✅ (2026‑08‑29/30) | `sondeos/Paso2CasoForall.lean` · `Paso2Guardado.lean` |
| 9 | `exc` | ✅ espejo **perfecto**, factorizado | `sondeos/SubstfcEx.lean` |
| 4 | `eqc` | ✅ vía `pcc_eval_substtc'` | `sondeos/EvalSubsttc.lean` |
| 3 | `atomc` | ✅ vía `pcc_eval_substtsc'` | `sondeos/EvalSubsttc.lean` |

### 3.29.2 · 🔑 Los tres binarios son **la misma fórmula salvo el tag** — y se certifica por `rfl`

```lean
def AXBIN_BODY (T : Term) : Formula :=
  substfc #3 #2 (binct T #1 #0) =eq binct T (substfc #3 #2 #1) (substfc #3 #2 #0)
theorem AXBIN_impl : ax_substfc_impl = forall_4 (AXBIN_BODY (numeralM 5)) := rfl
theorem AXBIN_and  : ax_substfc_and  = forall_4 (AXBIN_BODY (numeralM 7)) := rfl
theorem AXBIN_or   : ax_substfc_or   = forall_4 (AXBIN_BODY (numeralM 8)) := rfl
```

⇒ se factorizan en `pcc_substfc_bin_dot` (genérico en la etiqueta como `Term` abstracto) y
`paso2_caso_bin` (genérico en `k : Nat`); los tres casos finales son **cuatro líneas cada uno**. El
ensamblaje sale genérico **gratis** porque `binT`, `pcc_dot_bin`, `pcc_dot_bin_symm` y
`pcc_congr_binT_1/2_code` **ya son paramétricos en `k`** en producción.

### 3.29.3 · 🔑 La técnica que lo hizo posible, y vale fuera de aquí

Con la etiqueta abstracta, `substCodeF 3 W₃ (AXBIN_BODY T)` reduce definicionalmente **entero salvo
una hoja**: `substCodeT 3 W₃ T`. En vez de pelearse con `simp only` sobre `substCodeF`, se enuncia
el `have` **dejando esa hoja sin evaluar** —puro defeq, cero tácticas— y después **una sola línea**,
`rw [substCodeT_closed 3 W₃ T hT]`, la convierte en `termCode T`.

> **Receta**: cuando un parámetro bloquea la reducción **en una sola hoja**, enuncia el `have` con
> la hoja bloqueada y reescríbela luego. **No intentes normalizar el término entero.**

Es hermana de las ideas #2 y #3 de §3.27.4: en las tres, el ahorro viene de **no desplegar** lo que
no hace falta desplegar.

### 3.29.4 · `pcc_eval_substtc` — cerrado, **con guarda**, y el encargo estaba mal pedido

```lean
pcc_eval_substtc'  (w v s t) (h : Prf (isTC1 w t)) :
    Prf (provFromCode (eqc (substtcT v̇ ṡ ṫ) (tcFn (substtc v s t))))
pcc_eval_substtsc' (w v s t) (hwf : Prf (wfAll1 w)) (hargs : Prf (argsIn w t)) : …
pcc_eval_substtc_hasWit' (v s t) : Prf (hasWit t ⇒ targetSubsttc v s t)
```

⚠️ La forma **sin guarda** que pedía el encargo **no está probada, y no es probable por esta vía** —
ni ella ni su gemela `pcc_eval_liftc`. **El encargo estaba mal pedido, no el teorema mal probado**:
la inducción es sobre el **VALOR** del código (`prf_strong_induction`), así que para descender hace
falta que `t` sea de verdad un código de término, y eso es exactamente lo que dice `isTC1 w t`.

**Las dos obstrucciones de §3.28.4, resueltas:**
* **La tricotomía** sale por **or‑elim EXTERNO** (`Prf₀.j3`), no interno. Producción **sí** tiene
  or‑elim interno (`pcc_or_elim_code`, `Meta/PropCodePrf.lean:112`) pero **no hizo falta**.
* **El `pred` dotado**: `PredHyp` **declarada y descargada** (`predHyp`), vía
  `prf_lt_iff` → `prf_add_succ_t` → `ax26_pred_succ` dentro de `Prov`, **sin inducción**.

**Empalme**: `isTC1`, `wfAll1`, `argsIn`, `isTermCodeE1`, `shapeUn/Bin`, `consOk` son **idénticas**
a las de `DescensoLiftc.lean` (verificado def a def) ⇒ **el mismo testigo sirve para las dos
evaluaciones**, y los controles adversariales de aquel fichero valen tal cual.

### 3.29.5 · Lo que el paso adversarial cazó — y por qué el `PARCIAL`

El verificador de `substtc` no se fió del «los controles valen tal cual»: montó su **propio**
fichero de auditoría y compiló los testigos. Resultado: la matemática, **confirmada entera**
(no vacua sobre `termCodeM t` con `v`/`s` abstractos; guarda **refutable** con código de fórmula y
testigo abierto ⇒ no es un `⊥ ⇒ …`; siete controles negativos `fail_if_success`).

⛔ **Pero uno de los nueve hallazgos era FALSO**: `pcc_eq_tracked` **ya existe** en producción
(`Meta/Sigma1AtomPrf.lean:246`), con enunciado idéntico y ya consumido en
`Meta/InAxiomsCodePrf.lean:220`. La copia local lo **sombrea** — la trampa registrada de «misma
definición en dos namespaces». Actuar sobre el hallazgo («debería vivir al lado de
`pcc_lt_tracked`») habría creado una **tercera** copia. **Lo correcto es borrar la local.**
⇒ el `PARCIAL` es exacto: no degrada la prueba, y evita mandar trabajo a la basura.

### 3.29.6 · Piezas nuevas, y el arbitraje entre dos agentes

* ⚠️ **`pcc_axiom_inst4` NO existía**: producción llega sólo a `pcc_axiom_inst3`
  (`Meta/MpCodePrf.lean:243`) y los tres binarios son `forall_4`. **Dos agentes la escribieron por
  separado.** Es **candidata clara a promoción**: `ax_substfc_atom` y `ax_substfc_eq` también son
  `forall_4`, o sea que el frente la volverá a necesitar dos veces más.
* **`pred` dotado — dos versiones, y la comparación importa**: `EvalPredDot.lean` prueba
  `pcc_eval_pred (n)` **incondicional** para `n` abstracto (por inducción);
  `EvalSubsttc.lean` prueba `predHyp`, **guardada** por `lt v n`, sin inducción. El segundo agente
  declaró que el primero era «innecesario»: **es media verdad** — para *su* uso sí, pero la
  incondicional es **estrictamente más fuerte** y es la que vale la pena promover.
* **Piezas que resultaron innecesarias** (útil para no arrastrarlas): de las congruencias internas
  de `Paso2CasoForall` §4 sólo hace falta **`arg3`**; en los casos planos no interviene nada de
  §7‑§9, ni `succcT`, ni `unT`, ni `liftcT`, ni el kit de `liftfcT`/`liftscT`.

### 3.29.7 · ▶ Lo que queda

1. **El ENSAMBLAJE**: la inducción fuerte que junta los ocho casos en `pcc_eval_substfc`. Es lo que
   falta de verdad, y no está medido.
2. **La guarda sobre argumento ABSTRACTO** (§3.28.6): los 7 reflectores de `lineWF` la necesitarán,
   y hoy sólo se sabe descargar para códigos reales.
3. **Promoción a `Meta/`**: sigue sin pagarse (§3.28.5), y ahora con dos candidatas claras
   (`pcc_axiom_inst4`, `pcc_eval_pred`) y una limpieza pendiente (borrar la `pcc_eq_tracked` local).

---

## §3.30 · 🏁 EL MURO DE `substfc` ESTÁ ROTO — `pcc_eval_substfc` PROBADO (2026‑08‑31)

Cierra la rama A del árbol de la fase, y con ella el frente que llevaba abierto desde julio.
**Tres framings independientes, 1 CONFIRMADO + 2 PARCIAL** (los dos parciales con `medicionFiable`,
que era el veredicto correcto: midieron bien y no cerraron). Los tres compilan; recompilados por mí
desde su ubicación final. Build de producción intacto, **118 jobs**, **57 `sondeos/`**.

### 3.30.1 · El teorema

`sondeos/EvalSubstfcPrf.lean` (7 522 l.):

```lean
def hasWitF (c : Term) : Formula := ∃.∃. isFC1 #1 #0 ↑↑c

theorem pcc_eval_substfc (wF wT v s f : Term)
    (hws : Prf (hasWit s)) (hfc : Prf (isFC1 wF wT f)) :
    Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f))))

theorem pcc_eval_substfc_wit (v s f : Term) :
    Prf (Formula.impl (land (hasWit s) (hasWitF f)) (targetSubstfc v s f))
```

Las hipótesis son las **guardas** —testigo para el sustituyendo y para el código de fórmula—, no
obligaciones colgando: la misma forma que `pcc_eval_liftc` (§3.28) y `pcc_eval_substtc'` (§3.29).

**Footprint, reejecutado por el verificador y por mí**:
`pcc_eval_substfc`, `pcc_eval_substfc_wit` y `DESCENSO_substfc` →
`[propext, Classical.choice, Quot.sound, prf_axiomsCodeT_eq]` (la base sancionada, sin nada nuevo);
`hPHI`, `PHI_step`, las cuatro ramas y los cuatro controles de discriminación → **net‑0 puro**.

### 3.30.2 · 🔑 Las cuatro ideas — y ninguna era la prevista

1. **NO hacían falta tres sorts.** §3.29.7 anunciaba un `Φ` conjuntivo sobre fórmula + término +
   lista. **Falso**: la inducción de término/lista ya estaba cerrada aparte, así que la de
   **fórmula es de UN SOLO SORT** y consume las otras dos **como caja negra**. Los tags 4 (`eqc`) y
   3 (`atomc`) **no descienden por `substfc`**: descienden por `substtc`/`substtsc`.
2. **El puente de testigos NO se prueba: SE DISUELVE.** El encargo pedía medir «del testigo de
   FÓRMULA sale el de TÉRMINO para sus subcódigos». No hay que demostrarlo — hay que **DEFINIR** el
   reconocedor de modo que sus casillas de término apunten a `wT` con la forma **exacta** que
   consume `EvalSubsttc`:
   ```lean
   clEq   wT X := shapeBin X 4 ∧ In (nthc X 1̄) wT ∧ In (nthc X 2̄) wT
   clAtom wT X := shapeBin X 3 ∧ argsIn wT (nthc X 2̄)
   ```
   Con `wfAll1 wT` dentro de la guarda, la premisa de `DESCENSO_imp` sale por **`rfl`**
   (`bridge_isTC1`, net‑0). **Definir bien salió más barato que probar.**
3. **El gate fue gratis por una decisión tomada por otra razón.** El paquete de testigos ya venía
   **empaquetado en UN término** (`p`, con `acF/acT/acTs = carc, carc∘cdrc, cdrc∘cdrc`), cosa que
   `ParticionTresPredicados` decidió por naturalidad de `pcc_bdAll_intro`. ⇒ tres binders, y
   `FOL.substTerm_liftTerm`/`_liftLift`/`SubstArith.substTerm_liftLiftLift` bastan tal cual.
   *El empaquetado que impuso la mutualidad es lo que hace que el gate sea gratis.*
4. ⚠️ **«LA MONEDA DE LA INDUCCIÓN OBJETO» — lo caro de verdad, y se pagó tres veces.**

> Un lema de caso con la HI como hipótesis **META** (`Prf A → Prf C`) **no sirve**. La inducción
> objeto sólo puede consumir implicaciones **OBJETO** (`Prf (A ⇒ C)`) o versiones
> **Γ‑paramétricas** (`∀ Γ, PrfH Γ A → PrfH Γ C`), porque **la HI sólo existe dentro del `Γ` del
> paso**. Por eso los cuatro lemas de término/lista de `EvalSubsttc` valían tal cual y los cinco de
> fórmula no. **Regla: un lema de caso destinado a una inducción OBJETO se enuncia en forma
> Γ‑paramétrica desde el principio.** Conversión mecánica: `imp_of_ctx1`/`imp_of_ctx2`.

### 3.30.3 · Piezas que ya estaban y nadie había usado

* **`SinWTs.isFormCodeB2`** (`ClausuraLiftSinWTs.lean:1170`) — el reconocedor de código de fórmula
  con **DOS** listas testigo, con su discriminación ya probada (`crit_isFormCodeB2_rejects*`) y
  **sin un solo consumidor**. Sólo le faltaba la versión ecuacional (`isFormCodeE2`).
* **`SubstfcEx.lean` §MED** ya había medido que los tags 4 y 3 no descienden por `substfc`, y no se
  había recogido en ningún documento.

Es la tercera vez en esta semana que aparece trabajo hecho y no usado. La regla del grep sobre el
árbol **entero** (§3.28.6) sigue sin ser un lujo.

### 3.30.4 · ▶ Lo único que falta: el control de NO‑VACUIDAD

```lean
prf_hasWitF_real (φ : Formula) : Prf (hasWitF (formCodeM φ))
```

Sin él, el teorema es correcto pero **podría ser vacío**. ✅ **La mitad difícil ya está probada**:
la guarda **DISCRIMINA** y no es un colador — `CRIT_E2_rejects_varc`, `CRIT_E2_rejects_funcc`,
`CRIT_isFC1_rejects_varc`, vía `prf_isFormCodeE2_str` (la forma ecuacional **fortalece** la
posicional y hereda su discriminación de los 8 tags).
**Dos precedentes exactos** para transportar: `SinWTs.prf_isTC1_tcodes` (misma forma, sort término)
y `ParticionTresPredicados.prf_isFCB3_fcodes` (sort fórmula, predicado posicional de tres
testigos). **Los tres sondeos coinciden en señalar esta misma pieza como residuo**, lo que la
confirma.

### 3.30.5 · Los dos sondeos que no cerraron, y lo que aportan

No son fracasos: son **medición fiable**, y quedan archivados por eso.

| sondeo | qué aporta |
|---|---|
| `sondeos/EnsamblajeTriple.lean` (1 127 l.) | La ruta del `Φ` triple, que **también pasa el gate**. Su `structure CasesCtx` es el **censo Γ‑paramétrico** de los 10 casos, y `imp_of_ctx1`/`imp_of_ctx2` son la conversión mecánica de moneda. Reutilizables. |
| `sondeos/EnsamblajeMedida.lean` (1 503 l.) | El **inventario de acoples**: los tres puentes entre familias de predicados, el censo de guardas y el inventario de lifts. Es quien primero dijo «no hacen falta tres sorts». |

⚠️ **Trampa de notación nueva, cara y no registrada**: `FOL/FOL/FOL.lean:38` declara
`infixr:65 " ∨ " => Formula.or`, que **sombrea el `∨` de Lean** (precedencia 30). ⇒
`(k = 5 ∨ k = 7 ∨ k = 8)` es un **error de PARSEO** —agrupa `k = (5 ∨ k) = 7`— y **el mensaje no
menciona `∨`**. Escribir `Or (k = 5) (Or …)`.

---

## §3.31 · LA NO‑VACUIDAD, CERRADA — y **A4 resultó IMPOSIBLE** (2026‑08‑31)

Cierra el residuo que §3.30.4 declaraba como «lo único que falta». **Tres rutas independientes,
3 CONFIRMADAS**, todas con `noVacuo=true`. Recompiladas por mí desde su ubicación final.

### 3.31.1 · El teorema

`sondeos/HasWitFReal.lean`:

```lean
def fcodesF : Formula → List Term   -- subcódigos de FÓRMULA de φ
def tcodesF : Formula → List Term   -- subcódigos de TÉRMINO de φ (vía SinWTs.tcodes1/tcodes1s)

theorem prf_isFC1_real   (φ : Formula) :
    Prf (ENS.isFC1 (objList (fcodesF φ)) (objList (tcodesF φ)) (formCodeM φ))
theorem prf_hasWitF_real (φ : Formula) : Prf (ENS.hasWitF (formCodeM φ))
```

🔑 **Footprint `[propext, Classical.choice, Quot.sound]` — net‑0 PURO**, ni siquiera arrastra
`prf_axiomsCodeT_eq`. Los enunciados hablan de las constantes **reales** `ENS.isFC1`/`ENS.hasWitF`
—no de copias homónimas—, verificado con puentes `rfl` net‑0.

⇒ **`pcc_eval_substfc` deja de ser condicional para códigos reales**: `pcc_eval_substfc_wit_REAL`
da la ecuación **pelada**, sin guardas, para toda `φ` y todo término `t`.

### 3.31.2 · ⛔ A4 no es trabajo pendiente: **es imposible tal como estaba enunciado**

§3.30 y el árbol de tareas listaban como A4 «la guarda sobre argumento **ABSTRACTO**». Hay que
retirarlo:

> **`hasWitF` sobre argumento abstracto es FALSO en general**, y ya estaba refutado en el propio
> fichero del ensamblaje: **`ENS.CRIT_isFC1_rejects_varc`** refuta `isFC1 wF wT (varc n)` **para
> CUALQUIER testigo**. No es que falte probarlo: **no se puede**.

⇒ **La vía real para los 7 reflectores es CARGAR la guarda como hipótesis OBJETO a lo largo de la
cadena y descargarla al final**, donde el argumento sí es un código real. Eso replantea cómo se
ataca la rama C, y conviene saberlo **antes** de empezarla.

Es, en pequeño, la misma lección que §3.28.6: **una obligación que parece pendiente puede ser una
obligación mal enunciada.** Aquí la refutación ya estaba compilada en el árbol desde el día
anterior, escrita como control de discriminación, y nadie la leyó como lo que también era: la
prueba de que A4 no existe.

### 3.31.3 · ▶ La obligación NUEVA, ésta sí real

```lean
Prf (ENS.hasWitF c ⇒ ENS.hasWitF (liftc zero c))     -- NO existe
```
La propagación de la guarda bajo el `liftc` **OBJETO**. El análogo del sort TÉRMINO sí existe
(`SinWTs.CRIT_hasWit_lift`) y el molde debería transportarse — `ENS.liftF_isFC1` ya está y la
estructura es la misma con **dos** binders en vez de uno.
⚠️ **`ENS.liftF_hasWitF` NO sirve**: es sólo el lift **De Bruijn**, no el objeto. Son cosas
distintas con nombres parecidos.

### 3.31.4 · 🧱 El footprint mínimo, medido — lo más accionable para la rama B

La no‑vacuidad **no necesita nada** del descenso, ni `Paso2`, ni `SFsubsttc`, ni `DescMutua`, ni el
ensamblaje. Le bastan tres bloques:

| bloque | qué es |
|---|---|
| `S_Clausura` (namespace `SinWTs`) | `EvalSubstfcPrf.lean:11‑1241` |
| el bloque **definicional** `ENS` §1‑§2 | `:5953‑6228` |
| `def hasWitF` (+ `liftF_hasWitF`) | `:8243‑8244`, `:8320‑8324` |

Verificado **ejecutándolo**: `sondeos/HasWitFRealMin.lean`, **1 819 líneas, EXIT=0, mismo net‑0**.
⇒ **promover la no‑vacuidad a `Meta/` es un módulo pequeño e independiente**, no las ~20 000 líneas
del frente entero. Es el primer trozo de la rama B que se puede pagar barato.

### 3.31.5 · Medidas de coste que corrigen la estimación previa

* **La ruta que se encargó NO hizo falta.** El encargo decía «copia §19 de
  `ParticionTresPredicados` (~650 l.) y reescríbelo». **No se abrió §19 ni una vez**: fue
  re‑derivación desde el precedente del sort TÉRMINO más un molde ya existente. Coste real
  **~590 líneas**.
* **El precedente del sort TÉRMINO se reutiliza ENTERO y sin tocar.** `SinWTs.okE1_T`/`okE1_Ts`
  valen byte a byte porque `tcodesF` se definió a base de `tcodes1`/`tcodes1s`. El eje TÉRMINO
  costó **cero líneas de invención**: `okT_F` son 20 líneas de fontanería de `List.mem_append`.
* **«La tercera lista se absorbe en `argsIn`»: confirmado, y cuesta 8 líneas.** `flcodes`/`WTs` no
  aparecen en ningún sitio.
* **El eje ECUACIONAL, medido**: **TRES** lemas de forma cubren **los OCHO tags**
  (`prf_shapeNul_real` 1 l., `_shapeUn_real` 3 l., `_shapeBin_real` 5 l.), y `cl_bin_real`/
  `cl_un_real` salen **genéricos en el tag `k`** ⇒ los tags 5/7/8 comparten un lema y 6/9 otro, y
  los 8 nodos suman **~55 líneas**. La predicción «en forma ecuacional cada nodo cuesta menos»
  **se quedó corta**: cuesta menos **y se factoriza**.

### 3.31.6 · ⚠️ Cuarta vez: trabajo hecho y no recogido — ahora en `Probe/`

`Probe/ADV_novacuo.lean` (**7 668 l.**, de una tanda anterior de esa misma noche) ya contenía
`PROBE_wfAllF_of_list`, el molde general del `∀` acotado que hacía falta, ya medido. Se copió
literal.

La regla registrada decía «grepea el árbol de **producción** entero». **Es insuficiente**: hay que
extenderla a **`sondeos/` y `Probe/`**. El censo de las cuatro veces está en el nodo de memoria
[[feedback-auditoria-footprint]] §6.

---

## §3.32 · DOS MEDICIONES, Y DOS DOCUMENTOS DE ESTE ÁRBOL QUE ERAN FALSOS (2026‑08‑31)

Dos frentes medidos en paralelo, **3 de 3 CONFIRMADOS cada uno**, seis ficheros en `sondeos/`,
recompilados por mí. Ninguno tocó el árbol (`git status` limpio en todo momento). Y los dos
terminan corrigiendo un documento del proyecto.

### 3.32.1 · ⛔ **§3.27.1 ERA FALSO: enmendar un `ax_lineWF_*` NO cambia la sentencia G**

Este documento viene repitiendo —§3.27.1, y con él parte del razonamiento de ADR‑015— que
axiomatizar «no es más caro: es **otro teorema**», porque un axioma nuevo entraría en `axioms`,
`ax_axiomsCodeT_eq` lo metería en `axiomsCodeT`, cambiaría `provCodeC'` y **cambiaría G**.

Medido sobre el `Environment` de Lean, no por grep ni por lectura:

```
godelCN: 483 dependencias transitivas
¿depende de  axioms / ax_lineWF_q1 / coreAxioms / codingAxioms ?  ->  NINGUNA
```

**Razón estructural, y comprobable**: `axiomsCodeT := Term.func "axiomsCodeT" []`,
`lineWF l := Formula.atom "lineWF" [l]`, `chainOk c p := Formula.atom "chainOk" [c,p]` y `runFn`
son **átomos OPACOS**. `provFormulaC' = ∃p. chainOk nil p ∧ In #1 (runFn nil p)` los menciona
**sólo por su nombre**, y `godelBeta'`/`godelPred'`/`diagTerm`/`selfAppN` se construyen encima.
⇒ **la sentencia G, como fórmula, no depende de `axioms`.**

⚠️ **El matiz, y es el que importa**: G es **literalmente la misma fórmula**, pero pasa a hablar de
una **teoría distinta**. Lo que cambia no es el enunciado sino **qué demuestra `Prov`**. Si eso
afecta a la afirmación matemática es decisión del autor — pero **el argumento de coste que se venía
usando para descartar la enmienda es incorrecto y hay que dejar de repetirlo.**

### 3.32.2 · La rama C: las tres vías medidas, y dos REFUTADAS

`sondeos/MedirC_Deriva.lean` · `MedirC_Carga.lean` · `MedirC_Enmienda.lean`.

**(A) ¿sale la guarda del antecedente `lineWF t`? ⛔ REFUTADA** — y no «no conseguida». Se
construyó una **línea basura** que satisface `lineWF` (usando el `prf_lineWF_q1` de **producción**),
con tag 9, `lenc = 4̄`, que cumple **la condición estructural entera** del esquema, y cuya casilla 2
es un **código de VARIABLE**:

```lean
MEDIDA_A_REFUTADA_con_TODO_el_antecedente_de_hcond
  (hA : ∀ t, Prf (lineWF t ⇒ (lenc t ≐ 4̄) ⇒ substFormula 0 t condQ1 ⇒ hasWitF (nthc t 2̄)))
  : Prf ⊥
```

🔑 **La causa es de una limpieza brutal, y está compilada**: `condQ1_es_UNA_ecuacion_atomica` —
**la condición entera del tag 9 es UNA sola ecuación de `carc`**. No menciona bien‑formación en
ningún sitio, y `ax_lineWF_inv` sólo habla de la **etiqueta**. La otra mitad tampoco baja: segunda
línea basura con un código de **fórmula** en la ranura de **término**.

**(B) ¿cargar la guarda por la cadena? ⛔ REFUTADA, y por una razón peor de la temida.** Sube hasta
`pcc_lineWF_tracked` y hasta **D3** (compilado con el `d3_prf_of_chainOkDot` **real** de
producción). Pero el problema no es ése:

```lean
M5_LA_GUARDA_COLGANTE_IMPLICA_BOT : Prf GUARDA_COLGANTE → Prf ⊥
```

⇒ la D3 que saldría sería **VACUA**, no sólo condicionada.
✅ Lo que **sí** sobrevive, y es la buena noticia: **ni el chasis ni el ensamblador hay que
rehacerlos** — el ensamblador con guarda ya está escrito (25 líneas).

**(C) enmendar el esquema — la ÚNICA que puede funcionar.** ⚠️ Pero **es circular** tal cual: rompe
el chasis que la consume, porque éste pide reflejar todo el lado derecho del `⇔`. Hay que pagar
antes un lema previo, **`∀t. hasWit (tcFn t)`**. Y es la vía que `hcond_absorbe_extra`
(`sondeos/SegundoMuro.lean`) sabe abaratar, porque lo que absorbe es un **conjunto extra en `C`** —
o sea, exactamente una enmienda de esquema. Aquella pieza se probó para esto y no se sabía.

### 3.32.3 · El frente F: su plan declara imposible algo que existe desde julio

`sondeos/MedirF_Opaco.lean` · `MedirF_Censo.lean` · `MedirF_Replan.lean`.

`PLAN-NEGVERIFIER.md` §B dice que **`NegVerifier` NO es demostrable** por la opacidad de
`axiomsCodeT`. **Es falso**, y las piezas llevan compiladas **y enchufadas** desde julio:

```lean
-- Meta/AxiomListCode.lean:70
neg_In_axiomsCodeT (φ) (hnp : ¬ Prf φ) : axioms ⊢ neg (In (formCode φ) axiomsCodeT)
-- Meta/LineWFCases.lean:223  — el consumidor, ya alimentado
derives_lineWF_neg_thy_of_not_prf (φ) (hnp) : axioms ⊢ neg (lineWF ⟨formCode φ, 15̄⟩)
```

🔑 **Las fechas lo explican** (comprobadas en git): el plan es del **2026‑07‑13**,
`Meta/AxiomListCode.lean` del **2026‑07‑14**. **El módulo se escribió al día siguiente del plan que
lo declara imposible**, y el propio plan marca ✅ su paso 0.5 («concretar `axiomsCodeT`») **sin
reescribir la conclusión de §B que ese paso invalidaba**. El documento se contradice a sí mismo.

**Estimación revisada, medida contra el árbol**: de **1 900‑2 700 líneas / 8‑11 sesiones** a
**~800‑1 300 líneas / 3,5‑5 sesiones**. Ya están entregadas ~1 160 líneas del presupuesto, que el
plan estimaba en 650‑900. **La opacidad es hoy el 0 % del coste restante.**

**El censo de los 21 tags**: el caso 4 (aridad) es **gratis para 21/21**, el caso 3 cae por la
cabeza de `carc` en **19/21**, y el único hueco real lo tapa un sustituto de `canon_ne` de
**~45 líneas net‑0**.

⚠️ **Y el cuello de botella real de F NO es `axiomsCodeT`: es la rama B.** Los casos 3 y 4 necesitan
`codeNat_ne`/`codeNatTerm_ne`, que **sólo viven en `sondeos/CodeNatInj.lean`**, fuera del build.
⇒ la promoción a `Meta/` bloquea **también** a F.

⛔ **Y una recomendación del plan que NO hay que ejecutar**: su §0.5 propone añadir un `axiom`
(`ax_notInAxC`). Se tomó la opción net‑0 y **la dirección negativa es hoy un teorema**; ejecutarla
añadiría un axioma innecesario a un inventario que sigue en **7**.

### 3.32.4 · Piezas del frente que faltan en producción (para la rama B)

Detectadas al reconstruirlas a mano durante las mediciones: `prf_isFormCodeE2_str`,
`CRIT_E2_rejects_varc`, `CRIT_isFC1_rejects_varc` — el kit de **discriminación** — y
**`prf_congr_carc`**, que no existe (sólo `prf_congr_carcT`, la de código).

---

← Índice raíz: [REFERENCE.md](../REFERENCE.md) · Ramas: [Gödelización](REFERENCE-Godelization.md) · [Núcleo](REFERENCE-Kernel.md) · [Full](REFERENCE-Full.md) · [Aritmética](REFERENCE-Arithmetic.md)
