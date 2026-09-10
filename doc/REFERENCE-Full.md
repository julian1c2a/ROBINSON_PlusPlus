# REFERENCE — Sistema `Full/` · inducción general, representabilidad, TFA · ROBINSON_PlusPlus

> **Nodo temático** del sistema REFERENCE (árbol; ver `AI-GUIDE.md` §0.5).
> Índice raíz: [REFERENCE.md](../REFERENCE.md).
> **Nodos relacionados:** [Núcleo](REFERENCE-Kernel.md) (axiomas), [Aritmética](REFERENCE-Arithmetic.md)
> (bloques que estos teoremas derivan/generalizan), [Incompletitud](REFERENCE-Incompleteness.md)
> (`numeral` + `ax_induction` alimentan el verificador y la regla `ind`).
> **Ficheros `.lean`:** `ROBINSON_PlusPlus/Full/*.lean` (ver [directorio](../ROBINSON_PlusPlus/Full/)).

**Contenido:** inducción general a nivel objeto (`ax_induction`/`inductionFormula`), inducción fuerte
derivada, puente `numeral` + homomorfismo, acotados, divisibilidad/división, primos y **TFA completo**
(`tfa_numeral`). **Last updated:** 2026-09-10h · Lean v4.31.0.

---

## Descripción de módulos

### 3.14 `Full/` — Inducción general, representabilidad y TFA (Eje 4)

**Namespace**: `ROBINSON_PlusPlus.Full`
**Status**: ✅ Fragmento aritmético + listas de Minimal derivado; **TFA completo**
**@importance**: `high`
**@axiom_system**: `Full` (inducción general como axioma object-level + meta-axiomas)
**Last updated**: 2026-06-12
**Módulos** (11): `Induction`, `Mod2`, `Lists`, `StrongInduction`, `Numerals`, `Bounded`, `Divisibility`, `Division`, `PrimeFactor`, `Primality`, `Factorization`.

> **Nota histórica**: `Intermediate/Induction.lean` (prototipo de inducción meta, Eje 3) fue **eliminado 2026-06-11**: el sistema con Φ finito es el caso particular de Full con inducción general, sin valor técnico añadido. Toda la inducción vive en `Full/`.

#### `Full/Induction.lean` — inducción general object-level

```lean
def inductionFormula (φ : Formula) : Formula                 -- φ(0) ⇒ ((∀n φ(n)⇒φ(σn)) ⇒ ∀n φ(n))
axiom ax_induction (φ : Formula) : axioms ⊢ inductionFormula φ
theorem induction_object {φ} (base step) : axioms ⊢ Formula.forall φ
-- Composición De Bruijn lift-aware (caso multivariable):
theorem substFormula_succ_lift_gen / step_reduce …
-- Axiomas de Minimal derivados como TEOREMAS:
theorem add_comm_thm : axioms ⊢ ax6_add_comm        -- ax6 ;  add_assoc_ax (ax7)
theorem mul_comm_thm : axioms ⊢ ax10_mul_comm       -- ax10 ; mul_assoc_ax (ax11), mul_distrib_ax (ax12)
theorem lt_irrefl_thm : axioms ⊢ ax18_lt_irrefl     -- ax18 ; lt_trichotomy_thm (ax19)
-- + lemas de orden: lt_succ_self, not_lt_zero, lt_succ_of_lt, zero_lt_succ, zero_or_succ_ax, lt_succ_cases
```

#### `Full/Mod2.lean` — ax21, ax24 (Opción C.2)

```lean
axiom ax_mod2_alternation : axioms ⊢ ∀. (add (mod2 (σ #0)) (mod2 #0) =eq one)  -- caracteriza mod2
theorem mod2_range_thm   : axioms ⊢ ax21_mod2_range      -- ax21 (inducción + alternancia)
theorem mod2_of_even_thm : axioms ⊢ ax24_mod2_of_even    -- ax24
```

Hallazgo: `ax16`+`ax17` dejan `mod2` subdeterminado (modelos con `mod2(σn)≥2`); `ax_mod2_alternation` lo cierra. Conservativo respecto a Minimal.

#### `Full/Lists.lean` — ax_C3, ax_L3 (inducción estructural sobre listas)

```lean
axiom ax_list_induction (φ : Term → Formula) (base : Γ ⊢ φ nil)
    (step : ∀ h t, Γ ⊢ φ t → Γ ⊢ φ (cons h t)) : ∀ L, Γ ⊢ φ L     -- meta-axioma
theorem concat_assoc_thm : axioms ⊢ ax_C3_concat_assoc   -- ax_C3
theorem in_concat_thm    : axioms ⊢ ax_L3_in_concat      -- ax_L3
```

#### Capa de representabilidad (camino Gödel-aware a TFA)

Reencuadre 2026-06-11: en vez del slog object-level De Bruijn, se trabaja sobre **numerales** (`numeral n = σⁿ(0)`) con cómputo meta en ℕ + transferencia por homomorfismo. Disuelve los "Muros" (FOL= no da testigos meta ni case-split meta).

```lean
-- Full/StrongInduction.lean — inducción fuerte DERIVADA de ax_induction (sin axioma nuevo)
theorem substFormula_liftFormula (φ c s) : substFormula c s (liftFormula c φ) = φ
theorem lt_succ_split (m n) : axioms ⊢ lt m (σ n) → axioms ⊢ lor (lt m n) (m =eq n)
theorem strong_induction (φ : Formula) (step) : ∀ n, axioms ⊢ substFormula 0 n φ
-- Full/Numerals.lean — puente meta↔object
def numeral : Nat → Term                                       -- n ↦ σⁿ(0)
theorem numeral_add / numeral_mul / numeral_pow                -- homomorfismo +, ·, ^
theorem numeral_lt {a b} (h : a < b) : axioms ⊢ lt (numeral a) (numeral b)
theorem numeral_ne {a b} (h : a ≠ b) : axioms ⊢ neg (numeral a =eq numeral b)
-- Full/Bounded.lean — cuantificación acotada → casos finitos
theorem le_numeral_split (d C) : ∀ n, axioms ⊢ le d (numeral n) →
    (∀ i, Nat.le i n → axioms ⊢ (d =eq numeral i) → axioms ⊢ C) → axioms ⊢ C
-- Full/Divisibility.lean
theorem numeral_dvd {a b} (h : a ∣ b) : Dvd (numeral a) (numeral b)
theorem divisor_le (d q n) : axioms ⊢ (mul d q =eq n) → axioms ⊢ lt zero n → axioms ⊢ le d n
-- Full/Division.lean
theorem division_numeral (n d) (hd : 0 < d) :
    (axioms ⊢ numeral n =eq add (mul (numeral (n/d)) (numeral d)) (numeral (n%d)))
    ∧ (axioms ⊢ lt (numeral (n%d)) (numeral d))
-- Full/Primality.lean
theorem isPrime_numeral (p) (hp2 : 2 ≤ p) (hpd : ∀ a, a∣p → a=1∨a=p) : IsPrime (numeral p)
```

#### `Full/PrimeFactor.lean` — teoría de números META (ℕ pura, sin Mathlib) + TFA

```lean
def IsPrimeNat (p) : Prop := 2 ≤ p ∧ ∀ a, a∣p → a=1 ∨ a=p
def natProd : List Nat → Nat
theorem exists_prime_factor (n) (hn : 2 ≤ n) : ∃ p, IsPrimeNat p ∧ p ∣ n      -- inducción fuerte
theorem primeFactorList (n) (hn : 1 ≤ n) : ∃ ps, (∀ p∈ps, IsPrimeNat p) ∧ natProd ps = n
-- Euclides + UNICIDAD (vía Nat.Coprime.dvd_of_dvd_mul, List.perm_cons_erase):
theorem euclid (hp : IsPrimeNat p) : p ∣ a*b → p∣a ∨ p∣b
theorem count_unique / factorization_perm_unique : dos factorizaciones del mismo n son permutaciones
```

#### `Full/Factorization.lean` — TFA transferido al object

```lean
def toTerm : List Nat → Term                                   -- lista de pares (numeral p, one)
theorem prod_pairs_toTerm (ps) : axioms ⊢ (prod_pairs (toTerm ps) =eq numeral (natProd ps))
theorem tfa_numeral (n) (hn : 1 ≤ n) : ∃ ps, (∀ p∈ps, IsPrimeNat p)
    ∧ (axioms ⊢ prod_pairs (toTerm ps) =eq numeral n)                   -- EXISTENCIA (object)
    ∧ (∀ qs, (∀ q∈qs, IsPrimeNat q) → natProd qs = n → ps.Perm qs)      -- UNICIDAD (ℕ)
```

**TFA completo** (existencia object ∧ unicidad ℕ), autocontenido sin Mathlib/Peano. El `ax_p_tfa` de Block8 queda como forma *idealizada* (membership object + testigo object, no discharge constructivo por el "Muro 1"); `tfa_numeral` es la realización equivalente para todos los usos reales.

**Axiomas extra de Full**: `ax_induction`, `ax_mod2_alternation`, `ax_list_induction`. **Estado del fragmento de Minimal en Full**: ax6/7/10–12, ax18/19, ax21/24, ax_C3/L3 ✅ + TFA ✅.

---

### 3.14.1 · ⭐ EL CENSO DE `coreAxioms` — qué es PRIMITIVO y qué es TEOREMA (2026‑09‑10h)

> **El planteamiento correcto es éste**: *en `Full` deberían demostrarse como teoremas todos los
> axiomas de `Minimal` **que no sean definitorios**.* No «todos»: una ecuación que **define** un
> símbolo de función no la deriva ningún esquema de inducción — sin ella el símbolo no significa
> nada. El censo separa las dos clases y **mide** cuántos quedan.

`Minimal` tiene `axioms = coreAxioms ++ codingAxioms` (`axioms_eq`, por `rfl`), medido con
`#eval ·.length`: **34 + 107 = 141**.

#### (a) Los **107** `codingAxioms` — **extensión definicional, irreducibles por diseño**

Las ecuaciones recursivas de `substtc`/`substtsc`/`liftc`/`liftsc`/`substfc`/`liftfc`, las 22
cláusulas `ax_vpf_*` del verificador, `ax_tc_zero`/`ax_tc_succ`, `ax_carc`/`ax_cdrc`. **Definen**
los símbolos aritmetizados; no son enunciados matemáticos que la inducción pueda alcanzar. ⇒ fuera
del censo.

#### (b) Los **34** `coreAxioms`, partidos en dos

| clase | cuántos | cuáles | por qué |
|---|---|---|---|
| **PRIMITIVOS / DEFINITORIOS** | **23** | ax2, ax3 (Peano) · ax4, ax5 (definen `+`) · ax8, ax9 (definen `·`) · ax13 (define `<`) · ax14, ax15 (caracterizan `√`) · ax16, ax17 (caracterizan `mod2`/`div2`) · ax25, ax26 (definen `pred`) · ax_L0, ax_L1, ax_L2 (definen `cons`/`In`) · ax_C1, ax_C2 (definen `concat`) · ax29 (caracteriza la resta truncada) · ax_pow_zero, ax_pow_succ · ax_prodp_nil, ax_prodp_cons | **irreducibles**: fijan el significado de un símbolo. Nada que derivar |
| **DERIVABLES CON INDUCCIÓN** | **11** | ax6, ax7, ax10, ax11, ax12, ax18, ax19, ax21, ax24, ax_C3, ax_L3 | consecuencias de las ecuaciones definitorias **+ inducción** ⇒ **deben ser teoremas en `Full`** |

#### (c) 🏁 **Estado: 11 de 11.** Y los tres últimos cayeron hoy

| axioma | teorema en `Full` | fichero |
|---|---|---|
| ax6 `add_comm` | `add_comm_thm` | `Full/Induction.lean` |
| **ax7 `add_assoc`** | 🆕 **`add_assoc_thm`** | `Full/Induction.lean` |
| ax10 `mul_comm` | `mul_comm_thm` | `Full/Induction.lean` |
| **ax11 `mul_assoc`** | 🆕 **`mul_assoc_thm`** | `Full/Induction.lean` |
| **ax12 `mul_distrib`** | 🆕 **`mul_distrib_thm`** | `Full/Induction.lean` |
| ax18 `lt_irrefl` | `lt_irrefl_thm` | `Full/Induction.lean` |
| ax19 `lt_trichotomy` | `lt_trichotomy_thm` | `Full/Induction.lean` |
| ax21 `mod2_range` | `mod2_range_thm` | `Full/Mod2.lean` |
| ax24 `mod2_of_even` | `mod2_of_even_thm` | `Full/Mod2.lean` |
| ax_C3 `concat_assoc` | `concat_assoc_thm` | `Full/Lists.lean` |
| ax_L3 `in_concat` | `in_concat_thm` | `Full/Lists.lean` |

⭐ **La «obstrucción» de ax7/ax11/ax12 era FALSA.** `Full/Induction.lean` llevaba una NOTA —tres
sesiones— diciendo que el empaquetado `∀³` vía `gen` triple «topa con el ajuste de niveles
`liftTerm`» y que hacía falta un «helper de empaquetado n‑ario». **No hacía falta ninguno**: tras
los dos `gen`, el hueco del parámetro exterior es
`substTerm (0+1) ṡ (liftTerm 0 (liftTerm 0 a))`, y eso **ya tenía lema desde siempre** —
**`FOL.substTerm_liftLift`** (`FOL/Theorems/Eq.lean`)—, que devuelve exactamente `liftTerm 0 a`,
que es lo que `add_assoc_ax a b` produce. Era **un lema ausente del `simp set`**: cuatro líneas
por axioma. Es otra vez [[feedback-medir-la-forma]]: *una obstrucción medida pero no probada puede
simplemente ser falsa*.

⚠️ **Y la trampa del camino, que merece quedar escrita**: el primer intento metió en el `simp set`
un lema propio dejado en `sorry` «para medir» —
`substTerm (c+1) s (liftTerm 0 (liftTerm 0 t)) = liftTerm 0 (liftTerm 0 t)`. Los **tres**
empaquetados compilaron con él, y el lema es **FALSO** (la sustitución en `c+1` sí baja un nivel).
**Un `sorry` en el `simp set` no mide: fabrica el verde.** Cf. AI‑GUIDE §27.1.

#### (d) ⛔ LO QUE EL CENSO **NO** CIERRA — y es lo sustantivo

Los once teoremas se enuncian **`axioms ⊢ axN`**, y `axN ∈ axioms`. ⇒ el enunciado es
**trivialmente cierto por `ax`**: el tipo **no certifica** la redundancia, sólo la prueba lo hace.
Medido (grep sobre `Full/`): **ninguna de las once pruebas cita su propio axioma** — pero **nada lo
impide**, y una edición futura podría cortocircuitar cualquiera sin que nada rompa.

**La forma que sí certifica** sería partir la lista:

```lean
def primAxioms : List Formula := [ … los 23 … ]          -- ⬜ no existe
theorem add_comm_thm : primAxioms ⊢ ax6_add_comm := …    -- ⬜ el enunciado que certifica
```

⚠️⚠️ **CORRECCIÓN (misma sesión, [ADR‑023](../DECISIONS.md)).** Aquí se escribió que certificarlo
*«mueve la frontera de la teoría»*. **Confunde dos cosas, y sólo una es cierta:**

| | qué se hace | ¿mueve la frontera? |
|---|---|---|
| **(A) CERTIFICAR** | añadir `primAxioms ⊆ axioms` y probar `primAxioms ⊢ axN` | ⛔ **NO.** `axioms` queda intacta ⇒ `axiomsCodeT`, `provCodeC'` y `G` no se enteran |
| **(B) ESTRECHAR** | **quitar** los 11 de `axioms` | ✅ SÍ — y por eso **no se hace** |

⇒ **(A) está decidida y parcialmente ejecutada.** ⭐ Y sale barata por dos hallazgos:
**`Derives.weakening` es un CONSTRUCTOR** de `Derives` (el puente es una línea, ninguna firma aguas
abajo cambia), y **ninguna de las 46 citaciones `∈ axioms`** de `Full/{Induction,Mod2,Lists}.lean`
cita uno de los 11 derivables ⇒ **no hay circularidad**, la migración es mecánica.

🏁 **Hecho hoy**: `primAxioms` (los 23) + `primAxioms_subset` + `prim_to_axioms` + `axp`
(`Full/Induction.lean` §0bis), y **`concat_assoc_prim`/`in_concat_prim`** — ax_C3 y ax_L3
**certificados**, con **cero cambios de axioma**, porque `ax_list_induction` ya era genérico en `Γ`.

⬜ **Los otros 9** pasan por `ax_induction`, que está especializado a `axioms`. ⛔ Y la salida fácil
está cerrada: `∀ {Γ}, Γ ⊢ inductionFormula φ` sería **FALSO** (con `Γ = []` haría la inducción
lógicamente válida). Un axioma **tiene que nombrar su contexto** ⇒ hay que **mover** `ax_induction`
a `primAxioms ⊢ …` y recuperar el de hoy por debilitamiento — **sanción del propietario** (M‑1).
Detalle y forma exacta en ADR‑023.


---


---

← Índice raíz: [REFERENCE.md](../REFERENCE.md) · Ramas: [Núcleo](REFERENCE-Kernel.md) · [Aritmética](REFERENCE-Arithmetic.md)
