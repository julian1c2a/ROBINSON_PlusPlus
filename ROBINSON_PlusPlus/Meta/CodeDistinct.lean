/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CodeArith
import ROBINSON_PlusPlus.Meta.Provability

import FOL.FOL
import FOL.Theorems.Eq
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Deduction
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Quantifiers
import ROBINSON_PlusPlus.Minimal.Axioms

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`. Los nombres de esa capa que cite el texto de abajo
> (`cons_ne_head`, `cons_ne_tail`, `neg_symm`, `formCode_ne`…) **ya no existen**: lo que se lea sobre ellos es REGISTRO, no estado.
> Lo que queda en el módulo no depende de `⊢`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CodeArith

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.CodeDistinct

/-!
## META — NIVEL D (real): aritmética NEGATIVA de códigos  (Fase 2.6, cimientos)

La dirección negativa (reflexión / D3 / `⊬¬G`) reposa sobre que la teoría
**refuta** igualdades de códigos distintos: la contraparte object-level de
`formCode_injective`. Aquí se construían los primitivos de distinción
(`cons_ne_head`/`cons_ne_tail`/`neg_symm`) y, sobre ellos, `formCode_ne`
(refutación de igualdad de códigos de fórmulas distintas) por inducción meta; todo
sobre `⊢`, y retirado con esa capa (ADR‑115).

**⚠️ CORRECCIÓN 2026‑07‑13 (auditoría).** Aquí se decía que el resultado «titular»
`⊢ ¬provCodeC φ` para `φ` indemostrable (Π₁, `∀p. ¬In ⌜φ⌝ (…)`) se obtendría con
el **esquema de inducción** (Fase 5). **Ese plan es IMPOSIBLE**: para `φ = ⊥`
—indemostrable si la teoría es consistente— `⊢ ¬provCodeC ⊥` es **literalmente
`Con(T)`**, que por **Gödel II** la teoría NO demuestra. (Para `φ = G` tampoco: por
el punto fijo, `⊢ ¬provCodeC' G` ⟺ `⊢ G`, y `⊬ G`.) La vía «la teoría refuta la
demostrabilidad» está **cerrada por Gödel**, no por falta de trabajo.

**Alcance honesto (real).** Este módulo es el cimiento aritmético de la dirección
negativa, pero ésta **sólo puede cerrarse a nivel META**: la **reflexión**
(`(axioms ⊢ provCodeC' φ) → Prf φ`) es una hipótesis meta —la ω‑consistencia
clásica— y así se enunciaba, **explícita**, en `Meta/DiagonalTwo.lean`
(`Reflects` / `goedel_first_undecidable_real'`). Descargarla exige ω‑consistencia
**+ Δ₀‑completitud NEGATIVA del verificador en testigos CONCRETOS** (cerrados) —
el espejo de `repr_pos'`, y sí alcanzable, a diferencia de la versión Π₁ universal.
`formCode_ne` es la base de eso.
🗑️ `Reflects`, `repr_pos'` y `formCode_ne` eran de `⊢`: retirados con esa capa (ADR‑115). Hoy la
mitad `⊬¬G` no tiene enunciado sobre `Prf`.
-/


/-! ### `formCode_ne`: la teoría refuta igualdad de códigos de fórmulas distintas

🗑️ Era de `⊢`: `formCode_ne` y sus primitivos, retirados con esa capa (ADR‑115). Queda `charToNat_ne`,
de Lean puro. -/

/-- Inyectividad de `Char.toNat` (vía `Char.ofNat_toNat`). -/
theorem charToNat_ne {c c' : Char} (h : c ≠ c') : c.toNat ≠ c'.toNat := by
  intro he
  apply h
  have key : Char.ofNat c.toNat = Char.ofNat c'.toNat := by rw [he]
  rwa [Char.ofNat_toNat, Char.ofNat_toNat] at key





/-! ### 🏁 Códigos de FÓRMULA contra códigos de TÉRMINO — la causa (f) de `DEUDA_chainNeg`

⭐⭐ `StdArgs` (`Meta/OmegaReflect.lean`) sólo exige que cada argumento sea `formCode _`
**o** `termCode _`, **sin decir cuál**. Por eso una línea estándar puede llevar un código de
término donde el tag espera uno de fórmula, y entonces `decodeForm` falla: ésa es la **sexta**
causa de rechazo del decodificador (ADR‑075).

⭐ Lo que la cierra es puro **álgebra de códigos**, y se apoya en un hecho de una línea: los tags
de cabeza son **disjuntos** — `termCode` usa 0/1 y `formCode` usa 2…9.

🔑 *La mitad cara aparente —«¿y si el tag SÍ coincide?»— sólo ocurre en un constructor por lema,
y ahí se desciende una capa y se vuelve al mismo hecho de una línea.*

🗑️ Los refutadores que la cerraban eran de `⊢` y se retiraron con esa capa (ADR‑115). Aquí quedan
los tags (`formTag`, `termTag`) y sus `_eq_cons`. -/

/-- El TAG de cabeza del código de una fórmula. -/
def formTag : Formula → Nat
  | .bottom => 2 | .atom _ _ => 3 | .eq _ _ => 4 | .impl _ _ => 5
  | Formula.forall _ => 6 | .and _ _ => 7 | .or _ _ => 8 | .ex _ => 9

theorem formCode_eq_cons (f : Formula) : ∃ r, formCode f = cons (numeral (formTag f)) r := by
  cases f <;> exact ⟨_, rfl⟩


/-- El TAG de cabeza del código de un término. Gemelo de `formTag`. -/
def termTag : Term → Nat
  | .var _ => 0 | .func _ _ => 1

theorem termCode_eq_cons (t : Term) : ∃ r, termCode t = cons (numeral (termTag t)) r := by
  cases t <;> exact ⟨_, rfl⟩


/-! (Aquí vivían las **ranuras** —un `termCode` donde va un código de FÓRMULA, y al revés—, sobre `⊢`; retiradas con ADR‑115.) -/


/-! ### ⭐⭐⭐ UN SOLO REFUTADOR para toda la causa (f) transparente

⚠️ Antes de esto, cada tag y cada ranura pedía su propio lema: `formCode_ne_implc_tc_1`,
`_tc_2`, `_andc_tc_1`, … y el ensamblaje por tag encima. Contados: **~32**.

⭐ `NotFC e` dice «este término **no es el código de ninguna fórmula**», por razones puramente
**sintácticas**: o es un código de término, o lleva uno en una posición donde va un código de
fórmula. Es un inductivo de **nueve** constructores, y `formCode_ne_notFC` lo refuta **de una
vez para todos**.

⇒ el refutador de cada tag y cada ranura pasa a ser **una derivación de una línea**:

    -- tag 0, ranura 2:  implc a (implc (termCode u) a)
    formCode_ne_notFC (NotFC.implcR _ (NotFC.implcL _ (NotFC.tc u))) f

🔑 *Cuando los refutadores de una familia se COMPONEN (ADR‑094), la composición ya es un
inductivo esperando a que lo escriban.* 🗑️ Los lemas sueltos, que se quedaban como casos base y
ejemplos trabajados, y el propio `formCode_ne_notFC` eran de `⊢`: retirados con esa capa (ADR‑115).
Aquí quedan sólo los inductivos `NotFC`/`NotTC`, sin refutador.

⛔ **Su límite, medido**: sólo alcanza las posiciones **TRANSPARENTES**, las construidas con
`implc`/`andc`/`orc`/`forallc`/`exc`. De las ~32 ranuras, **tres** caen dentro de `substfc` —
el argumento de término de los tags 9 y 10, y el de fórmula del 13— y ésas **no se refutan por
la sintaxis**: van por las guardas que ADR‑020 metió dentro de `lineWF`.

⭐⭐ **Y la otra mitad**: `NotTC e` dice «este término **no es el código de ningún término**».
Hace falta porque (f) tiene **dos direcciones** —`termCode` donde va fórmula, y `formCode` donde
va término (tags 12 y 13)— y `eqc` es la única constructora transparente que abre un hueco de
TÉRMINO. Por eso `NotFC` gana dos constructoras `eqc*` que consumen un `NotTC`.

⚠️ `NotTC` tiene **una sola** constructora, y eso es deliberado: es lo que hace falta, medido.
Crecerá si aparece una posición de término transparente más. -/
inductive NotTC : Term → Prop
  | fc (A : Formula) : NotTC (formCode A)


inductive NotFC : Term → Prop
  | tc (u : Term) : NotFC (termCode u)
  | eqcL {a : Term} (b : Term) : NotTC a → NotFC (eqc a b)
  | eqcR (a : Term) {b : Term} : NotTC b → NotFC (eqc a b)
  | implcL {a : Term} (b : Term) : NotFC a → NotFC (implc a b)
  | implcR (a : Term) {b : Term} : NotFC b → NotFC (implc a b)
  | andcL {a : Term} (b : Term) : NotFC a → NotFC (andc a b)
  | andcR (a : Term) {b : Term} : NotFC b → NotFC (andc a b)
  | orcL {a : Term} (b : Term) : NotFC a → NotFC (orc a b)
  | orcR (a : Term) {b : Term} : NotFC b → NotFC (orc a b)
  | forallcI {a : Term} : NotFC a → NotFC (forallc a)
  | excI {a : Term} : NotFC a → NotFC (exc a)


end ROBINSON_PlusPlus.Meta.CodeDistinct

export ROBINSON_PlusPlus.Meta.CodeDistinct (
  formTag
  formCode_eq_cons
  termTag
  termCode_eq_cons
  NotFC
  NotFC.tc
  NotFC.implcL
  NotFC.implcR
  NotFC.andcL
  NotFC.andcR
  NotFC.orcL
  NotFC.orcR
  NotFC.forallcI
  NotFC.excI
  NotTC
  NotTC.fc
  NotFC.eqcL
  NotFC.eqcR
)
