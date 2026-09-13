/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.Core

/-!
# SONDEO · `henkin_extension_lemma` **es demostrable** — y por eso mismo hay que pensárselo

**Fecha:** 2026‑09‑13 · **Encargo:** «vamos a medirlo» (el último axioma de
`../FOL/cuarentena/Completeness.lean`).

## 0 · El resultado, en una línea

🏁 **Sale.** `IsMaximalConsistent S → IsHenkin S` es un teorema, y con él
`henkin_extension_lemma` es `lindenbaum_lemma` + tres líneas ⇒
**`cuarentena/Completeness.lean` llega a CERO axiomas propios**.

⚠️⚠️ **Y el precio está medido**: el footprint de `completeness` pasa de

    [propext, Classical.choice, Quot.sound, henkin_extension_lemma]

a

    [propext, Classical.choice, Quot.sound, FOL.MetaRules.raa]

⇒ **no es «1 → 0»**. Es cambiar *un postulado propio, honesto y con nombre* por **el axioma que
hace el cálculo COMPLETO y NO SÓLIDO** — el mismo que en `cuarentena/Inconsistencia.lean` demuestra
`False` en cuanto se le junta cualquier teorema de solidez. Y además obliga a que
`Completeness.lean` **importe `FOL.MetaRules`**, cosa que hoy **no hace** (medido: sus siete
imports no lo incluyen, y `cuarentena/README.md` §4 lo presentaba como la razón de que
`Completeness` no estuviera en el radio de la inconsistencia).

## 1 · Por qué sale: porque `raa` hace COMPLETO todo contexto

`raa : (Γ ⊢ A → Γ ⊢ ⊥) → Γ ⊢ ¬A` toma una **función de Lean**. Si `Γ ⊬ A`, esa función existe
**vacuamente** ⇒ `Γ ⊢ ¬A`. Luego `derives_complete` de abajo: **todo contexto decide toda
fórmula**, en tres líneas. Es lo que `Meta/OmegaStrength.lean` midió para `axioms ⊢` (ADR‑024,
**M‑10**), aquí enunciado para `Γ` arbitrario.

## 2 · La cadena, sin constantes frescas y sin inducción sobre `Derives`

El obstáculo clásico —«ampliar el lenguaje con constantes nuevas y probar la conservatividad»—
**no llega a plantearse**, y no porque la firma sea abierta (que lo es: `Term.func : String → …`),
sino porque la completitud sintáctica da el testigo por otro lado:

1. `S` maximal consistente y `S (∃A)`. Se toma `Γ0 ⊆ S` finito con `Γ0 ⊢ ∃A`.
2. Si ninguna instancia está en `S`, entonces **ninguna instancia es derivable desde `Γ0`**
   (si lo fuera, `max_cons_contains` la metería en `S`). ⭐ **Y aquí el contexto es UNIFORME**:
   `Γ0` para todas las instancias a la vez. Ése era el punto donde el argumento parecía romperse.
3. `no_instance_no_body`: si ninguna instancia es derivable desde `Γ0`, el **cuerpo** no es
   derivable desde el contexto **levantado** — por `intro_forall` seguido de `elim_forall`, los dos
   **constructores**. ⭐ Footprint `[propext]`: ni siquiera necesita `raa`.
4. Luego `raa` en el contexto levantado da `Γ0.map (liftFormula 0) ⊢ ¬A`, y con `elim_ex` cae `⊥`.

⚠️ **Nada de esto es inducción sobre `Derives`** — sólo constructores, `raa` como **introducción**,
y tercio excluido sobre la `Prop` `Γ ⊢ A`. **M‑11 no se viola.** Las pruebas son legítimas.

## 3 · ⚠️ Lo que NO se sigue, y lo que sí

* **No** se sigue `False`. El detonador de `Inconsistencia.lean` es `raa` **+ solidez**;
  `Completeness.lean` no demuestra solidez y va en la dirección contraria.
* **Sí** se sigue que el Teorema de Completitud de este repo sería *«todo lo válido es derivable
  en un cálculo que, cuando no deriva `A`, deriva `¬A`»*. Es cierto y es mucho menos de lo que
  el nombre sugiere. 🔑 **Es exactamente ADR‑024 otra vez: `⊢` es la herramienta, no el sujeto.**
* ⚠️ Y por eso la prueba de abajo **no vale para un cálculo normal**: en uno sólido
  `derives_complete` es falso y el paso 4 no existe. Esta Henkin sale de la patología, no de la
  lógica.

## 4 · El estado que deja

| | axiomas propios de `Completeness.lean` | footprint de `completeness` |
|---|---|---|
| hoy | **1** (`henkin_extension_lemma`) | `[propext, Classical.choice, Quot.sound, henkin_extension_lemma]` |
| con esto | **0** | `[propext, Classical.choice, Quot.sound, FOL.MetaRules.raa]` |

⬜ **Decisión del propietario.** Lo medido está aquí; lo que se publique con ello, no lo decide
la cifra.

⚠️ Este fichero **no entra en el build** (`sondeos/` está fuera del `lean_lib`). Para reejecutarlo,
desde la raíz de ROBINSON_PlusPlus: `lake env lean sondeos/HenkinSaleDeRaa.lean`.
-/

namespace HenkinSaleDeRaa
open FOL Classical

/-- ⭐ **Todo contexto de `Derives` decide toda fórmula.** Tres líneas, y la culpa es de `raa`:
su premisa es una **función de Lean**, que existe vacuamente cuando `Γ ⊬ A`. -/
theorem derives_complete (Γ : List Formula) (A : Formula) : (Γ ⊢ A) ∨ (Γ ⊢ neg A) := by
  by_cases h : Γ ⊢ A
  · exact Or.inl h
  · exact Or.inr (FOL.MetaRules.raa (fun hA => absurd hA h))

/-- Si **ninguna instancia** de `A` es derivable desde `Γ`, el cuerpo no lo es desde el contexto
levantado. ⭐ Sólo `intro_forall` y `elim_forall`, los dos **constructores**: footprint `[propext]`,
sin `raa`. Es la pieza que sustituye a la generalización sobre constante fresca — y por eso aquí
no hace falta ni ampliar el lenguaje ni probar conservatividad. -/
theorem no_instance_no_body {Γ : List Formula} {A : Formula}
    (h : ∀ t : Term, ¬ (Γ ⊢ substFormula 0 t A)) :
    ¬ ((Γ.map (liftFormula 0)) ⊢ A) := by
  intro hbody
  exact h (Term.var 0) (Derives.elim_forall Γ A (Term.var 0) (Derives.intro_forall Γ A hbody))

/-- Un existencial derivable **sin ninguna instancia derivable** vuelve inconsistente el contexto.
Éste es el corazón de la propiedad de Henkin, y el contexto `Γ` es el **mismo** en todo el
argumento — que era justo lo que parecía impedirlo. -/
theorem ex_without_witness_is_absurd {Γ : List Formula} {A : Formula}
    (hex : Γ ⊢ Formula.ex A)
    (h : ∀ t : Term, ¬ (Γ ⊢ substFormula 0 t A)) :
    Γ ⊢ Formula.bottom := by
  have hneg : (Γ.map (liftFormula 0)) ⊢ neg A :=
    FOL.MetaRules.raa (fun hA => absurd hA (no_instance_no_body h))
  have hbot : (A :: Γ.map (liftFormula 0)) ⊢ Formula.bottom := by
    refine Derives.elim_impl _ A Formula.bottom ?_ ?_
    · exact Derives.weakening _ _ _ hneg (fun x hx => List.Mem.tail _ hx)
    · exact Derives.hyp _ _ (List.Mem.head _)
  exact Derives.elim_ex Γ A Formula.bottom hex hbot

-- Footprints medidos el 2026‑09‑13.
#print axioms derives_complete              -- [propext, choice, Quot.sound, MetaRules.raa]
#print axioms no_instance_no_body           -- [propext]  ⭐ ni `raa`
#print axioms ex_without_witness_is_absurd  -- [propext, MetaRules.raa]

/-!
## 5 · La mitad que vive en `Completeness.lean`

No se puede compilar aquí —necesita `DerivesSet`, `IsMaximalConsistent`, `max_cons_contains`…, que
están en `cuarentena/` y no son importables—, pero **sí se compiló** sobre una copia del módulo, con
los footprints de §4. Son estas veinte líneas:

    theorem maxcons_isHenkin {S : Formula → Prop} (hMax : IsMaximalConsistent S) : IsHenkin S := by
      intro A hex
      apply Classical.byContradiction
      intro hno
      have hnot : ∀ t : Term, ¬ S (substFormula 0 t A) := fun t ht => hno ⟨t, ht⟩
      obtain ⟨Γ0, hΓ0, hDer⟩ := DerivesSet_hyp hex
      have hnoinst : ∀ t : Term, ¬ (Γ0 ⊢ substFormula 0 t A) := by
        intro t hd
        exact hnot t (max_cons_contains hMax ⟨Γ0, hΓ0, hd⟩)
      exact hMax.left ⟨Γ0, hΓ0, ex_without_witness_is_absurd hDer hnoinst⟩

    theorem henkin_extension_lemma {S : Formula → Prop} (hCons : IsConsistent S) :
        ∃ (S' : Formula → Prop), IsMaximalConsistent S' ∧ IsHenkin S' ∧ (∀ f, S f → S' f) := by
      obtain ⟨S', hMax, hSub⟩ := lindenbaum_lemma hCons
      exact ⟨S', hMax, maxcons_isHenkin hMax, hSub⟩

más `import FOL.MetaRules` en la cabecera, que hoy **no está**.
-/

end HenkinSaleDeRaa
