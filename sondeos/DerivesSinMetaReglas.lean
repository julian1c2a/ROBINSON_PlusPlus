/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL   -- ⚠️ SIN `FOL.MetaRules`: el `inductive` PELADO, sin los cuatro axiomas

/-!
# SONDEO · el `inductive Derives` PELADO ya tiene todas las reglas

**Fecha:** 2026‑09‑14 · **Para:** `doc/PLAN-COMPLETITUD-FINITISTA.md` §3 (**Paso 0**).

## La pregunta

Los cuatro axiomas de `FOL/MetaRules.lean` —`imp_intro`, `raa`, `or_elim`, `ex_elim`— **tienen** que
ser axiomas: su premisa `Γ ⊢ A → Γ ⊢ B` es una ocurrencia **no positiva** y el kernel rechaza el
`inductive`. Y por habitar `Derives` prohíben la inducción sobre él (**M‑11**, ADR‑029).

⇒ La pregunta del plan es: **si se declara un `Derives₀` sin ellos, ¿se pierde alguna REGLA, o sólo
se pierde la fuerza META?**

## La respuesta, medida

**Sólo la fuerza meta.** Este fichero importa **únicamente `FOL.FOL`** —el inductivo, sin
`MetaRules`— y construye la versión OBJETO de las cuatro, más `dne` y la generalización. Las seis
salen con footprint **`[propext]`**.

| meta‑regla (axioma, premisa‑FUNCIÓN) | equivalente OBJETO (constructor) |
|---|---|
| `imp_intro (h : Γ ⊢ A → Γ ⊢ B)` | `Derives.intro_impl : Derives (A :: Γ) B → …` |
| `raa (h : Γ ⊢ A → Γ ⊢ ⊥)` | `Derives.intro_impl` con `B := ⊥` |
| `or_elim` | `Derives.elim_or` |
| `ex_elim` | `Derives.elim_ex` |
| `dne` | `Derives.dne_rule` / `Derives.dne_schema` (constructores desde D‑2) |
| `gen` | `Derives.gen_rule` |

⇒ `Derives₀` := los **21** constructores de `Derives` **menos `gen_rule`** (que tiene premisa
**infinitaria** y no pinta en un cálculo finitario) es **deducción natural clásica completa** y
tiene **cero habitantes‑axioma** ⇒ **M‑11 no aplica** ⇒ la solidez y el lema de renombrado pasan a
ser trabajo ordinario.

⭐ **Y no toca a ROBINSON_PlusPlus**: `Derives₀` sería un objeto **nuevo** para la metateoría, con
un encaje `Derives₀ Γ f → Derives Γ f`. Las 320 citas de las meta‑reglas y las 164 de los
constructores se quedan donde están.

⚠️ Este fichero **no entra en el build**. Reejecutar con
`lake env lean sondeos/DerivesSinMetaReglas.lean` desde la raíz de RPP.
-/

namespace DerivesSinMetaReglas

theorem imp_intro_obj {Γ : List Formula} {A B : Formula}
    (h : Derives (A :: Γ) B) : Derives Γ (.impl A B) :=
  Derives.intro_impl Γ A B h

theorem raa_obj {Γ : List Formula} {A : Formula}
    (h : Derives (A :: Γ) Formula.bottom) : Derives Γ (neg A) :=
  Derives.intro_impl Γ A Formula.bottom h

theorem or_elim_obj {Γ : List Formula} {A B C : Formula}
    (hor : Derives Γ (.or A B))
    (ha : Derives (A :: Γ) C) (hb : Derives (B :: Γ) C) : Derives Γ C :=
  Derives.elim_or Γ A B C hor ha hb

theorem ex_elim_obj {Γ : List Formula} {A B : Formula}
    (hex : Derives Γ (.ex A))
    (hb : Derives (A :: Γ.map (liftFormula 0)) (liftFormula 0 B)) : Derives Γ B :=
  Derives.elim_ex Γ A B hex hb

theorem dne_obj {Γ : List Formula} {A : Formula}
    (h : Derives Γ (neg (neg A))) : Derives Γ A :=
  Derives.dne_rule Γ A h

theorem gen_obj {Γ : List Formula} {A : Formula}
    (h : ∀ n : Term, Derives Γ (substFormula 0 n A)) : Derives Γ (.forall A) :=
  Derives.gen_rule Γ A h

#print axioms imp_intro_obj   -- [propext]
#print axioms raa_obj         -- [propext]
#print axioms or_elim_obj     -- [propext]
#print axioms ex_elim_obj     -- [propext]
#print axioms dne_obj         -- [propext]
#print axioms gen_obj         -- [propext]  ⚠️ premisa INFINITARIA: fuera de `Derives₀`

end DerivesSinMetaReglas
