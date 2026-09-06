/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.EvalBoundedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.PropCodePrf

/-!
## META — NIVEL D real (§39): LÓGICA PROPOSICIONAL e INDUCCIÓN **internas** a nivel de código

Cierre del sistema de prueba interno. Todas las líneas‑axioma proposicionales del verificador son
**estructurales** (bicondicional `lineWF` con códigos **arbitrarios** y `premsOf = nil`), igual que
EQREFL/Q1/Q2/LEIBNIZ (§25): cada una se demuestra con un testigo de **una sola línea** (`pcc_axline`)
y sale **libre de muro** (`[propext, choice, Quot.sound]`, sin `prf_inAxC`).

| Tag | Línea | Esquema |
|:---:|:------|:--------|
| 0 | `p1`  | `A ⇒ (B ⇒ A)` (K) |
| 1 | `p2`  | `(A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))` (S) |
| 7 | `j3`  | `(A ∨ B) ⇒ ((A ⇒ C) ⇒ ((B ⇒ C) ⇒ C))` (`∨`‑elim) |
| 8 | `efq` | `⊥ ⇒ A` |
| 18 | `ind` | `A[0] ⇒ (∀x. A[x] ⇒ A[σx]) ⇒ ∀x. A[x]` (**inducción**) |

Con **P1 + P2 + MP** el cálculo implicacional interno es completo: de ahí el debilitamiento
(`pcc_weaken_code`) y el **silogismo hipotético** (`pcc_imp_trans_code`), y con J3 el `∨`‑elim en
forma implicación (`pcc_or_elim_imp_code`). Junto con lo ya existente (MP, `∀`‑elim, `∃`‑intro, gen,
Leibniz, `∧`, `∨`‑intro), **`Prov` dispone ya de lógica completa**.

**`pcc_ind_code` es el desbloqueo de la ruta B**: la INTRODUCCIÓN del `∀` acotado (que `hC_dot`
necesita, y que §30 dejó pendiente) requiere inducción, y la regla `ind` del verificador resulta ser
estructural — luego la inducción interna cuesta una línea.
-/

/-! ### Las cuatro líneas‑axioma proposicionales que faltaban -/

/-- **P1 (K) codificado**: `⊢ Prov(⌜ A ⇒ (B ⇒ A) ⌝)`, códigos arbitrarios. -/
theorem pcc_p1_code (Ac Bc : Term) : Prf (provFromCode (implc Ac (implc Bc Ac))) :=
  pcc_axline _ (cons (implc Ac (implc Bc Ac)) (cons (numeralM 0) (cons Ac (cons Bc nil))))
    (prf_iff_mpr (prf_lineWF_p1 _ Ac Bc) (prf_refl _))
    (prf_carc_cons _ _) (prf_premsOf_p1 _ Ac Bc)

/-- **P2 (S) codificado**: `⊢ Prov(⌜ (A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)) ⌝)`. -/
theorem pcc_p2_code (Ac Bc Cc : Term) :
    Prf (provFromCode (implc (implc Ac (implc Bc Cc)) (implc (implc Ac Bc) (implc Ac Cc)))) :=
  pcc_axline _
    (cons (implc (implc Ac (implc Bc Cc)) (implc (implc Ac Bc) (implc Ac Cc)))
      (cons (numeralM 1) (cons Ac (cons Bc (cons Cc nil)))))
    (prf_iff_mpr (prf_lineWF_p2 _ Ac Bc Cc) (prf_refl _))
    (prf_carc_cons _ _) (prf_premsOf_p2 _ Ac Bc Cc)

/-- **J3 (`∨`‑elim) codificado**: `⊢ Prov(⌜ (A ∨ B) ⇒ ((A ⇒ C) ⇒ ((B ⇒ C) ⇒ C)) ⌝)`. -/
theorem pcc_j3_code (Ac Bc Cc : Term) :
    Prf (provFromCode (implc (orc Ac Bc) (implc (implc Ac Cc) (implc (implc Bc Cc) Cc)))) :=
  pcc_axline _
    (cons (implc (orc Ac Bc) (implc (implc Ac Cc) (implc (implc Bc Cc) Cc)))
      (cons (numeralM 7) (cons Ac (cons Bc (cons Cc nil)))))
    (prf_iff_mpr (prf_lineWF_j3 _ Ac Bc Cc) (prf_refl _))
    (prf_carc_cons _ _) (prf_premsOf_j3 _ Ac Bc Cc)

/-- **EFQ codificado**: `⊢ Prov(⌜ ⊥ ⇒ A ⌝)`. -/
theorem pcc_efq_code (Ac : Term) : Prf (provFromCode (implc botc Ac)) :=
  pcc_axline _ (cons (implc botc Ac) (cons (numeralM 8) (cons Ac nil)))
    (prf_iff_mpr (prf_lineWF_efq _ Ac) (prf_refl _))
    (prf_carc_cons _ _) (prf_premsOf_efq _ Ac)

/-! ### Reglas derivadas del cálculo implicacional interno (P1 + P2 + MP) -/

/-- **Debilitamiento interno**: de `Prov(⌜B⌝)` sale `Prov(⌜A ⇒ B⌝)`. -/
theorem pcc_weaken_code (Ac Bc : Term) (h : Prf (provFromCode Bc)) :
    Prf (provFromCode (implc Ac Bc)) :=
  pcc_mp_code_apply (pcc_p1_code Bc Ac) h

/-- **Silogismo hipotético interno**: de `Prov(⌜A ⇒ B⌝)` y `Prov(⌜B ⇒ C⌝)` sale `Prov(⌜A ⇒ C⌝)`. -/
theorem pcc_imp_trans_code (Ac Bc Cc : Term)
    (h1 : Prf (provFromCode (implc Ac Bc))) (h2 : Prf (provFromCode (implc Bc Cc))) :
    Prf (provFromCode (implc Ac Cc)) :=
  pcc_mp_code_apply
    (pcc_mp_code_apply (pcc_p2_code Ac Bc Cc) (pcc_weaken_code Ac (implc Bc Cc) h2))
    h1

/-- **`∨`‑elim interno, forma IMPLICACIÓN**: de `Prov(⌜A ⇒ C⌝)` y `Prov(⌜B ⇒ C⌝)` sale
    `Prov(⌜(A ∨ B) ⇒ C⌝)`. Dos usos de P2 sobre J3, debilitando cada hipótesis bajo el `(A ∨ B) ⇒`. -/
theorem pcc_or_elim_imp_code (Ac Bc Cc : Term)
    (h1 : Prf (provFromCode (implc Ac Cc))) (h2 : Prf (provFromCode (implc Bc Cc))) :
    Prf (provFromCode (implc (orc Ac Bc) Cc)) := by
  have hstep1 : Prf (provFromCode (implc (orc Ac Bc) (implc (implc Bc Cc) Cc))) :=
    pcc_mp_code_apply
      (pcc_mp_code_apply (pcc_p2_code (orc Ac Bc) (implc Ac Cc) (implc (implc Bc Cc) Cc))
        (pcc_j3_code Ac Bc Cc))
      (pcc_weaken_code (orc Ac Bc) (implc Ac Cc) h1)
  exact pcc_mp_code_apply
    (pcc_mp_code_apply (pcc_p2_code (orc Ac Bc) (implc Bc Cc) Cc) hstep1)
    (pcc_weaken_code (orc Ac Bc) (implc Bc Cc) h2)

/-- **`∨`‑elim interno, forma APLICADA**. -/
theorem pcc_or_elim_code (Ac Bc Cc : Term)
    (hor : Prf (provFromCode (orc Ac Bc)))
    (h1 : Prf (provFromCode (implc Ac Cc))) (h2 : Prf (provFromCode (implc Bc Cc))) :
    Prf (provFromCode Cc) :=
  pcc_mp_code_apply (pcc_or_elim_imp_code Ac Bc Cc h1 h2) hor

/-! ### INDUCCIÓN interna a nivel de código (tag 18) — el desbloqueo del `∀` acotado

La regla `ind` del verificador es **estructural** (`prf_lineWF_ind` es un bicondicional con código `a`
**arbitrario** y `premsOf = nil`), luego la inducción interna se demuestra con un testigo de **una
línea**, exactamente como Leibniz (§25). Es lo que permite la INTRODUCCIÓN del `∀` acotado (`hC_dot`),
que no se puede hacer con la disyunción finita de casos porque la cota (`lenc p`, con `p` abstracto)
**no es un numeral concreto**. -/

/-- Conclusión de la línea‑axioma IND para un código `Ac` **arbitrario**:
    `Ac[0] ⇒ (∀x. Ac[x] ⇒ Ac[σx]) ⇒ ∀x. Ac[x]`. -/
noncomputable def indConcl (Ac : Term) : Term :=
  implc (substfc zero (termCodeM zero) Ac)
    (implc (forallc (implc Ac (substfc zero (termCodeM (succ (.var 0))) (liftfc (succ zero) Ac))))
           (forallc Ac))

/-- **INDUCCIÓN interna a nivel de código, LIBRE DE MURO**:
    `⊢ Prov(⌜ Ac[0] ⇒ (∀x. Ac[x] ⇒ Ac[σx]) ⇒ ∀x. Ac[x] ⌝)`.

    ⚠️ **Ya NO es «para `Ac` arbitrario»** ([ADR-020](../../DECISIONS.md)): el esquema `lineWF`
    del tag 18 lleva la guarda `hasWitF` dentro, así que `Ac` tiene que ser un código con
    testigo. Sigue siendo libre de MURO —que es otra cosa: no pide `pcc_eval_substfc`—, y la
    guarda la pagan `prf_hasWitF_fc` para códigos reales y los constructores de
    `Meta/SubstfcWitnessPrf.lean` para los construidos. -/
theorem pcc_ind_code (Ac : Term) (hwA : Prf (hasWitF Ac)) :
    Prf (provFromCode (indConcl Ac)) :=
  pcc_axline _ (cons (indConcl Ac) (cons (numeralM 18) (cons Ac nil)))
    (prf_iff_mpr (prf_lineWF_ind _ Ac hwA) (prf_refl _))
    (prf_carc_cons _ _) (prf_premsOf_ind _ Ac)

end ROBINSON_PlusPlus.Meta.PropCodePrf

export ROBINSON_PlusPlus.Meta.PropCodePrf (
  pcc_p1_code pcc_p2_code pcc_j3_code pcc_efq_code
  pcc_weaken_code pcc_imp_trans_code pcc_or_elim_imp_code pcc_or_elim_code
  indConcl pcc_ind_code
)
