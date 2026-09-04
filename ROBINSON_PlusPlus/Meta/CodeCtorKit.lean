/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
import ROBINSON_PlusPlus.Meta.LineWFTrackedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
open ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.CodeCtorKit

/-!
## META — NIVEL D real (B.3c): KIT de constructores de código, genérico en el TAG

Los constructores de código del lenguaje son **todos el mismo `cons`‑árbol** variando sólo su tag
numérico y su aridad:

  `botc` = ⟨2⟩ · `atomc` = ⟨3,·,·⟩ · `eqc` = ⟨4,·,·⟩ · `implc` = ⟨5,·,·⟩ · `forallc` = ⟨6,·⟩
  `andc` = ⟨7,·,·⟩ · `orc` = ⟨8,·,·⟩ · `exc` = ⟨9,·⟩

En vez de dar constructor object, congruencia, distribución de `substtc` y ecuación `tc` **para cada
uno** —que es lo que se hizo a mano con `eqcT` en `LineWFTrackedPrf`— se parametrizan por aridad y
tag: `nulT` / `unT` / `binT`. Con eso, `eqcT = binT 4` pasa a ser un caso particular, y los árboles
`E` de los 18 tags pendientes quedan cubiertos de un golpe.

La pieza que de verdad importa es la última sección: la **congruencia dentro de `Prov`**
(`pcc_congr_binT_{1,2}_code`, `pcc_congr_unT_code`), que generaliza el
`pcc_congr_eqcT_diag_code_imp` que `eqrefl` tuvo que construir a mano.
-/

/-- Constructor object de un código NULARIO de tag `m` (p. ej. `botc` = tag 2). -/
def nulT (m : Nat) : Term := consT (termCode (numeralM m)) (termCode nil)

/-- Constructor object de un código UNARIO de tag `m` (p. ej. `forallc` = 6, `exc` = 9). -/
def unT (m : Nat) (a : Term) : Term := consT (termCode (numeralM m)) (consT a (termCode nil))

/-- Constructor object de un código BINARIO de tag `m` (`eqc` = 4, `implc` = 5, `andc` = 7,
    `orc` = 8). -/
def binT (m : Nat) (a b : Term) : Term :=
  consT (termCode (numeralM m)) (consT a (consT b (termCode nil)))

/-- Puente definicional con `termCode`, caso nulario. -/
theorem nulT_termCode (m : Nat) : nulT m = termCode (cons (numeralM m) nil) := rfl

/-- Puente definicional con `termCode`, caso unario. -/
theorem unT_termCode (m : Nat) (a : Term) :
    unT m (termCode a) = termCode (cons (numeralM m) (cons a nil)) := rfl

/-- Puente definicional con `termCode`, caso binario. -/
theorem binT_termCode (m : Nat) (a b : Term) :
    binT m (termCode a) (termCode b) = termCode (cons (numeralM m) (cons a (cons b nil))) := rfl

/-! ### Congruencia y distribución de `substtc` -/

/-- Congruencia de `unT`. -/
theorem prf_congr_unT {m : Nat} {a a' : Term} (ha : Prf (a =eq a')) :
    Prf (unT m a =eq unT m a') := by
  unfold unT; exact prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_refl _))

/-! ### El constructor binario con ETIQUETA ABSTRACTA — y los tres `substtc` que lo alimentan

    ⚠️ **Bajados de `sondeos/SubstfcPlanos.lean` en B3 (2026‑09‑04), y bajados AQUI y no a
    `LiftcCodePrf` por el CICLO DE IMPORTS ([ADR‑019](../../DECISIONS.md))**: `LiftcCodePrf`
    IMPORTA este modulo, asi que un general que viviera alli no podria reescribir
    `prf_congr_binT` ni `prf_substtc_binT`, que son de aqui. Puestos aqui, los reescribe **los
    dos**, y ademas `LiftcCodePrf` puede colgar de el sus `_at`.

    ⚠️ **TARIFA del movimiento, pagada**: `prf_substtc_binK_at` consume
    `prf_substtc_termCode_closed`/`_zero`, que vivian en `LiftcCodePrf` y estaban en SU bloque
    `export`. Han subido con el — y se han retirado de aquel `export`, porque exportar una
    constante que el modulo ya no declara es ERROR DURO. -/

theorem prf_substtc_termCode_closed (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) := by
  have h := prf_substtc_arith_open v W t
  rwa [substCodeT_closed v W t ht] at h

theorem prf_substtc_termCode_numeralM (v m : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  prf_substtc_termCode_closed v W (numeralM m) (fun c => liftTerm_numeralM c m)

theorem prf_substtc_termCode_zero (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  prf_substtc_termCode_closed v W zero (fun _ => rfl)

/-- El binario con la etiqueta **abstracta** (`termCode T` con `T` cerrado), que es lo que
    permite factorizar `impl`/`and`/`or` en UN lema en vez de tres. -/
def binK (H a b : Term) : Term := consT H (consT a (consT b (termCode nil)))

/-- Puente por `rfl` con el `binT` de este mismo modulo. -/
theorem binK_binT (m : Nat) (a b : Term) : binK (termCode (numeralM m)) a b = binT m a b := rfl

theorem prf_congr_binK {H a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (binK H a b =eq binK H a' b') :=
  prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_congr_consT hb (prf_refl _)))

/-- `substtc` atraviesa `binK` a nivel ARBITRARIO (`prf_substtc_binT` solo vale a nivel
    `zero`). Requiere que la etiqueta `T` sea CERRADA. -/
theorem prf_substtc_binK_at (T : Term) (hT : ∀ c : Nat, liftTerm c T = T)
    (n : Nat) (W a b : Term) :
    Prf (substtc (numeral n) W (binK (termCode T) a b)
      =eq binK (termCode T) (substtc (numeral n) W a) (substtc (numeral n) W b)) := by
  unfold binK consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_closed n W T hT)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero n W)))

/-- Congruencia de `binT` en ambos argumentos. **Corolario de `prf_congr_binK`** desde B3:
    `binT m a b` es `binK (termCode (numeralM m)) a b` por `rfl`. Tiene 11 call-sites reales
    en cuatro modulos (`CodeCtorKit`, `CodeTreeReflect`, `LiftcCodePrf`, `LineWFEfqPrf`). -/
theorem prf_congr_binT {m : Nat} {a a' b b' : Term}
    (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) : Prf (binT m a b =eq binT m a' b') :=
  prf_congr_binK (H := termCode (numeralM m)) ha hb

/-- `substtc` es la identidad sobre un código nulario (es cerrado). -/
theorem prf_substtc_nulT (m : Nat) (W : Term) :
    Prf (substtc zero W (nulT m) =eq nulT m) := by
  unfold nulT
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  exact prf_congr_consT (substtc_inv_termCode_numeralM m W)
    (LineWFTrackedPrf.substtc_inv_termCode_of_tc prf_tc_zero W)

/-- `substtc` distribuye sobre `unT` (el tag y el `⌜nil⌝` son cerrados). -/
theorem prf_substtc_unT (m : Nat) (W a : Term) :
    Prf (substtc zero W (unT m a) =eq unT m (substtc zero W a)) := by
  unfold unT
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  refine prf_congr_consT (substtc_inv_termCode_numeralM m W) ?_
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  exact prf_congr_consT (prf_refl _)
    (LineWFTrackedPrf.substtc_inv_termCode_of_tc prf_tc_zero W)

/-- `substtc` distribuye sobre `binT`. **Corolario de `prf_substtc_binK_at` al nivel `zero`**
    desde B3 (`numeral 0` es `zero` por `rfl`).

    ⚠️ Este es el corolario que la colocacion inicialmente propuesta —el general en
    `LiftcCodePrf`— dejaba **INALCANZABLE**, porque aquel modulo importa este. Es el caso
    concreto que motivo la correccion de ADR‑019. -/
theorem prf_substtc_binT (m : Nat) (W a b : Term) :
    Prf (substtc zero W (binT m a b) =eq binT m (substtc zero W a) (substtc zero W b)) :=
  prf_substtc_binK_at (numeralM m) (fun c => liftTerm_numeralM c m) 0 W a b

/-- Invariancia `substtc` de `nulT` (forma `∀ W`, la que consumen los Leibniz internos). -/
theorem substtc_inv_nulT (m : Nat) : ∀ W, Prf (substtc zero W (nulT m) =eq nulT m) :=
  prf_substtc_nulT m

/-- Invariancia `substtc` de `unT`, heredada de la de su argumento. -/
theorem substtc_inv_unT {m : Nat} {a : Term}
    (ha : ∀ W, Prf (substtc zero W a =eq a)) :
    ∀ W, Prf (substtc zero W (unT m a) =eq unT m a) := fun W =>
  prf_eq_trans (prf_substtc_unT m W a) (prf_congr_unT (ha W))

/-- Invariancia `substtc` de `binT`, heredada de la de sus argumentos. -/
theorem substtc_inv_binT {m : Nat} {a b : Term}
    (ha : ∀ W, Prf (substtc zero W a =eq a)) (hb : ∀ W, Prf (substtc zero W b =eq b)) :
    ∀ W, Prf (substtc zero W (binT m a b) =eq binT m a b) := fun W =>
  prf_eq_trans (prf_substtc_binT m W a b) (prf_congr_binT (ha W) (hb W))

/-! ### Ecuaciones `tc` (el código del código, por aridad) -/

/-! ### Los sustitutos del KIT (2026-08-23)

Aquí vivían `prf_tc_nul`/`prf_tc_un`/`prf_tc_bin`, que eran **`prf_tc_cons'` compuesto** sobre el
árbol `⟨m,a,b⟩`. Con argumentos ABSTRACTOS esos enunciados son **falsos** bajo la lectura numeral,
así que no se recuperan a nivel de código.

**Salen por composición de `pcc_dot_cons`, dentro de `Prov` y sin inducción nueva** — que es lo que
predijo la medición (`sondeos/KitPayoff.lean`), porque `nulT`/`unT`/`binT` son todos `cons`-árboles.
Las hojas (`prf_tc_numeral`, `prf_tc_zero`) **nunca murieron**; sólo el paso recursivo. -/

/-- `tcFn ⟨m⟩ = nulT m`, **dentro de `Prov`**. Sólo reescrituras de CÓDIGO sobre `pcc_dot_cons`. -/
theorem pcc_dot_nul (m : Nat) :
    Prf (provFromCode (eqCodeFn (nulT m) (tcFn (cons (numeralM m) nil)))) := by
  unfold nulT
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_consT (prf_tc_numeralM' m) prf_tc_zero) (prf_refl _)))
    (pcc_dot_cons (numeralM m) nil)

/-- `tcFn ⟨m,a⟩ = unT m ȧ`, **dentro de `Prov`**: código → 1 paso interno → código. -/
theorem pcc_dot_un (m : Nat) (a : Term) :
    Prf (provFromCode (eqCodeFn (unT m (tcFn a)) (tcFn (cons (numeralM m) (cons a nil))))) := by
  unfold unT
  have h1 : Prf (provFromCode (eqCodeFn (consT (termCode (numeralM m)) (tcFn (cons a nil)))
      (tcFn (cons (numeralM m) (cons a nil))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
        (prf_congr_consT (prf_tc_numeralM' m) (prf_refl _)) (prf_refl _)))
      (pcc_dot_cons (numeralM m) (cons a nil))
  have h2 : Prf (provFromCode (eqCodeFn
      (consT (termCode (numeralM m)) (consT (tcFn a) (tcFn nil)))
      (tcFn (cons (numeralM m) (cons a nil))))) := by
    refine pcc_rw (fun s => eqCodeFn (consT (termCode (numeralM m)) s)
      (tcFn (cons (numeralM m) (cons a nil)))) ?_ _ _ (pcc_dot_cons_symm a nil) h1
    intro s
    refine prf_eq_trans (prf_substfc_eq zero s _ _) ?_
    exact prf_congr_eqCodeFn
      (prf_eq_trans (prf_substtc_consT zero s _ _)
        (prf_congr_consT (substtc_inv_termCode_numeralM' m s) (prf_substtc_varc0 s)))
      (substtc_inv_tcFn _ s)
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_consT (prf_refl _) (prf_congr_consT (prf_refl _) prf_tc_zero)) (prf_refl _))) h2

/-- `tcFn ⟨m,a,b⟩ = binT m ȧ ḃ`, **dentro de `Prov`**: código → 2 pasos internos anidados → código. -/
theorem pcc_dot_bin (m : Nat) (a b : Term) :
    Prf (provFromCode (eqCodeFn (binT m (tcFn a) (tcFn b))
      (tcFn (cons (numeralM m) (cons a (cons b nil)))))) := by
  unfold binT
  let RHS : Term := tcFn (cons (numeralM m) (cons a (cons b nil)))
  have hR : ∀ W, Prf (substtc zero W RHS =eq RHS) := substtc_inv_tcFn _
  have h1 : Prf (provFromCode (eqCodeFn
      (consT (termCode (numeralM m)) (tcFn (cons a (cons b nil)))) RHS)) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
        (prf_congr_consT (prf_tc_numeralM' m) (prf_refl _)) (prf_refl _)))
      (pcc_dot_cons (numeralM m) (cons a (cons b nil)))
  have h2 : Prf (provFromCode (eqCodeFn
      (consT (termCode (numeralM m)) (consT (tcFn a) (tcFn (cons b nil)))) RHS)) := by
    refine pcc_rw (fun s => eqCodeFn (consT (termCode (numeralM m)) s) RHS) ?_ _ _
      (pcc_dot_cons_symm a (cons b nil)) h1
    intro s
    refine prf_eq_trans (prf_substfc_eq zero s _ _) ?_
    exact prf_congr_eqCodeFn
      (prf_eq_trans (prf_substtc_consT zero s _ _)
        (prf_congr_consT (substtc_inv_termCode_numeralM' m s) (prf_substtc_varc0 s)))
      (hR s)
  have h3 : Prf (provFromCode (eqCodeFn
      (consT (termCode (numeralM m)) (consT (tcFn a) (consT (tcFn b) (tcFn nil)))) RHS)) := by
    refine pcc_rw (fun s => eqCodeFn (consT (termCode (numeralM m)) (consT (tcFn a) s)) RHS) ?_ _ _
      (pcc_dot_cons_symm b nil) h2
    intro s
    refine prf_eq_trans (prf_substfc_eq zero s _ _) ?_
    refine prf_congr_eqCodeFn ?_ (hR s)
    refine prf_eq_trans (prf_substtc_consT zero s _ _) ?_
    refine prf_congr_consT (substtc_inv_termCode_numeralM' m s) ?_
    exact prf_eq_trans (prf_substtc_consT zero s _ _)
      (prf_congr_consT (substtc_inv_tcFn a s) (prf_substtc_varc0 s))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_consT (prf_refl _) (prf_congr_consT (prf_refl _)
      (prf_congr_consT (prf_refl _) prf_tc_zero))) (prf_refl _))) h3

/-- Las direcciones simétricas, que es lo que consumen los sitios reales. -/
theorem pcc_dot_nul_symm (m : Nat) :
    Prf (provFromCode (eqCodeFn (tcFn (cons (numeralM m) nil)) (nulT m))) :=
  pcc_mp_code_apply
    (pcc_eq_symm_code_internal (nulT m) (tcFn (cons (numeralM m) nil)) (substtc_inv_nulT m))
    (pcc_dot_nul m)

theorem pcc_dot_un_symm (m : Nat) (a : Term) :
    Prf (provFromCode (eqCodeFn (tcFn (cons (numeralM m) (cons a nil))) (unT m (tcFn a)))) :=
  pcc_mp_code_apply
    (pcc_eq_symm_code_internal (unT m (tcFn a)) (tcFn (cons (numeralM m) (cons a nil)))
      (substtc_inv_unT (substtc_inv_tcFn a)))
    (pcc_dot_un m a)

theorem pcc_dot_bin_symm (m : Nat) (a b : Term) :
    Prf (provFromCode (eqCodeFn (tcFn (cons (numeralM m) (cons a (cons b nil))))
      (binT m (tcFn a) (tcFn b)))) :=
  pcc_mp_code_apply
    (pcc_eq_symm_code_internal (binT m (tcFn a) (tcFn b))
      (tcFn (cons (numeralM m) (cons a (cons b nil))))
      (substtc_inv_binT (substtc_inv_tcFn a) (substtc_inv_tcFn b)))
    (pcc_dot_bin m a b)

/-! ### Congruencia DENTRO de `Prov` (la pieza que cada reflector consume)

Cambiar un argumento del árbol de código **bajo `Prov`**, con la igualdad interna en la mano. Va
por Leibniz interno sobre un contexto de código de un solo hueco. Generaliza el
`pcc_congr_eqcT_diag_code_imp` que `eqrefl` construyó a mano (que era su caso diagonal). -/

/-- **Congruencia interna de `binT` en el 2º argumento**: de `Prov(⌜X = Y⌝)` sale
    `Prov(⌜binT m A X = binT m A Y⌝)`. -/
theorem pcc_congr_binT_2_code (m : Nat) (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (binT m A X) (binT m A Y))) := by
  let Ac : Term := eqc (binT m A X) (binT m A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (binT m A X) (binT m A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (binT m A X) (binT m A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_binT m w A X) (prf_congr_binT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_binT m w A (varc (numeral 0)))
        (prf_congr_binT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (binT m A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- **Congruencia interna de `binT` en el 1er argumento**. -/
theorem pcc_congr_binT_1_code (m : Nat) (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (binT m X B) (binT m Y B))) := by
  let Ac : Term := eqc (binT m X B) (binT m (varc (numeral 0)) B)
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (binT m X B) (binT m w B)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (binT m X B) (binT m (varc (numeral 0)) B)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_binT m w X B) (prf_congr_binT (hX w) (hB w))
    · exact prf_eq_trans (prf_substtc_binT m w (varc (numeral 0)) B)
        (prf_congr_binT (prf_substtc_varc0 w) (hB w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (binT m X B))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- **Congruencia interna de `unT`**. -/
theorem pcc_congr_unT_code (m : Nat) (X Y : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (unT m X) (unT m Y))) := by
  let Ac : Term := eqc (unT m X) (unT m (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (unT m X) (unT m w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (unT m X) (unT m (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_unT m w X) (prf_congr_unT (hX w))
    · exact prf_eq_trans (prf_substtc_unT m w (varc (numeral 0)))
        (prf_congr_unT (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (unT m X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

end ROBINSON_PlusPlus.Meta.CodeCtorKit

export ROBINSON_PlusPlus.Meta.CodeCtorKit (
  nulT unT binT nulT_termCode unT_termCode binT_termCode
  prf_congr_unT prf_congr_binT
  binK binK_binT prf_congr_binK prf_substtc_binK_at
  prf_substtc_termCode_closed prf_substtc_termCode_numeralM prf_substtc_termCode_zero
  prf_substtc_nulT prf_substtc_unT prf_substtc_binT
  substtc_inv_nulT substtc_inv_unT substtc_inv_binT
  pcc_dot_nul pcc_dot_un pcc_dot_bin pcc_dot_nul_symm pcc_dot_un_symm pcc_dot_bin_symm
  pcc_congr_binT_1_code pcc_congr_binT_2_code pcc_congr_unT_code
)
