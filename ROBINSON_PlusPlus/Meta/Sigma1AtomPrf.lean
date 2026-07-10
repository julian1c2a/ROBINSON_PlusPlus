/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.TrackedCorePrf
import ROBINSON_PlusPlus.Meta.TcArithPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Sigma1AtomPrf

/-!
## META — NIVEL D real (§12‑A FASE 3, núcleo): toolkit RASTREADO del átomo `=eq`

Reflexión provable del átomo de igualdad `t =eq u`, para la Σ₁‑completitud provable del
verificador (`hbI`/`hbC` de `Meta/Sigma1BoundedPrf.lean`, cuyo átomo base es `nthc L i =eq x`).

**Por qué RASTREADO (y no libre de muro).** La reflexión de `t =eq u` para `t`, `u` **abstractos**
es imposible sin restricción (obstrucción de Tarski): `provCodeC'(t =eq u) = provFromCode(formCode(t
=eq u))` contiene `termCode t`/`termCode u` (**meta**, sin congruencia object), y `termCode t =eq
termCode u` NO se sigue de `t =eq u`. La salida estándar (Hilbert‑Bernays) es codificar los
argumentos con **`tcFn`** (que SÍ tiene congruencia Leibniz object, `prf_congr_tcFn`) y **discharge**
del puente `tcFn t =eq termCode t` cuando `t` es un numeral (`prf_tc_numeral`) — lo que hará la
inducción estructural de la fase 5.

Este módulo entrega el **átomo `=eq`** del toolkit rastreado, espejo exacto del de `In`
(`prf_provCodeC'_In_of_tracked`, `Meta/Sigma1CorePrf.lean`): constructor object `eqCodeFn`,
congruencia, clausura, transporte, y la reflexión rastreada `prf_provCodeC'_eq_of_tracked`.
-/

/-- Constructor object del código de `Formula.eq a b` desde los códigos `a`, `b` de sus términos:
    `⟨4, a, b⟩`. Espeja `formCode (.eq t u) = ⟨4, termCode t, termCode u⟩`. -/
def eqCodeFn (a b : Term) : Term :=
  cons (numeral 4) (cons a (cons b nil))

/-- **Puente definicional** con `formCode`: con los códigos meta `termCode`, `eqCodeFn` coincide
    con `formCode` de la igualdad (por definición de `formCode` sobre `.eq`). -/
theorem eqCodeFn_termCode (t u : Term) :
    eqCodeFn (termCode t) (termCode u) = formCode (Formula.eq t u) := rfl

/-- `provCodeC' (t =eq u)` es `provFromCode` del código con `termCode` (definicional). -/
theorem provCodeC'_eq_eq (t u : Term) :
    provCodeC' (Formula.eq t u) = provFromCode (eqCodeFn (termCode t) (termCode u)) := rfl

/-- **Clausura** de `eqCodeFn a b` bajo `liftTerm`: cerrado si `a`, `b` lo son. -/
theorem liftTerm_eqCodeFn (a b : Term)
    (ha : ∀ lvl, liftTerm lvl a = a) (hb : ∀ lvl, liftTerm lvl b = b) :
    ∀ lvl, liftTerm lvl (eqCodeFn a b) = eqCodeFn a b := by
  intro lvl
  simp only [eqCodeFn, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral, ha lvl, hb lvl]

/-- **Congruencia** de `eqCodeFn` en ambos argumentos (`Prf`). -/
theorem prf_congr_eqCodeFn {a a' b b' : Term}
    (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (eqCodeFn a b =eq eqCodeFn a' b') := by
  unfold eqCodeFn
  exact prf_congr_cons_tail
    (prf_eq_trans (prf_congr_cons_head ha) (prf_congr_cons_tail (prf_congr_cons_head hb)))

/-- **Transporte** de la demostrabilidad de una igualdad por igualdad de los códigos de sus
    términos (Leibniz object vía `provFromCode`). Espeja `prf_provFromCode_In_congr`. -/
theorem prf_provFromCode_eq_congr {a a' b b' : Term}
    (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (provFromCode (eqCodeFn a b) ⇒ provFromCode (eqCodeFn a' b')) :=
  prf_provCode_congr (prf_congr_eqCodeFn ha hb)

/-- **Clausura** de `provFromCode (eqCodeFn a b)` bajo `liftFormula` (args cerrados). -/
theorem liftFormula_provFromCode_eq (k : Nat) (a b : Term)
    (ha : ∀ lvl, liftTerm lvl a = a) (hb : ∀ lvl, liftTerm lvl b = b) :
    liftFormula k (provFromCode (eqCodeFn a b)) = provFromCode (eqCodeFn a b) :=
  liftFormula_provFromCode k (eqCodeFn a b) (liftTerm_eqCodeFn a b ha hb)

/-- **Reflexión RASTREADA del átomo `=eq`**: dada la demostrabilidad del código con argumentos
    rastreados `eqCodeFn tc uc` y los puentes `tc =eq termCode t`, `uc =eq termCode u`, se obtiene
    `provCodeC' (t =eq u)`. Espejo exacto de `prf_provCodeC'_In_of_tracked`.

    En la inducción (fase 5) los puentes se descargan cuando `t`, `u` son numerales
    (`tc = tcFn t`, `prf_tc_numeral`). -/
theorem prf_provCodeC'_eq_of_tracked {t u tc uc : Term}
    (ht : Prf (tc =eq termCode t)) (hu : Prf (uc =eq termCode u))
    (h : Prf (provFromCode (eqCodeFn tc uc))) :
    Prf (provCodeC' (Formula.eq t u)) :=
  prf_mp (prf_provFromCode_eq_congr ht hu) h

/-- **Reflexividad rastreada** (versión débil, con puente): se obtiene de la reflexión de `t =eq t`
    (teorema, `repr_pos'_prf (prf_refl t)`) transportada por `tc =eq termCode t`.
    **Superada** por `prf_provFromCode_eqCodeFn_refl` (libre de muro), que no necesita el puente. -/
theorem prf_provFromCode_eqCodeFn_refl_of_tracked {t tc : Term}
    (ht : Prf (tc =eq termCode t)) :
    Prf (provFromCode (eqCodeFn tc tc)) := by
  -- `provCodeC'(t =eq t) = provFromCode (eqCodeFn (termCode t) (termCode t))` (rfl), reflexividad
  have hrefl : Prf (provFromCode (eqCodeFn (termCode t) (termCode t))) :=
    repr_pos'_prf (prf_refl t)
  -- transporta `eqCodeFn (termCode t)(termCode t) ⇒ eqCodeFn tc tc` por `tc =eq termCode t` (simétrico)
  exact prf_mp (prf_provFromCode_eq_congr (prf_eq_symm ht) (prf_eq_symm ht)) hrefl

/-! ### Reflexividad LIBRE DE MURO (§15.4 punto 1)

La reflexión de `provFromCode (eqCodeFn c c)` para código `c` **abstracto** NO necesita el puente
`c =eq termCode t`: se construye directamente un **testigo del verificador** de una sola línea, la
**línea-axioma EQREFL** `⟨eqCodeFn c c, 12, c⟩`.

La clave es que el verificador comprueba `lineWF` **estructuralmente**:
`prf_lineWF_eqrefl (concl t) : lineWF ⟨concl, 12, t⟩ ⇔ (concl =eq eqc t t)`
— y `eqc t t` es exactamente `eqCodeFn t t`. Con `concl := eqCodeFn c c` y `t := c` la condición es
**pura reflexividad** (`prf_refl`), válida para `c` arbitrario. No interviene `termCode`. -/

/-- `eqCodeFn` es el constructor object `eqc` del verificador (definicional: `numeral 4 = σ⁴0`). -/
theorem eqCodeFn_eq_eqc (a b : Term) : eqCodeFn a b = eqc a b := rfl

/-- **Introductor de `provFromCode` desde un testigo de prueba**, a nivel de CÓDIGO arbitrario
    (versión de `provCodeC'_intro_prf` sin pasar por `formCode`). -/
theorem prf_provFromCode_intro (d p : Term)
    (h1 : Prf (chainOk nil p)) (h2 : Prf (In d (runFn nil p))) :
    Prf (provFromCode d) := by
  have hbody : Prf (land (chainOk nil p) (In d (runFn nil p))) := prf_and_intro h1 h2
  have hex : Prf (Formula.ex (land (chainOk nil (.var 0))
      (In (liftTerm 0 d) (runFn nil (.var 0))))) :=
    prf_ex_intro (A := land (chainOk nil (.var 0)) (In (liftTerm 0 d) (runFn nil (.var 0)))) p
      (by simpa [substFormula, substTerm, substTerms, land, chainOk, In, runFn, nil, zero,
            FOL.substTerm_liftTerm] using hbody)
  simpa [provFromCode, provFormulaC', substFormula, substTerm, substTerms, land, chainOk, In, runFn,
    nil, zero, FOL.substTerm_liftTerm] using hex

/-- **Línea-axioma EQREFL** para el código `c`: `⟨eqCodeFn c c, 12, c⟩` (regla 12 = `eqrefl`). -/
def eqreflLine (c : Term) : Term := cons (eqCodeFn c c) (cons (numeralM 12) (cons c nil))

/-- La línea EQREFL es válida en cualquier contexto: `lineWF` es **pura reflexividad**
    (`eqCodeFn c c =eq eqc c c`, defeq) y no tiene premisas (`premsOf =eq nil`). -/
theorem prf_lineOk_eqrefl (c : Term) : Prf (lineOk nil (eqreflLine c)) :=
  prf_and_intro
    (prf_iff_mpr (prf_lineWF_eqrefl (eqCodeFn c c) c) (prf_refl (eqCodeFn c c)))
    (prf_allIn_subst2 (prf_eq_symm (prf_premsOf_eqrefl (eqCodeFn c c) c)) (prf_allIn_nil nil))

/-- La cadena de una sola línea EQREFL es válida desde `nil`. -/
theorem prf_chainOk_eqrefl (c : Term) : Prf (chainOk nil (cons (eqreflLine c) nil)) :=
  prf_iff_mpr (prf_chainOk_cons nil (eqreflLine c) nil)
    (prf_and_intro (prf_lineOk_eqrefl c) (prf_chainOk_nil _))

/-- La conclusión de la cadena EQREFL es `eqCodeFn c c`. -/
theorem prf_in_runFn_eqrefl (c : Term) :
    Prf (In (eqCodeFn c c) (runFn nil (cons (eqreflLine c) nil))) := by
  have hrun : Prf (runFn nil (cons (eqreflLine c) nil) =eq cons (eqCodeFn c c) nil) :=
    prf_eq_trans (prf_runFn_cons nil (eqreflLine c) nil)
      (prf_eq_trans (prf_runFn_nil _)
        (prf_eq_trans (prf_concat_nil_eq _)
          (prf_congr_cons_head (prf_carc_cons (eqCodeFn c c) _))))
  exact prf_eq_subst_in (prf_eq_symm hrun) (prf_in_cons_head (eqCodeFn c c) nil)

/-- **Reflexividad LIBRE DE MURO**: `provFromCode (eqCodeFn c c)` para código `c` **arbitrario**,
    sin hipótesis de tracking. Testigo: la cadena de una línea `[⟨eqCodeFn c c, 12, c⟩]`. -/
theorem prf_provFromCode_eqCodeFn_refl (c : Term) : Prf (provFromCode (eqCodeFn c c)) :=
  prf_provFromCode_intro (eqCodeFn c c) (cons (eqreflLine c) nil)
    (prf_chainOk_eqrefl c) (prf_in_runFn_eqrefl c)

/-! ### Reflexión de la igualdad con código `tcFn` — también LIBRE DE MURO

Con la reflexividad libre de muro como base, la reflexión de `t =eq u` **al nivel del código
rastreado `tcFn`** ya no necesita ningún puente: de `t =eq u` sale `tcFn t =eq tcFn u`
(congruencia de `tcFn`, `prf_congr_tcFn`), y se transporta por Leibniz object. El muro de Tarski
queda **confinado al último paso** `provFromCode (eqCodeFn (tcFn t) (tcFn u)) → provCodeC' (t =eq u)`,
que exige `tcFn t =eq termCode t` — descargable con numerales (`prf_tc_numeral`) en la fase 5. -/

/-- Congruencia de `tcFn` en `PrfH` (Leibniz object). -/
theorem PrfH_congr_tcFn {Γ : List Formula} {t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (tcFn t₁ =eq tcFn t₂) := by
  let f : Formula := Formula.eq (tcFn (liftTerm 0 t₁)) (tcFn (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (tcFn t₁) (tcFn s) := by
    intro s
    simp only [f, tcFn, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (tcFn t₁)) Γ)

/-- Congruencia de `eqCodeFn` en ambos argumentos, en `PrfH`. -/
theorem PrfH_congr_eqCodeFn {Γ : List Formula} {a a' b b' : Term}
    (ha : PrfH Γ (a =eq a')) (hb : PrfH Γ (b =eq b')) :
    PrfH Γ (eqCodeFn a b =eq eqCodeFn a' b') := by
  unfold eqCodeFn
  exact PrfH_congr_cons_tail
    (PrfH_eq_trans (PrfH_congr_cons_head ha) (PrfH_congr_cons_tail (PrfH_congr_cons_head hb)))

/-- **Reflexión de la igualdad al nivel del código rastreado, LIBRE DE MURO**:
    `Prf ((t =eq u) ⇒ provFromCode (eqCodeFn (tcFn t) (tcFn u)))`, para `t`, `u` **arbitrarios**.
    Base = reflexividad libre de muro; paso = congruencia de `tcFn` + Leibniz object. -/
theorem pcc_eq_tracked (t u : Term) :
    Prf ((t =eq u) ⇒ provFromCode (eqCodeFn (tcFn t) (tcFn u))) := by
  refine prf_deduction ?_
  have hbase : PrfH [t =eq u] (provFromCode (eqCodeFn (tcFn t) (tcFn t))) :=
    prf_to_prfH (prf_provFromCode_eqCodeFn_refl (tcFn t)) _
  have htc : PrfH [t =eq u] (tcFn t =eq tcFn u) := PrfH_congr_tcFn (prfH_hyp_self _)
  have hcode : PrfH [t =eq u] (eqCodeFn (tcFn t) (tcFn t) =eq eqCodeFn (tcFn t) (tcFn u)) :=
    PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl (tcFn t)) _) htc
  exact PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.leibniz provFormulaC' _ _)) hcode) hbase

/-- **Reflexión completa del átomo `=eq`** cuando los términos están rastreados por `tcFn`
    (puente `tcFn t =eq termCode t`, descargable con numerales vía `prf_tc_numeral`):
    `Prf ((t =eq u) ⇒ provCodeC' (t =eq u))`. Compone `pcc_eq_tracked` con el transporte. -/
theorem pcc_eq_of_tc_bridge (t u : Term)
    (ht : Prf (tcFn t =eq termCode t)) (hu : Prf (tcFn u =eq termCode u)) :
    Prf ((t =eq u) ⇒ provCodeC' (Formula.eq t u)) := by
  refine prf_deduction ?_
  have h1 : PrfH [t =eq u] (provFromCode (eqCodeFn (tcFn t) (tcFn u))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked t u) _) (prfH_hyp_self _)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provFromCode_eq_congr ht hu) _) h1

/-! ### Átomos unarios: `atom1CodeFn` (constructor object del código de `Formula.atom s [a]`)

Necesario para el átomo `lineWF t = Formula.atom "lineWF" [t]` del cuerpo de `chainOkB`.
Espeja `atom2CodeFn` (`Meta/TrackedCorePrf.lean`), que cubre los átomos binarios (`In`,
`chainOk`, `allIn`). -/

/-- Constructor object del código de un **átomo unario** `Formula.atom s [a]` desde el código `a`
    de su argumento: `⟨3, ⌜s⌝, [a]⟩`. -/
def atom1CodeFn (s : String) (a : Term) : Term :=
  cons (numeral 3) (cons (strCode s) (cons (cons a nil) nil))

/-- **Puente definicional** con `formCode` (por definición de `formCode` sobre `.atom`). -/
theorem atom1CodeFn_termCode (s : String) (a : Term) :
    atom1CodeFn s (termCode a) = formCode (Formula.atom s [a]) := rfl

/-- **Clausura** de `atom1CodeFn s a` bajo `liftTerm`: cerrado si `a` lo es. -/
theorem liftTerm_atom1CodeFn (s : String) (a : Term)
    (ha : ∀ lvl, liftTerm lvl a = a) :
    ∀ lvl, liftTerm lvl (atom1CodeFn s a) = atom1CodeFn s a := by
  intro lvl
  simp only [atom1CodeFn, cons, nil, zero, liftTerm, liftTerms,
    liftTerm_numeral, liftTerm_strCode, ha lvl]

/-- **Congruencia** de `atom1CodeFn` en su argumento (`Prf`). -/
theorem prf_congr_atom1CodeFn {s : String} {a a' : Term} (ha : Prf (a =eq a')) :
    Prf (atom1CodeFn s a =eq atom1CodeFn s a') := by
  unfold atom1CodeFn
  exact prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head (prf_congr_cons_head ha)))

/-- **Transporte** de la demostrabilidad de un átomo unario por igualdad del código de su
    argumento (Leibniz object vía `provFromCode`). -/
theorem prf_provFromCode_atom1_congr {s : String} {a a' : Term} (ha : Prf (a =eq a')) :
    Prf (provFromCode (atom1CodeFn s a) ⇒ provFromCode (atom1CodeFn s a')) :=
  prf_provCode_congr (prf_congr_atom1CodeFn ha)

/-- **Clausura** de `provFromCode (atom1CodeFn s a)` bajo `liftFormula` (arg cerrado). -/
theorem liftFormula_provFromCode_atom1 (k : Nat) (s : String) (a : Term)
    (ha : ∀ lvl, liftTerm lvl a = a) :
    liftFormula k (provFromCode (atom1CodeFn s a)) = provFromCode (atom1CodeFn s a) :=
  liftFormula_provFromCode k (atom1CodeFn s a) (liftTerm_atom1CodeFn s a ha)

/-- Constructor object del código de `lineWF t` desde el código `tc` de `t`. -/
def lineWFCodeFn (tc : Term) : Term := atom1CodeFn "lineWF" tc

/-- Puente `lineWFCodeFn (termCode t) = formCode (lineWF t)` (rfl). -/
theorem lineWFCodeFn_termCode (t : Term) :
    lineWFCodeFn (termCode t) = formCode (lineWF t) := rfl

/-- `provCodeC' (lineWF t)` es `provFromCode` del código con `termCode` (definicional). -/
theorem provCodeC'_lineWF_eq (t : Term) :
    provCodeC' (lineWF t) = provFromCode (lineWFCodeFn (termCode t)) := rfl

/-- **Reflexión RASTREADA del átomo `lineWF`** (transporte; espejo de `=eq`/`In`).

    ⚠ **NOTA (obstrucción, ver `GODEL-D3-TRACKED-DESIGN.md` §16):** este es el *transporte*, no la
    *producción*. A diferencia de `=eq` (cuya reflexividad es un axioma, ⇒ reflexión libre de muro),
    `lineWF` es un **átomo primitivo** cuyos 21 axiomas son bicondicionales indexados por etiqueta de
    regla, **sin axioma de inversión**. Por eso `Prf (lineWF t ⇒ provFromCode (lineWFCodeFn (tcFn t)))`
    **no es derivable** para `t` abstracto: de `lineWF t` la teoría no puede extraer la etiqueta. -/
theorem prf_provCodeC'_lineWF_of_tracked {t tc : Term}
    (ht : Prf (tc =eq termCode t)) (h : Prf (provFromCode (lineWFCodeFn tc))) :
    Prf (provCodeC' (lineWF t)) :=
  prf_mp (prf_provFromCode_atom1_congr ht) h

/-! ### Inversión de `lineWF` en `Prf` (cierre del axioma `ax_lineWF_inv`, §16.4)

Desbloquea la reflexión de `lineWF` para líneas **abstractas**: de `lineWF t` se extrae la etiqueta
(una de las 21), y con ella el bicondicional `ax_lineWF_*` correspondiente determina la condición
estructural — una **disyunción finita de átomos `=eq`**, que ya sabemos reflejar (`pcc_eq_tracked`). -/

/-- Cierre `Prf` de `ax_lineWF_inv`: `lineWF line ⇒ (⋁_{k=0}^{20} lineTag line =eq numeralM k)`. -/
theorem prf_lineWF_inv (line : Term) :
    Prf (Formula.impl (lineWF line) (tagDisj line 20)) := by
  have hh := prf_spec (prf_ax (show ax_lineWF_inv ∈ axioms by simp [axioms])) line
  simpa [ax_lineWF_inv, tagDisj, lineTag, lineWF, nthc, numeralM, lor, succ, zero,
    substFormula, substTerm, substTerms, FOL.substTerm_liftTerm] using hh

end ROBINSON_PlusPlus.Meta.Sigma1AtomPrf

export ROBINSON_PlusPlus.Meta.Sigma1AtomPrf (
  eqCodeFn eqCodeFn_termCode provCodeC'_eq_eq eqCodeFn_eq_eqc
  liftTerm_eqCodeFn prf_congr_eqCodeFn prf_provFromCode_eq_congr
  liftFormula_provFromCode_eq
  prf_provCodeC'_eq_of_tracked prf_provFromCode_eqCodeFn_refl_of_tracked
  prf_provFromCode_intro eqreflLine prf_lineOk_eqrefl prf_chainOk_eqrefl
  prf_in_runFn_eqrefl prf_provFromCode_eqCodeFn_refl
  PrfH_congr_tcFn PrfH_congr_eqCodeFn pcc_eq_tracked pcc_eq_of_tc_bridge
  atom1CodeFn atom1CodeFn_termCode liftTerm_atom1CodeFn prf_congr_atom1CodeFn
  prf_provFromCode_atom1_congr liftFormula_provFromCode_atom1
  lineWFCodeFn lineWFCodeFn_termCode provCodeC'_lineWF_eq prf_provCodeC'_lineWF_of_tracked
  prf_lineWF_inv
)
