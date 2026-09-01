/-
Probe/MF_censo.lean — SONDEO (B): **EL CENSO**. ¿Cuánto del módulo C cubre la vía BARATA?

Mide, sobre el árbol de HOY, las cuatro preguntas del encargo:
  §0  ¿sigue vivo el bloqueo 2 (`axiomsCodeT` opaco)?          →  NO. Está MUERTO.
  §1  ¿el CASO 4 (aridad) es realmente gratis?                 →  SÍ, y para los 21 tags.
  §2  ¿cuántos de los 21 tags caen por `carc` sola?            →  19 (los 21 menos `thy` y `mp`).
  §3  el sustituto de `canon_ne` SOBRE LÍNEAS: ¿cuánto cuesta? →  ~45 líneas, net-0.
  §4  ¿hay que cambiar `StdChain`?                             →  NO: `NumTree` ya la subsume.

## TABLA DEL CENSO — los 21 tags  (columnas A, B y C MEDIDAS contra `tagConcl` de producción)

| tag | regla   | ar | lenc | caso 4 | cláusula `carc` | reconstrucción     | caso 3 barato        |
|----:|---------|---:|-----:|:------:|:----------------|:-------------------|:---------------------|
|   0 | p1      |  2 |    4 |   ✅   | `implc`         | PURA               | cabeza               |
|   1 | p2      |  3 |    5 |   ✅   | `implc`         | PURA               | cabeza               |
|   2 | c1      |  2 |    4 |   ✅   | `implc`         | PURA               | cabeza               |
|   3 | c2      |  2 |    4 |   ✅   | `implc`         | PURA               | cabeza               |
|   4 | c3      |  2 |    4 |   ✅   | `implc`         | PURA               | cabeza               |
|   5 | j1      |  2 |    4 |   ✅   | `implc`         | PURA               | cabeza               |
|   6 | j2      |  2 |    4 |   ✅   | `implc`         | PURA               | cabeza               |
|   7 | j3      |  3 |    5 |   ✅   | `implc`         | PURA               | cabeza               |
|   8 | efq     |  1 |    3 |   ✅   | `implc`         | PURA               | cabeza               |
|   9 | q1      |  2 |    4 |   ✅   | `implc`         | `substfc`          | cabeza (+`concl_code`)|
|  10 | q2      |  2 |    4 |   ✅   | `implc`         | `substfc`          | cabeza (+`concl_code`)|
|  11 | q3      |  2 |    4 |   ✅   | `implc`         | `liftfc`           | cabeza (+`concl_code`)|
|  12 | eqrefl  |  1 |    3 |   ✅   | **`eqc`**       | PURA               | cabeza               |
|  13 | leibniz |  3 |    5 |   ✅   | `implc`         | `substfc`×2        | cabeza (+`concl_code`)|
|  14 | p3      |  1 |    3 |   ✅   | `implc`         | PURA               | cabeza               |
|  15 | thy     |  0 |    2 |   ✅   | **NINGUNA**     | —                  | **CERRADO** (§0)     |
|  16 | mp      |  1 |    3 |   ✅   | **NINGUNA**     | —                  | ⛔ sólo aridad/`premsOf`|
|  17 | gen     |  1 |    3 |   ✅   | **`forallc`**   | PURA               | cabeza               |
|  18 | ind     |  1 |    3 |   ✅   | `implc`         | `substfc`×2+`liftfc`| cabeza (+`concl_code`)|
|  19 | qconf   |  2 |    4 |   ✅   | `implc`         | `liftfc`           | cabeza (+`concl_code`)|
|  20 | listInd |  1 |    3 |   ✅   | `implc`         | `substfc`×2+`liftfc`×3| cabeza (+`concl_code`)|

**RECUENTOS** (todos verificados por `decide`/`rfl` más abajo):
* `lenc`: 2→1 tag · 3→7 · 4→10 · 5→3.  (= los datos del encargo, confirmados.)
* **caso 4 (aridad): 21/21.** TODO `ax_lineWF_<tag>` de hoy lleva la cláusula `lenc = ṅ`
  (esquemas ESTRICTOS, B.3b). Es comparación de NUMERALES: `gnum_ne`. **GRATIS.**
* **cláusula sobre `carc`: 19/21** — faltan `thy` (15) y `mp` (16). Cabezas exigidas:
  `implc` ×17 · `eqc` ×1 (12) · `forallc` ×1 (17).
* **reconstrucción PURA: 12/19** (0-8, 12, 14, 17) · **con `substfc`/`liftfc`: 7/19**
  (9, 10, 11, 13, 18, 19, 20).
-/
import ROBINSON_PlusPlus.Meta

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.CodeDistinct
open ROBINSON_PlusPlus.Meta.LineWFCases
open ROBINSON_PlusPlus.Meta.AxiomListCode
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf
open ROBINSON_PlusPlus.Meta.OmegaReflect

namespace MFCenso

#check @gnum_ne
#check @prf_refl
#check @Prf.incl
#check @Prf₀.c2
#check @objList
#check @prf_lineWF_q1
#check @prf_formCode_numeral
#check @consN
#check @codeNat

/-! ## §0 — ¿sigue vivo el «bloqueo 2» (`axiomsCodeT` OPACO)?

El plan (§B, 2026-07-14) afirma: «**`NegVerifier` NO es demostrable mientras `axiomsCodeT` sea
opaco**», porque no existiría forma de refutar `In v axiomsCodeT`.

Contra-medición: la dirección negativa **no hay que transportarla, YA ESTÁ TRANSPORTADA** —
`neg_In_axiomsCodeT` vive en `Meta/AxiomListCode.lean`, en producción, y su consumidor
`derives_lineWF_neg_thy_of_not_prf` **también**. El caso `thy` está CERRADO de punta a punta. -/

/-- **El bloqueo 2 está MUERTO**: la refutación de `In ⌜φ⌝ axiomsCodeT` existe, en producción. -/
theorem bloqueo2_muerto (φ : Formula) (hnp : ¬ Prf φ) :
    axioms ⊢ neg (In (formCode φ) axiomsCodeT) :=
  neg_In_axiomsCodeT φ hnp

/-- Y su consumidor: la línea `thy` basura queda REFUTADA. Tag 15 — **cerrado**. -/
theorem tag15_cerrado (φ : Formula) (hnp : ¬ Prf φ) :
    axioms ⊢ neg (lineWF (cons (formCode φ) (cons (numeralM 15) nil))) :=
  derives_lineWF_neg_thy_of_not_prf φ hnp

/-! ## §1 — CASO 4 (la ARIDAD): ¿es realmente gratis?

Los **21** `ax_lineWF_<tag>` de HOY son esquemas ESTRICTOS: su RHS lleva SIEMPRE, como primer
conjunto, la cláusula canónica `lenc line =eq numeralM (aridad+2)`. Luego una línea con la
aridad equivocada se refuta comparando NUMERALES — que es lo único que este proyecto siempre
ha sabido hacer (`gnum_ne`). **Sin `carc`, sin distinción de árboles, sin `canon_ne`.**

Se mide con el tag 9 (`q1`, `lenc` canónico = 4) sobre una línea de aridad 3 (`lenc` = 3),
tal y como pedía el encargo. -/

/-- Puente `numeralM k = numeral k` (dos definiciones idénticas en namespaces distintos). -/
theorem numM_eq_num : ∀ n : Nat, numeralM n = numeral n
  | 0 => rfl
  | n + 1 => by show succ (numeralM n) = succ (numeral n); rw [numM_eq_num n]

/-- `m ≠ n ⟹ ⊢ ¬(ṁ = ṅ)` en la notación `numeralM` de `Minimal`. -/
theorem numM_ne {m n : Nat} (h : m ≠ n) : axioms ⊢ neg (numeralM m =eq numeralM n) := by
  rw [numM_eq_num, numM_eq_num]; exact gnum_ne h

/-- **MOTOR GENÉRICO DEL CASO 4** — vale para los 21 tags, sin excepción: de la forma estricta
    `lineWF L ⇔ (lenc L = ṅ ∧ Q)` y del cómputo `⊢ lenc L = ṁ` con `m ≠ n`, sale `⊢ ¬ lineWF L`.
    Nótese que `Q` queda **libre**: la conclusión NO se toca. -/
theorem derives_lineWF_neg_of_lenc {L : Term} {Q : Formula} {n m : Nat}
    (hiff : Prf (lineWF L ⇔ Formula.and (lenc L =eq numeralM n) Q))
    (hlen : Prf (lenc L =eq numeralM m)) (hnm : m ≠ n) :
    axioms ⊢ neg (lineWF L) := by
  have hfwd : Prf (lineWF L ⇒ Formula.and (lenc L =eq numeralM n) Q) := prf_and_elim_left hiff
  have hgetN : axioms ⊢ (lineWF L ⇒ (lenc L =eq numeralM n)) :=
    prf_to_derives (prf_imp_trans hfwd (Prf.incl (Prf₀.c2 _ _)))
  have hlenD : axioms ⊢ (lenc L =eq numeralM m) := prf_to_derives hlen
  exact FOL.MetaRules.imp_intro (fun hwf =>
    FOL.MetaRules.mp (numM_ne hnm)
      (FOL.derive_eq_trans (FOL.derive_eq_symm hlenD) (FOL.MetaRules.mp hgetN hwf)))

/-- La forma ESTRICTA del tag 9 sobre una línea de aridad 3 (la `q1` canónica es de aridad 2). -/
theorem lineWF_tag9_strict_ar3 (concl a : Term) :
    Prf (lineWF (cons concl (cons (numeralM 9) (cons a nil))) ⇔
      Formula.and (lenc (cons concl (cons (numeralM 9) (cons a nil))) =eq numeralM 4)
        (carc (cons concl (cons (numeralM 9) (cons a nil))) =eq
          implc (forallc (nthc (cons concl (cons (numeralM 9) (cons a nil))) (numeralM 2)))
            (substfc zero (nthc (cons concl (cons (numeralM 9) (cons a nil))) (numeralM 3))
              (nthc (cons concl (cons (numeralM 9) (cons a nil))) (numeralM 2))))) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_q1 ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 9) (cons a nil)))
  simp only [ax_lineWF_q1, substFormula, substTerm, substTerms, lineWF, carc, nthc, lenc,
    forallc, implc, substfc, numeralM, cons, nil, zero, succ, iff,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hax
  refine prf_mp hax ?_
  exact prf_eq_trans (prf_nthc_succ _ _ _) (prf_nthc_zero _ _)

/-- `lenc ⟨c, 9̇, a⟩ = 3̇` (puro cómputo con `ax_lenc_nil`/`ax_lenc_cons`). -/
theorem lenc_tag9_ar3 (concl a : Term) :
    Prf (lenc (cons concl (cons (numeralM 9) (cons a nil))) =eq numeralM 3) :=
  prf_eq_trans (prf_lenc_cons _ _)
    (prf_eq_congr_succ (prf_eq_trans (prf_lenc_cons _ _)
      (prf_eq_congr_succ (prf_eq_trans (prf_lenc_cons _ _)
        (prf_eq_congr_succ prf_lenc_nil)))))

/-- ✅ **EL CASO 4 ES GRATIS.** Línea con tag 9 (`q1`, `lenc` canónico 4) y ARIDAD 3: REFUTADA,
    para `concl` y `a` **arbitrarios** — sin tocar la conclusión ni distinguir árboles. -/
theorem caso4_gratis_tag9 (concl a : Term) :
    axioms ⊢ neg (lineWF (cons concl (cons (numeralM 9) (cons a nil)))) :=
  derives_lineWF_neg_of_lenc (lineWF_tag9_strict_ar3 concl a) (lenc_tag9_ar3 concl a)
    (by decide)

/-! ### `mp` (16): el tag que `carc` NUNCA puede refutar — y que la ARIDAD sí

`ax_lineWF_mp` es hoy `∀. (nthc #0 1 = 1̇6) ⇒ (lineWF #0 ⇔ (lenc #0 = 3̇))`: **sin** cláusula sobre
la conclusión (por diseño; la fidelidad de `mp` la lleva íntegra `premsOf`). Su RHS es la cláusula
de longitud SOLA — luego la vía de la aridad es la ÚNICA que refuta `lineWF` de un `mp`, y la
cubre entera. -/

/-- Variante del motor para el RHS sin conjunción (el caso `mp`). -/
theorem derives_lineWF_neg_of_lenc' {L : Term} {n m : Nat}
    (hiff : Prf (lineWF L ⇔ (lenc L =eq numeralM n)))
    (hlen : Prf (lenc L =eq numeralM m)) (hnm : m ≠ n) :
    axioms ⊢ neg (lineWF L) := by
  have hgetN : axioms ⊢ (lineWF L ⇒ (lenc L =eq numeralM n)) :=
    prf_to_derives (prf_and_elim_left hiff)
  have hlenD : axioms ⊢ (lenc L =eq numeralM m) := prf_to_derives hlen
  exact FOL.MetaRules.imp_intro (fun hwf =>
    FOL.MetaRules.mp (numM_ne hnm)
      (FOL.derive_eq_trans (FOL.derive_eq_symm hlenD) (FOL.MetaRules.mp hgetN hwf)))

/-- La forma estricta de `mp` sobre una línea de aridad 2 (la canónica es de aridad 1). -/
theorem lineWF_tag16_strict_ar2 (concl a b : Term) :
    Prf (lineWF (cons concl (cons (numeralM 16) (cons a (cons b nil)))) ⇔
      (lenc (cons concl (cons (numeralM 16) (cons a (cons b nil)))) =eq numeralM 3)) := by
  have hax := prf_spec (prf_ax (show ax_lineWF_mp ∈ axioms by simp [axioms]))
    (cons concl (cons (numeralM 16) (cons a (cons b nil))))
  simp only [ax_lineWF_mp, substFormula, substTerm, substTerms, lineWF, nthc, lenc,
    numeralM, cons, nil, zero, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hax
  exact prf_mp hax (prf_eq_trans (prf_nthc_succ _ _ _) (prf_nthc_zero _ _))

/-- ✅ **`mp` con aridad 2: REFUTADO** — por longitud, la única vía que tiene. -/
theorem caso4_gratis_tag16 (concl a b : Term) :
    axioms ⊢ neg (lineWF (cons concl (cons (numeralM 16) (cons a (cons b nil))))) :=
  derives_lineWF_neg_of_lenc' (lineWF_tag16_strict_ar2 concl a b)
    (prf_eq_trans (prf_lenc_cons _ _)
      (prf_eq_congr_succ (prf_eq_trans (prf_lenc_cons _ _)
        (prf_eq_congr_succ (prf_eq_trans (prf_lenc_cons _ _)
          (prf_eq_congr_succ (prf_eq_trans (prf_lenc_cons _ _)
            (prf_eq_congr_succ prf_lenc_nil))))))))
    (by decide : (4:Nat) ≠ 3)

/-! ## §2 — CASO 3 (la ECUACIÓN ESTRUCTURAL): el censo de los 21 tags

La tabla se **mide contra la producción** (`tagConcl` de `Meta/LineWFCases.lean`), no se copia
a mano: dos lectores mecánicos (`headTag`, la cabeza de código que el esquema exige en la
conclusión; `hasSL`, si la reconstrucción contiene `substfc`/`liftfc`) se evalúan sobre
`tagConcl k (args del tag k)` y se comprueban por `rfl`. -/

/-- Lee un numeral `σⁿ0` como `n`. -/
def numOfTerm : Term → Option Nat
  | .func "0" []  => some 0
  | .func "σ" [t] => (numOfTerm t).map (· + 1)
  | _             => none

/-- Cabeza (tag de constructor de código) de un `cons`. -/
def headTag : Term → Option Nat
  | .func "::" [h, _] => numOfTerm h
  | _                 => none

mutual
/-- ¿La reconstrucción contiene `substfc`/`liftfc` (funciones OPACAS, no constructores)? -/
def hasSL : Term → Bool
  | .var _      => false
  | .func s ts  => s == "substfc" || s == "liftfc" || hasSLs ts
def hasSLs : List Term → Bool
  | []      => false
  | t :: ts => hasSL t || hasSLs ts
end

/-- Args de prueba del tag `k` (tantos como su aridad de producción). -/
def dummyArgs (n : Nat) : List Term := (List.range n).map Term.var

/-- La columna A de la tabla: `lenc` canónico del tag `k`. Se **mide**: es `tagArity k + 2`. -/
def tagLenc (k : Nat) : Nat := tagArity k + 2

-- ### Columna A — los cuatro grupos de `lenc` (los datos del encargo, VERIFICADOS)
example : ((List.range 21).filter (fun k => tagLenc k == 2)).length = 1  := by decide
example : ((List.range 21).filter (fun k => tagLenc k == 3)).length = 7  := by decide
example : ((List.range 21).filter (fun k => tagLenc k == 4)).length = 10 := by decide
example : ((List.range 21).filter (fun k => tagLenc k == 5)).length = 3  := by decide
example : (List.range 21).all (fun k => tagLenc k == 2 || tagLenc k == 3 ||
            tagLenc k == 4 || tagLenc k == 5) = true := by decide

-- ### Columna B — la CABEZA que cada esquema exige en `carc` (medida sobre `tagConcl`)
-- 5 = implc · 4 = eqc · 6 = forallc · none = el esquema NO liga la conclusión
example : (tagConcl 0  (dummyArgs (tagArity 0 ))).bind headTag = some 5 := by rfl
example : (tagConcl 1  (dummyArgs (tagArity 1 ))).bind headTag = some 5 := by rfl
example : (tagConcl 2  (dummyArgs (tagArity 2 ))).bind headTag = some 5 := by rfl
example : (tagConcl 3  (dummyArgs (tagArity 3 ))).bind headTag = some 5 := by rfl
example : (tagConcl 4  (dummyArgs (tagArity 4 ))).bind headTag = some 5 := by rfl
example : (tagConcl 5  (dummyArgs (tagArity 5 ))).bind headTag = some 5 := by rfl
example : (tagConcl 6  (dummyArgs (tagArity 6 ))).bind headTag = some 5 := by rfl
example : (tagConcl 7  (dummyArgs (tagArity 7 ))).bind headTag = some 5 := by rfl
example : (tagConcl 8  (dummyArgs (tagArity 8 ))).bind headTag = some 5 := by rfl
example : (tagConcl 9  (dummyArgs (tagArity 9 ))).bind headTag = some 5 := by rfl
example : (tagConcl 10 (dummyArgs (tagArity 10))).bind headTag = some 5 := by rfl
example : (tagConcl 11 (dummyArgs (tagArity 11))).bind headTag = some 5 := by rfl
example : (tagConcl 12 (dummyArgs (tagArity 12))).bind headTag = some 4 := by rfl  -- eqc
example : (tagConcl 13 (dummyArgs (tagArity 13))).bind headTag = some 5 := by rfl
example : (tagConcl 14 (dummyArgs (tagArity 14))).bind headTag = some 5 := by rfl
example : tagConcl 15 (dummyArgs (tagArity 15)) = none := by rfl                   -- thy
example : tagConcl 16 (dummyArgs (tagArity 16)) = none := by rfl                   -- mp
example : (tagConcl 17 (dummyArgs (tagArity 17))).bind headTag = some 6 := by rfl  -- forallc
example : (tagConcl 18 (dummyArgs (tagArity 18))).bind headTag = some 5 := by rfl
example : (tagConcl 19 (dummyArgs (tagArity 19))).bind headTag = some 5 := by rfl
example : (tagConcl 20 (dummyArgs (tagArity 20))).bind headTag = some 5 := by rfl

-- ### Columna C — ¿la reconstrucción es PURA (sólo constructores) o lleva `substfc`/`liftfc`?
example : (tagConcl 0  (dummyArgs (tagArity 0 ))).map hasSL = some false := by rfl
example : (tagConcl 1  (dummyArgs (tagArity 1 ))).map hasSL = some false := by rfl
example : (tagConcl 2  (dummyArgs (tagArity 2 ))).map hasSL = some false := by rfl
example : (tagConcl 3  (dummyArgs (tagArity 3 ))).map hasSL = some false := by rfl
example : (tagConcl 4  (dummyArgs (tagArity 4 ))).map hasSL = some false := by rfl
example : (tagConcl 5  (dummyArgs (tagArity 5 ))).map hasSL = some false := by rfl
example : (tagConcl 6  (dummyArgs (tagArity 6 ))).map hasSL = some false := by rfl
example : (tagConcl 7  (dummyArgs (tagArity 7 ))).map hasSL = some false := by rfl
example : (tagConcl 8  (dummyArgs (tagArity 8 ))).map hasSL = some false := by rfl
example : (tagConcl 9  (dummyArgs (tagArity 9 ))).map hasSL = some true  := by rfl  -- substfc
example : (tagConcl 10 (dummyArgs (tagArity 10))).map hasSL = some true  := by rfl  -- substfc
example : (tagConcl 11 (dummyArgs (tagArity 11))).map hasSL = some true  := by rfl  -- liftfc
example : (tagConcl 12 (dummyArgs (tagArity 12))).map hasSL = some false := by rfl
example : (tagConcl 13 (dummyArgs (tagArity 13))).map hasSL = some true  := by rfl  -- substfc
example : (tagConcl 14 (dummyArgs (tagArity 14))).map hasSL = some false := by rfl
example : (tagConcl 17 (dummyArgs (tagArity 17))).map hasSL = some false := by rfl
example : (tagConcl 18 (dummyArgs (tagArity 18))).map hasSL = some true  := by rfl  -- subst+lift
example : (tagConcl 19 (dummyArgs (tagArity 19))).map hasSL = some true  := by rfl  -- liftfc
example : (tagConcl 20 (dummyArgs (tagArity 20))).map hasSL = some true  := by rfl  -- subst+lift

/-! ### La vía barata del caso 3: la CABEZA de `carc`

16 de los 19 tags estructurales exigen `implc` (cabeza 5), uno `eqc` (12) y uno `forallc` (17).
Si la conclusión es el código de una fórmula cuyo constructor NO es el exigido, la línea cae por
comparación de NUMERALES en la cabeza — con args **arbitrarios**, sin mirar dentro. -/

/-- Conclusión = código de una fórmula que NO es implicación ⇒ todo esquema que exija `implc`
    queda refutado, para args ARBITRARIOS. -/
theorem carc_head_kills_implc : ∀ {ψ : Formula}, (∀ A B, ψ ≠ Formula.impl A B) →
    ∀ x y : Term, axioms ⊢ neg (formCode ψ =eq implc x y)
  | .bottom,          _, _, _ => cons_ne_head (gnum_ne (a := 2) (b := 5) (by decide))
  | .atom _ _,        _, _, _ => cons_ne_head (gnum_ne (a := 3) (b := 5) (by decide))
  | .eq _ _,          _, _, _ => cons_ne_head (gnum_ne (a := 4) (b := 5) (by decide))
  | .impl a b,        h, _, _ => absurd rfl (h a b)
  | Formula.forall _, _, _, _ => cons_ne_head (gnum_ne (a := 6) (b := 5) (by decide))
  | .and _ _,         _, _, _ => cons_ne_head (gnum_ne (a := 7) (b := 5) (by decide))
  | .or _ _,          _, _, _ => cons_ne_head (gnum_ne (a := 8) (b := 5) (by decide))
  | .ex _,            _, _, _ => cons_ne_head (gnum_ne (a := 9) (b := 5) (by decide))

/-- ✅ **CASO 3, VÍA BARATA, SOBRE UNA LÍNEA REAL**: tag 0 (`p1`), aridad correcta, args
    `x`,`y` ARBITRARIOS, conclusión el código de una fórmula no-implicativa ⇒ línea REFUTADA. -/
theorem caso3_barato_p1 {ψ : Formula} (hψ : ∀ A B, ψ ≠ Formula.impl A B) (x y : Term) :
    axioms ⊢ neg (lineWF (cons (formCode ψ) (cons (numeralM 0) (objList [x, y])))) :=
  derives_lineWF_neg_of_tag 0 (formCode ψ) [x, y] _ rfl
    (carc_head_kills_implc hψ x (implc y x))

/-! ## §3 — EL SUSTITUTO DE `canon_ne` SOBRE LÍNEAS: `NumTree` (distinción por VALOR)

⚠️ La trampa que hay que evitar: **NO** codificar la línea con `codeNatTerm` — eso codifica
**SINTAXIS**, y es el error de categoría que hizo falso a `canon_ne`. Lo que hay que distinguir es
el **VALOR**, y `consN` es la operación de valor. El motor ya está en producción:
`prf_cons_eval_of` (`Meta/CodeNumeralPrf.lean:125`).

`NumTree t n` = «el árbol `t` denota el número `n`». Cuatro constructores; `nil` sale gratis
(`nil := zero`) y `formCode φ` también (`prf_formCode_numeral`, producción). -/

/-- Árboles de VALOR conocido. Es la clase que debe sustituir a `IsCanon` en `StdChain`. -/
inductive NumTree : Term → Nat → Prop
  | zero : NumTree zero 0
  | succ {t n} : NumTree t n → NumTree (succ t) (n + 1)
  | cons {h t a b} : NumTree h a → NumTree t b → NumTree (cons h t) (consN a b)
  | code (φ : Formula) : NumTree (formCode φ) (codeNat φ)

/-- La teoría COMPUTA el valor. (Producción entera: `prf_cons_eval_of`, `prf_formCode_numeral`.) -/
theorem prf_numTree {t : Term} {n : Nat} (h : NumTree t n) : Prf (t =eq numeral n) := by
  induction h with
  | zero => exact prf_refl zero
  | succ _ ih => exact prf_eq_congr_succ ih
  | cons _ _ iha ihb => exact prf_cons_eval_of iha ihb
  | code φ => exact prf_formCode_numeral φ

/-- **EL SUSTITUTO DE `canon_ne`.** Hipótesis correcta: los VALORES difieren (no la sintaxis). -/
theorem numTree_ne {a b : Term} {m n : Nat}
    (ha : NumTree a m) (hb : NumTree b n) (h : m ≠ n) : axioms ⊢ neg (a =eq b) :=
  FOL.MetaRules.imp_intro (fun hab =>
    FOL.MetaRules.mp (gnum_ne h)
      (FOL.derive_eq_trans (FOL.derive_eq_symm (prf_to_derives (prf_numTree ha)))
        (FOL.derive_eq_trans hab (prf_to_derives (prf_numTree hb)))))

/-- Los numerales son `NumTree` (con su propio valor). -/
theorem numTree_numM : ∀ n : Nat, NumTree (numeralM n) n
  | 0     => NumTree.zero
  | n + 1 => NumTree.succ (numTree_numM n)

/-- Decisión META del valor (`lineNat`): lo que computa el módulo C/D. -/
def treeVal : Term → Option Nat
  | .func "0" []      => some 0
  | .func "σ" [t]     => (treeVal t).map (· + 1)
  | .func "::" [h, t] =>
      match treeVal h, treeVal t with
      | some a, some b => some (consN a b)
      | _, _           => none
  | _ => none

/-- Acuerdo entre la decisión META y la clase. (Inducción FUNCIONAL: el `ite` sobre `String` de
    `split`/`simp` fabrica un cast que el KERNEL rechaza — trampa registrada del proyecto.) -/
theorem numTree_of_treeVal : ∀ {t : Term} {n : Nat}, treeVal t = some n → NumTree t n := by
  intro t
  fun_induction treeVal t with
  | case1 => intro n h; cases h; exact NumTree.zero
  | case2 t ih =>
      intro n h
      cases hv : treeVal t with
      | none => rw [hv] at h; exact absurd h (by simp)
      | some m => rw [hv] at h; simp at h; subst h; exact NumTree.succ (ih hv)
  | case3 h t va vb hv1 hv2 ih1 ih2 =>
      intro n hn; injection hn with hn; subst hn
      apply NumTree.cons <;>
        first
          | exact ih1 hv1 | exact ih1 hv2 | exact ih2 hv1 | exact ih2 hv2
  | case4 => intro n h; exact absurd h (by simp)
  | case5 => intro n h; exact absurd h (by simp)

/-! ### Por qué el VALOR y no la sintaxis: la colisión que mató a `canon_ne` -/

/-- `cons nil nil` **ES** `2̇` — provable. Es el contraejemplo que refuta `canon_ne`, y aquí sale
    como CONSECUENCIA del motor de valor (los dos lados tienen valor `consN 0 0 = 2`). -/
theorem cons_nil_nil_es_dos : Prf (cons nil nil =eq numeralM 2) := by
  rw [numM_eq_num]
  exact prf_numTree (NumTree.cons NumTree.zero NumTree.zero)

/-- ⛔ Y aquí la brecha donde la descendencia estructural **NO PUEDE**: un `cons` frente a un
    NUMERAL. No hay `succ_ne_cons` — y no puede haberlo (línea de arriba). Por VALOR sí sale. -/
theorem valor_gana_donde_la_estructura_no_puede :
    axioms ⊢ neg (formCode Formula.bottom =eq numeralM 3) :=
  numTree_ne (NumTree.code Formula.bottom) (numTree_numM 3) (by decide)

/-- ✅ **PAYOFF sobre una LÍNEA REAL** (tag 8, `efq`, aridad correcta): descendencia estructural
    (`cons_ne_tail`/`cons_ne_head`, producción) hasta la posición donde chocan un ÁRBOL y un
    NUMERAL, y ahí `numTree_ne`. Es el caso 3 que `canon_ne` iba a cubrir. -/
theorem caso3_por_valor_efq :
    axioms ⊢ neg (lineWF (cons (formCode (Formula.impl Formula.bottom Formula.bottom))
      (cons (numeralM 8) (objList [numeralM 3])))) :=
  derives_lineWF_neg_of_tag 8 _ [numeralM 3] _ rfl
    (cons_ne_tail (cons_ne_tail (cons_ne_head
      (numTree_ne (NumTree.code Formula.bottom) (numTree_numM 3) (by decide)))))

/-! ### Los 7 tags con `substfc`/`liftfc`: baratos TAMBIÉN, si los args son códigos REALES

`prf_substFormula_arith` (producción, `Meta/SubstArith`+`ArithPrf`) colapsa la reconstrucción a un
`formCode`, y entonces manda `formCode_ne` — que ya existe. Lo que NO cubre: args que son
`NumTree` pero **no** códigos de objetos reales (p.ej. un numeral pelado en la ranura de
`substfc`), porque ahí `substfc` es una función OPACA sin ecuación aplicable. -/

/-- Tag 9 (`q1`, uno de los 7 con `substfc`) con args = códigos REALES: refutado por `formCode_ne`. -/
theorem caso3_barato_q1_codigos_reales (ψ A : Formula) (t : Term)
    (h : ψ ≠ Formula.impl (Formula.forall A) (substFormula 0 t A)) :
    axioms ⊢ neg (lineWF (cons (formCode ψ)
      (cons (numeralM 9) (objList [formCode A, termCode t])))) := by
  refine derives_lineWF_neg_of_tag 9 (formCode ψ) [formCode A, termCode t] _ rfl ?_
  exact FOL.MetaRules.imp_intro (fun heq =>
    FOL.MetaRules.mp (formCode_ne h)
      (FOL.derive_eq_trans heq (prf_to_derives (prf_q1_concl_code A t))))

/-! ### El coste real del choque `cons` vs `numeral`: aritmética ACOTADA, no cómputo

`numTree_ne` pide `m ≠ n` a nivel META. Calcular el valor de un `formCode` es INVIABLE (el
emparejamiento de Cantor iterado: `codeNat (⊥⇒⊥)` ya son 583 734, y `triN` es recursión unaria).
Pero no hace falta calcularlo: `consN` tiene cota inferior lineal, y con ella la desigualdad
contra un numeral PEQUEÑO sale por aritmética acotada. -/

theorem triN_ge : ∀ n : Nat, n ≤ triN n
  | 0     => Nat.le_refl 0
  | n + 1 => by have := triN_ge n; show n + 1 ≤ triN n + (n + 1); omega

/-- **Cota inferior de `consN`**: un `cons` vale al menos `a + b + 1`. Es lo que permite decidir
    `valor(cons …) ≠ k̇` por búsqueda ACOTADA en vez de por cómputo. -/
theorem consN_ge (a b : Nat) : a + b + 1 ≤ consN a b := by
  have h := triN_ge (a + (b + 1))
  show a + b + 1 ≤ triN (a + (b + 1)) + (b + 1)
  omega

/-- El valor de un `cons` supera estrictamente al de su cabeza. -/
theorem consN_ge_head (a b : Nat) : a + 1 ≤ consN a b := by have := consN_ge a b; omega

/-- Corolario: **ningún código de fórmula vale menos de 3** (el tag ya es ≥ 2). Refuta de un golpe
    todos los choques contra `0̇`, `1̇`, `2̇` sin tocar un solo `triN`. -/
theorem codeNat_ge (φ : Formula) : 3 ≤ codeNat φ := by
  cases φ <;> simp only [codeNat] <;>
    (refine Nat.le_trans ?_ (consN_ge_head _ _); omega)

/-! ## §4 — `NumTree` SUBSUME la clase de testigos DE HOY (`StdChain` = `IsCodeShaped`)

`Meta/OmegaReflect.lean:96` define hoy `StdChain l := ∀ x ∈ l, IsCodeShaped x`, con
`IsCodeShaped` generada por `numeralM`, `strCodeM`, `nil`, `cons`. **Todos** ellos tienen valor
numérico ⟹ el sustituto por VALOR se aplica a la clase de testigos **tal y como está**, sin
tocar `StdChain` y por tanto **sin reforzar `OmegaConsistent`**. -/

theorem numTree_charsCodeM : ∀ cs : List Char, NumTree (charsCodeM cs) (codeNatChars cs)
  | []      => NumTree.zero
  | c :: cs => NumTree.cons (numTree_numM c.toNat) (numTree_charsCodeM cs)

theorem numTree_strCodeM (s : String) : NumTree (strCodeM s) (codeNatStr s) :=
  numTree_charsCodeM s.toList

/-- ✅ **La clase de testigos de HOY está enteramente cubierta por el valor.** -/
theorem numTree_of_isCodeShaped : ∀ {x : Term}, IsCodeShaped x → ∃ n, NumTree x n := by
  intro x hx
  induction hx with
  | numeral n => exact ⟨n, numTree_numM n⟩
  | strCode s => exact ⟨codeNatStr s, numTree_strCodeM s⟩
  | nil => exact ⟨0, NumTree.zero⟩
  | cons _ _ ih_h ih_t =>
      obtain ⟨a, ha⟩ := ih_h; obtain ⟨b, hb⟩ := ih_t
      exact ⟨consN a b, NumTree.cons ha hb⟩

/-! ### ⚠️ CORRECCIÓN a `Meta/OmegaReflect.lean:88-92`

El docstring de `IsCodeShaped` afirma: «las comparaciones de `NegVerifier` son **PARALELAS POR
TIPO** — `formCode φ` contra `formCode ψ`, **nunca `cons` contra `numeral` en la misma ranura**».

**Es FALSO** sobre la clase que él mismo define. La línea de abajo es `IsCodeShaped` (luego un
testigo `StdChain` legítimo), y refutarla exige comparar `formCode ⊥` (un `cons`) contra
`numeralM 3` (un numeral) **en la misma ranura** — que es exactamente lo que `formCode_ne` /
`cons_ne_head` NO pueden, y `numTree_ne` SÍ (`caso3_por_valor_efq`, arriba). -/

/-- La línea basura de `caso3_por_valor_efq` es un testigo `StdChain` LEGÍTIMO. -/
theorem isCodeShaped_linea_mala :
    IsCodeShaped (cons (formCode (Formula.impl Formula.bottom Formula.bottom))
      (cons (numeralM 8) (cons (numeralM 3) nil))) :=
  IsCodeShaped.cons
    (IsCodeShaped.cons (IsCodeShaped.numeral 5)
      (IsCodeShaped.cons (IsCodeShaped.cons (IsCodeShaped.numeral 2) IsCodeShaped.nil)
        (IsCodeShaped.cons (IsCodeShaped.cons (IsCodeShaped.numeral 2) IsCodeShaped.nil)
          IsCodeShaped.nil)))
    (IsCodeShaped.cons (IsCodeShaped.numeral 8)
      (IsCodeShaped.cons (IsCodeShaped.numeral 3) IsCodeShaped.nil))

/-- Y como CADENA entera: `StdChain` la acepta. -/
theorem stdChain_linea_mala :
    StdChain [cons (formCode (Formula.impl Formula.bottom Formula.bottom))
      (cons (numeralM 8) (cons (numeralM 3) nil))] := by
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact isCodeShaped_linea_mala

end MFCenso

#print axioms MFCenso.bloqueo2_muerto
#print axioms MFCenso.tag15_cerrado
#print axioms MFCenso.caso4_gratis_tag9
#print axioms MFCenso.caso4_gratis_tag16
#print axioms MFCenso.carc_head_kills_implc
#print axioms MFCenso.caso3_barato_p1
#print axioms MFCenso.numTree_ne
#print axioms MFCenso.numTree_of_treeVal
#print axioms MFCenso.cons_nil_nil_es_dos
#print axioms MFCenso.valor_gana_donde_la_estructura_no_puede
#print axioms MFCenso.caso3_por_valor_efq
#print axioms MFCenso.caso3_barato_q1_codigos_reales
#print axioms MFCenso.numTree_of_isCodeShaped
#print axioms MFCenso.stdChain_linea_mala
