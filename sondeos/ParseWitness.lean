/-
✅ SONDEO POSITIVO (2026-08-24) — **VÍA POR TESTIGO DE PARSEO, FASE A: la arquitectura SALE,
   y sale NET-0**.

Contexto: para tumbar el **muro de `substfc`** (los 7 tags de `lineWF`) hacen falta predicados
de buena-formación `isFormCode`/`isTermCode`. La opción (1) era **sancionarlos como axiomas**
(≈13-15 cláusulas + 7 enmiendas + 2 reflectores mutuamente recursivos). La opción (2), que el
sondeo de julio dejó «ni demostrada ni refutada», es **definirlos en vocabulario EXISTENTE** por
testigo de parseo, como el proyecto ya hizo con `chainOk` ⇝ `chainOkB`
(`prf_chainOk_iff_chainOkB`, `ChainOkBoundedPrf.lean:832`).

Este sondeo mide la fase A de (2). **Cero axiomas nuevos, todo `[propext, choice, Quot.sound]`.**

## Lo que está COMPILADO aquí

| pieza | qué asegura |
|---|---|
| `nodeOk` / `wfAll` / `isFCB` | la definición completa, **12 casos**, en vocabulario existente |
| **`prf_bdAll_numeral`** | **la pieza clave**: `∀i < numeralM n. Φ(i)` desde las `n` instancias concretas |
| `prf_lenc_objList`, `prf_nthc_objList`, `prf_In_objList` | el puente `objList` ⇄ meta |
| `PrfH_congr_nodeOk` | Leibniz sobre el nodo — **UNA** aplicación, no 12 |
| **`prf_wfAll_objList`** | **el ensamblaje**: de «cada elemento es nodo válido» a `wfAll` |
| `prf_isFCB_bottom` | el caso base `⊥`, extremo a extremo |

## Las tres decisiones de diseño que lo abarataron (material del libro)

1. **Pertenencia SIN orden** (`In x w`, no «aparece antes de la posición `i`»). Con orden, cada
   composición de testigos exigiría concatenación + desplazamiento de índices; sin orden,
   componer es gratis. **La buena fundamentación no se pierde**: la da
   `prf_cantor_mono_left/right` (sub-código ESTRICTAMENTE menor), que es lo que alimentará
   `prf_strong_induction` en la fase B.
2. **Las CADENAS no llevan predicado.** `substfc` no recurre en `strCodeM`, así que la casilla
   de símbolo es carga OPACA. Eso elimina de raíz el problema de totalidad de `Char.ofNat`
   (que `sondeos/RecodCoste.lean` había señalado) y borra un predicado entero.
3. **Cero monotonía.** Al probar cada nodo directamente contra la lista COMPLETA (vía
   `prf_In_objList`), nunca hay que transportar `nodeOk w X` a `nodeOk (cons y w) X` — que
   habría costado un or-elim de 12 casos por composición.

## Lo que FALTA para cerrar el hito (i) — es VOLUMEN, no diseño

`subCodes : Formula → List Term` (meta) y la inducción meta sobre `φ` que prueba que cada
elemento de `subCodes φ` es un nodo válido. Cada caso es: leer el tag, `prf_carc_cons`,
`prf_lenc_cons`, y `prf_In_objList` para las pertenencias. El ensamblaje ya está hecho.

## Lo que decide (y lo que NO)

Decide que la vía (2) **no está bloqueada** y que su fase A no necesita axiomas. **NO** decide
la fase B: `pcc_eval_substfc` por inducción fuerte sobre el código, con el testigo dando el
análisis de casos. Ése sigue siendo el trabajo grande, y es común a las dos opciones.

⚠️ `isFCB` **sobre-aproxima** (puede aceptar basura, p.ej. si un numeral coincidiera con un
`cons`). No es problema de solidez: añadir el conjunto **restringe** `lineWF`, luego `Prov`
nunca crece — la dirección opuesta al incidente `ax_lineWF_gen`.

## Cómo re-ejecutarlo

    lake env lean sondeos/ParseWitness.lean
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf

namespace ParseWitness

/-! ## 1 · El nodo bien formado

    ⚠️ **Decisión de diseño medida**: la pertenencia es `In x w` (SIN orden), no
    «aparece antes de la posición `i`». Con orden haría falta el par
    concatenación + desplazamiento de índices en cada composición; sin orden, componer
    testigos es gratis. La buena fundamentación NO se pierde: la da
    `prf_cantor_mono_left/right` (sub-código ESTRICTAMENTE menor), que es lo que alimenta
    `prf_strong_induction` cuando toque `pcc_eval_substfc`.

    ⚠️ Las CADENAS (`strCodeM`) son carga OPACA: `substfc` no recurre en ellas ⇒ no llevan
    predicado. Ahí está media rebaja frente a la vía axiomática. -/

/-- Nodo con `lenc = 1` y sin sub-códigos (sólo `⊥`, tag 2). -/
def nulOk (X : Term) (k : Nat) : Formula :=
  land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 1))

/-- Nodo con `lenc = 2` y UN sub-código en la casilla 1 (tags 6, 9). -/
def unOk (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 2)))
       (In (nthc X (numeralM 1)) w)

/-- Nodo con `lenc = 3` y DOS sub-códigos (tags 4, 5, 7, 8). -/
def binOk (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (land (In (nthc X (numeralM 1)) w) (In (nthc X (numeralM 2)) w))

/-- Nodo con `lenc = 3`, casilla 1 OPACA (cadena) y sub-código en la 2 (tags 1, 3). -/
def strBinOk (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (In (nthc X (numeralM 2)) w)

/-- `var n` (tag 0): `lenc = 2` y la casilla 1 es un NUMERAL, no un sub-código. -/
def varOk (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 0)) (Formula.eq (lenc X) (numeralM 2))

/-- Disyunción asociada a la derecha de una lista NO vacía (evita contar paréntesis). -/
def lorAll : Formula → List Formula → Formula
  | a, []      => a
  | a, b :: bs => lor a (lorAll b bs)

/-- **La disyunción**: `X` es un nodo bien formado con sus sub-códigos en `w`.
    Los 12 casos de `formCodeM`/`termCodeM`/`termsCodeM` (`Minimal/Axioms.lean:562‑589`). -/
def nodeOk (w X : Term) : Formula :=
  lorAll (nulOk X 2)                                -- ⊥
    [ strBinOk w X 3                                -- atom p ts
    , binOk w X 4                                   -- eq t u
    , binOk w X 5                                   -- impl a b
    , unOk  w X 6                                   -- ∀ a
    , binOk w X 7                                   -- ∧ a b
    , binOk w X 8                                   -- ∨ a b
    , unOk  w X 9                                   -- ∃ a
    , varOk X                                       -- var n        (término)
    , strBinOk w X 1                                -- func s ts    (término)
    , Formula.eq X nil                              -- termsCode [] (lista)
    , land (In (carc X) w) (In (cdrc X) w) ]        -- termsCode (t::ts)

/-- `wfAll w` := `∀ i < lenc w. nodeOk w (nthc w i)`. Δ₀ puro, vocabulario EXISTENTE. -/
def wfAll (w : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (nodeOk (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0))))

/-- `isFCB w c` := `w` es un testigo de parseo VÁLIDO y `c` está en él.
    El predicado Σ₁ es `∃w. isFCB w c`; **cero axiomas nuevos**. -/
def isFCB (w c : Term) : Formula := land (wfAll w) (In c w)

/-! ## 2 · EL LEMA GENÉRICO: `∀ i < numeralM n. Φ(i)` desde las `n` instancias concretas

    Con la cota CONCRETA el paso es legítimo (no es la ω-regla): `i < σⁿ0` se descompone en
    `i = 0 ∨ … ∨ i = n-1` iterando `prf_lt_succ_split`. Es la pieza que convierte «probar cada
    posición del testigo» en «probar el `∀` acotado», y era la de viabilidad menos clara. -/

theorem substTerm_numeralM (v : Nat) (s : Term) : ∀ n : Nat,
    substTerm v s (numeralM n) = numeralM n
  | 0     => by simp only [numeralM, zero, substTerm, substTerms]
  | n + 1 => by
      simp only [numeralM, succ, substTerm, substTerms, substTerm_numeralM v s n]

theorem prf_bdAll_numeral (Φ : Formula) (hΦ : substFormula 0 (.var 0) Φ = Φ) : ∀ (n : Nat),
    (∀ k : Nat, k < n → Prf (substFormula 0 (numeralM k) Φ)) →
      Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM n)) Φ))
  | 0, _ => by
      refine Prf.gen _ (prf_deduction ?_)
      exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq Φ))
        (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _)))
  | n + 1, h => by
      have ih := prf_bdAll_numeral Φ hΦ n (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have hself : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) (numeralM n)) Φ)
          = Formula.impl (lt (.var 0) (numeralM n)) Φ := by
        simp only [substFormula, lt, substTerm, substTerms, substTerm_numeralM, hΦ, if_true]
      refine Prf.gen _ (prf_deduction ?_)
      have hsplit : PrfH [lt (.var 0) (numeralM (n + 1))]
          (lor (lt (.var 0) (numeralM n)) (Formula.eq (.var 0) (numeralM n))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) (numeralM n)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      refine PrfH_or_elim hsplit ?brA ?brB
      case brA =>
        exact PrfH.mp _ _ _ (prf_to_prfH (hself ▸ prf_spec ih (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      case brB =>
        have hinst : Prf (substFormula 0 (numeralM n) Φ) := h n (Nat.lt_succ_self n)
        have heq : PrfH (Formula.eq (.var 0) (numeralM n) :: [lt (.var 0) (numeralM (n + 1))])
            (Formula.eq (numeralM n) (.var 0)) :=
          PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _))
        have := PrfH_leibniz_subst (A := Φ) heq (prf_to_prfH hinst _)
        rwa [hΦ] at this

/-! ## 3 · Puente `objList` ⇄ meta: longitud, proyección y pertenencia -/

theorem prf_lenc_objList : ∀ L : List Term,
    Prf (Formula.eq (lenc (objList L)) (numeralM L.length))
  | []      => prf_lenc_nil
  | e :: es =>
      prf_eq_trans (prf_lenc_cons e (objList es)) (prf_eq_congr_succ (prf_lenc_objList es))

theorem prf_nthc_objList : ∀ (L : List Term) (k : Nat) (x : Term), L[k]? = some x →
    Prf (Formula.eq (nthc (objList L) (numeralM k)) x)
  | [],      k,     x, h => by simp at h
  | e :: es, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact prf_nthc_zero e (objList es)
  | e :: es, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact prf_eq_trans (prf_nthc_succ e (objList es) (numeralM k))
        (prf_nthc_objList es k x h)

-- ⚠️ `x ∈ L` NO se puede escribir: con `Minimal.Axioms` abierto, `∈` es el `In` OBJETO
-- (`scoped notation:50 x " ∈ " l => In x l`). Hay que escribir `List.Mem x L`.
theorem prf_In_objList : ∀ (L : List Term) (x : Term), List.Mem x L → Prf (In x (objList L))
  | [],      x, h => by cases h
  | e :: es, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact prf_in_cons_head x (objList es)
      · exact prf_in_cons_tail e (prf_In_objList es x h')

/-! ## 4 · Congruencias objeto que hacen falta -/

theorem PrfH_congr_carc {Γ : List Formula} {t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (carc t₁ =eq carc t₂) := by
  let f : Formula := Formula.eq (carc (liftTerm 0 t₁)) (carc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (carc t₁) (carc s) := by
    intro s
    simp only [f, carc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (carc t₁)) Γ)

theorem PrfH_congr_lenc {Γ : List Formula} {t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (lenc t₁ =eq lenc t₂) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 t₁)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc t₁) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (lenc t₁)) Γ)

/-- Congruencia de `nthc` en el ÍNDICE. -/
theorem PrfH_congr_nthc_idx {Γ : List Formula} {w i₁ i₂ : Term} (h : PrfH Γ (i₁ =eq i₂)) :
    PrfH Γ (nthc w i₁ =eq nthc w i₂) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 w) (liftTerm 0 i₁)) (nthc (liftTerm 0 w) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w i₁) (nthc w s) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS i₂) ▸ PrfH_leibniz_subst (A := f) h ((hS i₁) ▸ prf_to_prfH (prf_refl (nthc w i₁)) Γ)

/-- **Congruencia de `nodeOk` en el nodo `X`** — UNA sola aplicación de Leibniz, no 12.
    Es la lección de `substfc`: sustituir el hueco cubre TODAS sus ocurrencias a la vez. -/
theorem PrfH_congr_nodeOk {Γ : List Formula} {w X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (hN : PrfH Γ (nodeOk w X₁)) : PrfH Γ (nodeOk w X₂) := by
  let f : Formula := nodeOk (liftTerm 0 w) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = nodeOk w s := by
    intro s
    simp only [f, nodeOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
      carc, cdrc, lenc, nthc, nil, zero, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, substTerm_numeralM, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := f) h ((hS X₁) ▸ hN)

/-! ## 5 · Caso base: `⊥` tiene testigo, y sale net-0 -/

def wBot : Term := objList [formCodeM Formula.bottom]

theorem prf_nodeOk_bot (w : Term) : Prf (nodeOk w (formCodeM Formula.bottom)) := by
  have htag : Prf (Formula.eq (carc (formCodeM Formula.bottom)) (numeralM 2)) :=
    prf_carc_cons (numeralM 2) nil
  have hlen : Prf (Formula.eq (lenc (formCodeM Formula.bottom)) (numeralM 1)) :=
    prf_eq_trans (prf_lenc_cons (numeralM 2) nil) (prf_eq_congr_succ prf_lenc_nil)
  have hnul : Prf (nulOk (formCodeM Formula.bottom) 2) := prf_and_intro htag hlen
  unfold nodeOk lorAll
  exact prf_mp (Prf.incl (Prf₀.j1 _ _)) hnul

theorem prf_isFCB_bottom : Prf (isFCB wBot (formCodeM Formula.bottom)) := by
  refine prf_and_intro ?_ (prf_In_objList _ _ (List.Mem.head _))
  refine Prf.gen _ (prf_deduction ?_)
  -- `lenc wBot = σ0` ⇒ el índice sólo puede ser `0` ⇒ el nodo es `formCodeM ⊥`
  have hlift : liftTerm 0 wBot = wBot := by
    simp only [wBot, objList, formCodeM, cons, nil, zero, numeralM, succ, liftTerm, liftTerms]
  rw [hlift]
  have hlen : Prf (Formula.eq (lenc wBot) (numeralM 1)) := prf_lenc_objList _
  have hlt1 : PrfH [lt (.var 0) (lenc wBot)] (lt (.var 0) (succ zero)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (prf_to_prfH hlen _)
      (PrfH.hyp _ _ (List.Mem.head _))
  have hsplit : PrfH [lt (.var 0) (lenc wBot)]
      (lor (lt (.var 0) zero) (Formula.eq (.var 0) zero)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) zero) _) hlt1
  refine PrfH_or_elim hsplit ?brA ?brB
  case brA =>
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _) (PrfH.hyp _ _ (List.Mem.head _)))
  case brB =>
    let Δ : List Formula := Formula.eq (.var 0) zero :: [lt (.var 0) (lenc wBot)]
    have hi : PrfH Δ (Formula.eq (.var 0) zero) := PrfH.hyp _ _ (List.Mem.head _)
    have hX : PrfH Δ (Formula.eq (nthc wBot (.var 0)) (formCodeM Formula.bottom)) :=
      PrfH_eq_trans (PrfH_congr_nthc_idx (w := wBot) hi)
        (prf_to_prfH (prf_nthc_zero (formCodeM Formula.bottom) nil) Δ)
    -- transporte del nodo: UNA Leibniz, el hueco cubre todas sus ocurrencias
    exact PrfH_congr_nodeOk (PrfH_eq_symm hX) (prf_to_prfH (prf_nodeOk_bot wBot) Δ)

/-! ## 6 · EL ENSAMBLAJE: de «cada elemento es un nodo válido» a `wfAll` -/

theorem prf_congr_nodeOk {w X₁ X₂ : Term} (h : Prf (X₁ =eq X₂)) (hN : Prf (nodeOk w X₁)) :
    Prf (nodeOk w X₂) :=
  prfH_nil_to_prf (PrfH_congr_nodeOk (prf_to_prfH h []) (prf_to_prfH hN [])) rfl

/-- **El ensamblaje.** `hcl` dice que el testigo es CERRADO (lo es: se construye con
    `cons`/`nil`/`numeralM`). -/
theorem prf_wfAll_objList (L : List Term)
    (hcl : ∀ s : Term, substTerm 0 s (objList L) = objList L)
    (hlift : liftTerm 0 (objList L) = objList L)
    (h : ∀ (k : Nat) (x : Term), L[k]? = some x → Prf (nodeOk (objList L) x)) :
    Prf (wfAll (objList L)) := by
  let w : Term := objList L
  let Φ : Formula := nodeOk w (nthc w (.var 0))
  have hsub : ∀ s : Term, substFormula 0 s Φ = nodeOk w (nthc w s) := by
    intro s
    simp only [Φ, w, nodeOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
      carc, cdrc, lenc, nthc, nil, zero, substFormula, substTerm, substTerms,
      substTerm_numeralM, hcl, if_true]
  have hΦ : substFormula 0 (.var 0) Φ = Φ := hsub (.var 0)
  -- las `n` instancias concretas
  have hinst : ∀ k : Nat, k < L.length → Prf (substFormula 0 (numeralM k) Φ) := by
    intro k hk
    rw [hsub]
    obtain ⟨x, hx⟩ : ∃ x, L[k]? = some x := ⟨L[k], getElem?_pos L k hk⟩
    exact prf_congr_nodeOk (prf_eq_symm (prf_nthc_objList L k x hx)) (h k x hx)
  have key : Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM L.length)) Φ)) :=
    prf_bdAll_numeral Φ hΦ L.length hinst
  have hself : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) (numeralM L.length)) Φ)
      = Formula.impl (lt (.var 0) (numeralM L.length)) Φ := by
    simp only [substFormula, lt, substTerm, substTerms, substTerm_numeralM, hΦ, if_true]
  have hlift2 : liftTerm 0 (lenc (objList L)) = lenc (objList L) := by
    simp only [lenc, liftTerm, liftTerms, hlift]
  refine Prf.gen _ (prf_deduction ?_)
  rw [hlift2, hlift]
  exact PrfH.mp _ _ _ (prf_to_prfH (hself ▸ prf_spec key (.var 0)) _)
    (ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH (prf_lenc_objList L) _) (PrfH.hyp _ _ (List.Mem.head _)))

end ParseWitness

#print axioms ParseWitness.prf_wfAll_objList
#print axioms ParseWitness.prf_bdAll_numeral
#print axioms ParseWitness.prf_lenc_objList
#print axioms ParseWitness.prf_nthc_objList
#print axioms ParseWitness.prf_In_objList
#print axioms ParseWitness.prf_isFCB_bottom
