/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.SolidezVerificador
import ROBINSON_PlusPlus.Meta.RosserNumEval

/-!
# `Meta/RigidezEstandar.lean` — 🏁 W1 y E10 en TODO modelo estándar (T75e, ADR‑173)

Hasta aquí, `prf_of_prov`, `modelo_prov_iff`, `godelCN_verdadera` y `con_verdadera` (`Meta/SolidezVerificador.lean`)
valían sólo para `MNV V₀`, el modelo construido. Aquí valen para TODO `M` con `Estandar M` (`Meta/SolidezPrf.lean`):
el dominio es `Nat`, `0`, `σ` y `::` son los de verdad, y valen los 142.

**Por qué no es inmediato.** Las ecuaciones de codificación sólo hablan de códigos con forma (`varc`, `funcc`,
`botc`…); sobre la basura, `M` es LIBRE (puede no ser `MNV V₀`). Lo que lo salva son las GUARDAS de ADR‑020: las
reglas de `lineWF` que sustituyen piden `hasWitF`/`hasWit` de sus argumentos, y las guardas significan lo mismo en `M`
que en `MNV`.

* **§1–§3 · Lo que los axiomas fijan del todo**: los numerales y los códigos de cadena, `+`, `<`, `∈`, `lenc`, `##`,
  `tcFn`; y `carc`, `cdrc` y `nthc` donde los fijan (sobre un `cons`; `nthc` en rango).
* **§4 · Las guardas** (`M_hasWit`, `M_hasWitF`): `M ⊨ hasWit t` sii el valor de `t` es un código de término de
  verdad, y lo mismo para las fórmulas. Lo que miran fuera de rango no cuenta: la forma ya lo descarta.
* **§5 · La sustitución y el lift sobre los códigos BUENOS** (`CodT`/`CodF` de `Meta/RosserNumEval.lean`, que son las
  guardas): por inducción sobre el código, valen lo de `MNV`.
* **§6–§7 · Los códigos cerrados, y el ancla**: `axiomsCodeT` vale en `M` el código de los 142 (el ancla es teorema y
  `M` es sólida).
* **§8–§10 · `lineWF`, las premisas, la cadena y `runFn`**: si `M` cree que `p` es una prueba, lo es, etiqueta por
  etiqueta (las 21), con el `V` del ancla.
* **§11 · 🏁** `prf_of_prov_de`, `modelo_prov_iff_de`, `godelCN_verdadera_de` y `con_verdadera_de`: lo que `M` cree
  demostrable lo es; `Prov` es fiel en `M`; `G` y `Con` son VERDADERAS en `M`. Las de `SolidezVerificador` son la
  instancia en `MNV V₀` (`estandar_MN`), que también es el control de que la hipótesis no es vacía.
* **§12 · ⛔ El control del ANCLA** (`control_ancla`, T75b, ADR‑175): sin el ancla, `Prov` puede mentir. `MNV V⊥`, con
  `V⊥` la lista del código de `⊥` sola, satisface los 141 de la base y cree demostrable `⊥` (una cadena de una línea
  `thy`), así que `Con` es FALSA en él; y el ancla falla, sin evaluar su numeral: si valiera, `MNV V⊥` sería estándar
  y `con_verdadera_de` haría verdadera `Con`.

⚠️ Lo que NO dice: que `M` sea `MNV V₀`. Sobre la basura (un código sin forma, `nthc` fuera de rango, `carc` de `0`)
`M` puede ser otro: lo que se demuestra es que no importa, porque ni las guardas ni las cadenas que `M` cree pruebas la
miran. Que de verdad puede ser otro lo enseña `Meta/SegundoModelo.lean` (T75d, ADR‑175): un modelo estándar que
difiere de `MNV V₀` en `substfc` sobre la basura.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open FOL FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.SolidezPrf

namespace ROBINSON_PlusPlus.Meta.RigidezEstandar

variable {M : Model Nat}

theorem ax_de (hM : Estandar M) {φ : Formula} (h : φ ∈ axioms) (v : Nat → Nat) : evalFormula M v φ :=
  hM.haxs v φ h

/-! ## §1 · Los códigos cerrados -/

theorem M_numeral (hM : Estandar M) (v : Nat → Nat) : ∀ n : Nat, evalTerm M v (numeralM n) = n
  | 0 => by simp [numeralM, zero, evalTerm, evalTerms, hM.hzero]
  | n + 1 => by simp [numeralM, succ, evalTerm, evalTerms, hM.hsucc, M_numeral hM v n]

theorem M_chars (hM : Estandar M) (v : Nat → Nat) : ∀ cs : List Char, evalTerm M v (charsCodeM cs) = codeNatChars cs
  | [] => by simp [charsCodeM, nil, zero, evalTerm, evalTerms, hM.hzero, codeNatChars]
  | c :: cs => by
      simp [charsCodeM, cons, evalTerm, evalTerms, hM.hcons, M_numeral hM v, M_chars hM v cs, codeNatChars]

theorem M_str (hM : Estandar M) (v : Nat → Nat) (s : List Char) : evalTerm M v (strCodeM s) = codeNatStr s := by
  simp [strCodeM, M_chars hM v, codeNatStr]

/-! ## §2 · La aritmética que miran las guardas: `+` y `<` -/

/-- `+` es la suma: `ax4`, `ax5` y la inducción sobre el segundo sumando. -/
theorem M_add (hM : Estandar M) (a b : Nat) : M.func add_sym [a, b] = a + b := by
  induction b with
  | zero =>
    have h := ax_de hM (φ := ax4_add_zero) (by simp [axioms]) (fun _ => 0) a
    simpa [ax4_add_zero, forall_, add, zero, evalFormula, evalTerm, evalTerms, shiftEnv, hM.hzero] using h
  | succ b ih =>
    have h := ax_de hM (φ := ax5_add_succ) (by simp [axioms]) (fun _ => 0) a b
    simp [forall_2, add, succ, evalFormula, evalTerm, evalTerms, shiftEnv, hM.hsucc] at h
    rw [h, ih]; omega

/-- `<` es el orden: `ax13` (`n < m ⇔ ∃k, n + σk = m`) con `+` rígido. -/
theorem M_lt (hM : Estandar M) (a b : Nat) : M.rel lt_sym [a, b] ↔ a < b := by
  have h := ax_de hM (φ := ax13_lt_def) (by simp [axioms]) (fun _ => 0) a b
  simp [ax13_lt_def, forall_2, _root_.iff, lt, add, succ, ex, evalFormula, evalTerm, evalTerms, shiftEnv, hM.hsucc,
    M_add hM] at h
  constructor
  · intro hp; obtain ⟨d, hd⟩ := h.1 hp; omega
  · intro hab; exact h.2 (b - a - 1) (by omega)

/-! ## §3 · Las listas: `∈`, `lenc`, `##`, y `carc`/`cdrc`/`nthc` donde los fijan los axiomas -/

theorem M_carc (hM : Estandar M) (a b : Nat) : M.func sym!"carc" [consN a b] = a := by
  have h := ax_de hM (φ := ax_carc) (by simp [axioms]) (fun _ => 0) a b
  simpa [ax_carc, forall_2, carc, cons, evalFormula, evalTerm, evalTerms, shiftEnv, hM.hcons] using h

theorem M_cdrc (hM : Estandar M) (a b : Nat) : M.func sym!"cdrc" [consN a b] = b := by
  have h := ax_de hM (φ := ax_cdrc) (by simp [axioms]) (fun _ => 0) a b
  simpa [ax_cdrc, forall_2, cdrc, cons, evalFormula, evalTerm, evalTerms, shiftEnv, hM.hcons] using h

/-- Toda lista no vacía es un `consN`, y su cola es menor. -/
theorem consN_de {l : Nat} (h : ¬ l = 0) : ∃ a b, And (l = consN a b) (b < l) :=
  ⟨carN l, cdrN l, (consN_car_cdr h).symm, cdrN_lt h⟩

theorem M_mem (hM : Estandar M) : ∀ (l x : Nat), M.rel in_sym [x, l] ↔ memN x l := by
  intro l
  induction l using Nat.strongRecOn with
  | ind l ih =>
    intro x
    by_cases hl : l = 0
    · subst hl
      have h := ax_de hM (φ := ax_L1_in_nil) (by simp [axioms]) (fun _ => 0) x
      simp [ax_L1_in_nil, forall_, neg, In, nil, zero, evalFormula, evalTerm, evalTerms, shiftEnv, hM.hzero] at h
      simp [h, memN_zero]
    · obtain ⟨a, b, rfl, hb⟩ := consN_de hl
      have h := ax_de hM (φ := ax_L2_in_cons) (by simp [axioms]) (fun _ => 0) x a b
      simp [ax_L2_in_cons, forall_3, _root_.iff, In, cons, lor, evalFormula, evalTerm, evalTerms, shiftEnv,
        hM.hcons] at h
      rw [show M.rel in_sym [x, consN a b] ↔ Or (x = a) (M.rel in_sym [x, b]) from ⟨h.1, h.2⟩,
        memN_consN, ih b hb x]

theorem M_lenc (hM : Estandar M) : ∀ l : Nat, M.func sym!"lenc" [l] = lenN l := by
  intro l
  induction l using Nat.strongRecOn with
  | ind l ih =>
    by_cases hl : l = 0
    · subst hl
      have h := ax_de hM (φ := ax_lenc_nil) (by simp [axioms]) (fun _ => 0)
      simpa [ax_lenc_nil, lenc, nil, zero, evalFormula, evalTerm, evalTerms, hM.hzero, lenN_zero] using h
    · obtain ⟨a, b, rfl, hb⟩ := consN_de hl
      have h := ax_de hM (φ := ax_lenc_cons) (by simp [axioms]) (fun _ => 0) a b
      simp [ax_lenc_cons, forall_2, lenc, cons, succ, evalFormula, evalTerm, evalTerms, shiftEnv,
        hM.hcons, hM.hsucc] at h
      rw [h, ih b hb, lenN_consN]

/-- `nthc` en RANGO: `ax_nthc_zero` y `ax_nthc_succ`. (Fuera de rango, sobre `nil`, ningún axioma lo fija.) -/
theorem M_nthc (hM : Estandar M) : ∀ (i l : Nat), i < lenN l → M.func sym!"nthc" [l, i] = nthN l i := by
  intro i
  induction i with
  | zero =>
    intro l hi
    have hl : ¬ l = 0 := by intro h; subst h; simp [lenN_zero] at hi
    obtain ⟨a, b, rfl, _⟩ := consN_de hl
    have h := ax_de hM (φ := ax_nthc_zero) (by simp [axioms]) (fun _ => 0) a b
    simp [ax_nthc_zero, forall_2, nthc, cons, zero, evalFormula, evalTerm, evalTerms, shiftEnv,
      hM.hcons, hM.hzero] at h
    rw [h, nthN_cz]
  | succ i ih =>
    intro l hi
    have hl : ¬ l = 0 := by intro h; subst h; simp [lenN_zero] at hi
    obtain ⟨a, b, rfl, _⟩ := consN_de hl
    have h := ax_de hM (φ := ax_nthc_succ) (by simp [axioms]) (fun _ => 0) a b i
    simp [ax_nthc_succ, forall_3, nthc, cons, succ, evalFormula, evalTerm, evalTerms, shiftEnv,
      hM.hcons, hM.hsucc] at h
    rw [lenN_consN] at hi
    rw [h, nthN_cs, ih b (by omega)]

theorem M_concat (hM : Estandar M) : ∀ a b : Nat, M.func concat_sym [a, b] = concatN a b := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b
    by_cases ha : a = 0
    · subst ha
      have h := ax_de hM (φ := ax_C1_concat_nil) (by simp [axioms]) (fun _ => 0) b
      simpa [ax_C1_concat_nil, forall_, concat, nil, zero, evalFormula, evalTerm, evalTerms, shiftEnv,
        hM.hzero, concatN_zero] using h
    · obtain ⟨x, r, rfl, hr⟩ := consN_de ha
      have h := ax_de hM (φ := ax_C2_concat_cons) (by simp [axioms]) (fun _ => 0) x r b
      simp [ax_C2_concat_cons, forall_3, concat, cons, evalFormula, evalTerm, evalTerms, shiftEnv,
        hM.hcons] at h
      rw [h, ih r hr b, concatN_consN]

/-- `tcFn` sobre todo `Nat`: `ax_tc_zero` y `ax_tc_succ`. -/
theorem M_tcFn (hM : Estandar M) : ∀ n : Nat, M.func sym!"tcFn" [n] = tcFnN n := by
  intro n
  induction n with
  | zero =>
    have h := ax_de hM (φ := ax_tc_zero) (by simp [axioms]) (fun _ => 0)
    simp [ax_tc_zero, tcFn, cons, nil, zero, evalFormula, evalTerm, evalTerms, hM.hcons, hM.hzero,
      M_numeral hM, M_str hM] at h
    rw [h, tcFnN]
  | succ n ih =>
    have h := ax_de hM (φ := ax_tc_succ) (by simp [axioms]) (fun _ => 0) n
    simp [ax_tc_succ, forall_, tcFn, cons, nil, zero, succ, evalFormula, evalTerm, evalTerms, shiftEnv,
      hM.hcons, hM.hzero, hM.hsucc, M_numeral hM, M_str hM] at h
    rw [h, ih, tcFnN]



/-! ## §4 · Las GUARDAS significan lo mismo en `M` que en `MNV` -/

theorem M_lift0 (v : Nat → Nat) (d : Nat) (t : Term) :
    evalTerm M (shiftEnv v d) (liftTerm 0 t) = evalTerm M v t := by
  have h := eval_liftTerm_ext M v d 0 t
  have heq : updateEnv 0 v d = shiftEnv v d := by funext n; exact updateEnv_zero v d n
  rw [heq] at h; exact h

theorem nth_forma1 {x a y : Nat} (h : x = consN a (consN y 0)) : nthN x 1 = y := by rw [h, nthN_cs, nthN_cz]
theorem len_forma1 {x a y : Nat} (h : x = consN a (consN y 0)) : lenN x = 2 := by
  rw [h, lenN_consN, lenN_consN, lenN_zero]
theorem nth1_forma2 {x a y z : Nat} (h : x = consN a (consN y (consN z 0))) : nthN x 1 = y := by
  rw [h, nthN_cs, nthN_cz]
theorem nth2_forma2 {x a y z : Nat} (h : x = consN a (consN y (consN z 0))) : nthN x 2 = z := by
  rw [h, nthN_cs, nthN_cs, nthN_cz]
theorem len_forma2 {x a y z : Nat} (h : x = consN a (consN y (consN z 0))) : lenN x = 3 := by
  rw [h, lenN_consN, lenN_consN, lenN_consN, lenN_zero]

/-- La forma UNARIA: con el `nthc` de `M` o con el de verdad, es lo mismo (si `x` tiene la forma, está en rango). -/
theorem forma1_iff (hM : Estandar M) (x k : Nat) :
    x = consN k (consN (M.func sym!"nthc" [x, 1]) 0) ↔ x = consN k (consN (nthN x 1) 0) := by
  constructor
  · intro h
    generalize hy : M.func sym!"nthc" [x, 1] = y at h
    rw [nth_forma1 h]; exact h
  · intro h
    rw [M_nthc hM 1 x (by rw [len_forma1 h]; omega)]; exact h

/-- La forma BINARIA, igual. -/
theorem forma2_iff (hM : Estandar M) (x k : Nat) :
    x = consN k (consN (M.func sym!"nthc" [x, 1]) (consN (M.func sym!"nthc" [x, 2]) 0)) ↔
      x = consN k (consN (nthN x 1) (consN (nthN x 2) 0)) := by
  constructor
  · intro h
    generalize hy : M.func sym!"nthc" [x, 1] = y at h
    generalize hz : M.func sym!"nthc" [x, 2] = z at h
    rw [nth1_forma2 h, nth2_forma2 h]; exact h
  · intro h
    have hl := len_forma2 h
    rw [M_nthc hM 1 x (by omega), M_nthc hM 2 x (by omega)]; exact h

/-- «todas las posiciones de `y` están en `w`», con el `nthc` de `M`: en rango, el de verdad. -/
theorem argsIn_iff (hM : Estandar M) (w y : Nat) :
    (∀ j, j < lenN y → memN (M.func sym!"nthc" [y, j]) w) ↔ argsInN w y := by
  constructor
  · intro h j hj; rw [← M_nthc hM j y hj]; exact h j hj
  · intro h j hj; rw [M_nthc hM j y hj]; exact h j hj

/-- Un código de TÉRMINO (una casilla del testigo), con el `nthc` de `M`, es uno de verdad. -/
theorem isTC_iff (hM : Estandar M) (w x : Nat) :
    (Or (x = consN 0 (consN (M.func sym!"nthc" [x, 1]) 0))
      (And (x = consN 1 (consN (M.func sym!"nthc" [x, 1]) (consN (M.func sym!"nthc" [x, 2]) 0)))
        (∀ j, j < lenN (M.func sym!"nthc" [x, 2]) →
          memN (M.func sym!"nthc" [M.func sym!"nthc" [x, 2], j]) w))) ↔ isTermCodeE1N w x := by
  rw [forma1_iff hM, isTermCodeE1N, shapeUnN, shapeBinN, argsInN]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨h2, ha⟩
    have h2' := (forma2_iff hM x 1).1 h2
    refine ⟨h2', ?_⟩
    rw [← M_nthc hM 2 x (by rw [len_forma2 h2']; omega)]
    exact (argsIn_iff hM w _).1 ha
  · rintro ⟨h2', ha⟩
    refine ⟨(forma2_iff hM x 1).2 h2', ?_⟩
    rw [M_nthc hM 2 x (by rw [len_forma2 h2']; omega)]
    exact (argsIn_iff hM w _).2 ha

theorem wfAll1_iff (hM : Estandar M) (w : Nat) :
    (∀ i, i < lenN w →
      Or (M.func sym!"nthc" [w, i] = consN 0 (consN (M.func sym!"nthc" [M.func sym!"nthc" [w, i], 1]) 0))
        (And (M.func sym!"nthc" [w, i] = consN 1 (consN (M.func sym!"nthc" [M.func sym!"nthc" [w, i], 1])
              (consN (M.func sym!"nthc" [M.func sym!"nthc" [w, i], 2]) 0)))
          (∀ j, j < lenN (M.func sym!"nthc" [M.func sym!"nthc" [w, i], 2]) →
            memN (M.func sym!"nthc" [M.func sym!"nthc" [M.func sym!"nthc" [w, i], 2], j]) w))) ↔
      wfAll1N w := by
  constructor
  · intro h i hi; rw [← M_nthc hM i w hi]; exact (isTC_iff hM w _).1 (h i hi)
  · intro h i hi; exact (isTC_iff hM w _).2 (by rw [M_nthc hM i w hi]; exact h i hi)

/-- 🏁 **La guarda de TÉRMINO significa lo mismo en `M`**: `M ⊨ hasWit t` sii el valor de `t` es el código de un
    término (en el sentido de `hasWitN`, el de `MNV`). -/
theorem M_hasWit (hM : Estandar M) (v : Nat → Nat) (t : Term) :
    evalFormula M v (hasWit t) ↔ hasWitN (evalTerm M v t) := by
  simp only [hasWit, isTC1, wfAll1, wfAll1Body, isTermCodeE1, shapeUn, shapeBin, argsIn, argsInBody,
    land, lor, lt, In, lenc, nthc, cons, nil, zero,
    evalFormula, evalTerm, evalTerms, shiftEnv, liftTerm, liftTerms, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add,
    ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM, M_lift0, M_numeral hM,
    M_lt hM, M_mem hM, M_lenc hM, hM.hcons, hM.hzero]
  rw [hasWitN]
  exact exists_congr (fun w => and_congr (wfAll1_iff hM w) Iff.rfl)



/-- Con la forma binaria (en `M` o de verdad), las dos casillas valen lo mismo con los dos `nthc`. -/
theorem forma2_and (hM : Estandar M) (x k : Nat) (P : Nat → Nat → Prop) :
    And (x = consN k (consN (M.func sym!"nthc" [x, 1]) (consN (M.func sym!"nthc" [x, 2]) 0)))
        (P (M.func sym!"nthc" [x, 1]) (M.func sym!"nthc" [x, 2])) ↔
      And (shapeBinN x k) (P (nthN x 1) (nthN x 2)) := by
  rw [shapeBinN]
  constructor
  · rintro ⟨h, hp⟩
    have h' := (forma2_iff hM x k).1 h
    have hl := len_forma2 h'
    rw [M_nthc hM 1 x (by omega), M_nthc hM 2 x (by omega)] at hp
    exact ⟨h', hp⟩
  · rintro ⟨h', hp⟩
    have hl := len_forma2 h'
    refine ⟨(forma2_iff hM x k).2 h', ?_⟩
    rw [M_nthc hM 1 x (by omega), M_nthc hM 2 x (by omega)]; exact hp

theorem forma1_and (hM : Estandar M) (x k : Nat) (P : Nat → Prop) :
    And (x = consN k (consN (M.func sym!"nthc" [x, 1]) 0)) (P (M.func sym!"nthc" [x, 1])) ↔
      And (shapeUnN x k) (P (nthN x 1)) := by
  rw [shapeUnN]
  constructor
  · rintro ⟨h, hp⟩
    have h' := (forma1_iff hM x k).1 h
    rw [M_nthc hM 1 x (by rw [len_forma1 h']; omega)] at hp
    exact ⟨h', hp⟩
  · rintro ⟨h', hp⟩
    refine ⟨(forma1_iff hM x k).2 h', ?_⟩
    rw [M_nthc hM 1 x (by rw [len_forma1 h']; omega)]; exact hp

theorem clAtom_iff (hM : Estandar M) (wT x : Nat) :
    And (x = consN 3 (consN (M.func sym!"nthc" [x, 1]) (consN (M.func sym!"nthc" [x, 2]) 0)))
      (∀ j, j < lenN (M.func sym!"nthc" [x, 2]) → memN (M.func sym!"nthc" [M.func sym!"nthc" [x, 2], j]) wT) ↔
      clAtomN wT x := by
  rw [forma2_and hM x 3 (fun _ b => ∀ j, j < lenN b → memN (M.func sym!"nthc" [b, j]) wT), clAtomN, argsIn_iff hM]

theorem clEq_iff (hM : Estandar M) (wT x : Nat) :
    And (x = consN 4 (consN (M.func sym!"nthc" [x, 1]) (consN (M.func sym!"nthc" [x, 2]) 0)))
      (And (memN (M.func sym!"nthc" [x, 1]) wT) (memN (M.func sym!"nthc" [x, 2]) wT)) ↔ clEqN wT x := by
  rw [forma2_and hM x 4 (fun a b => And (memN a wT) (memN b wT)), clEqN]

theorem clBin_iff (hM : Estandar M) (wF x k : Nat) :
    And (x = consN k (consN (M.func sym!"nthc" [x, 1]) (consN (M.func sym!"nthc" [x, 2]) 0)))
      (And (memN (M.func sym!"nthc" [x, 1]) wF) (memN (M.func sym!"nthc" [x, 2]) wF)) ↔ clBinN wF x k := by
  rw [forma2_and hM x k (fun a b => And (memN a wF) (memN b wF)), clBinN]

theorem clUn_iff (hM : Estandar M) (wF x k : Nat) :
    And (x = consN k (consN (M.func sym!"nthc" [x, 1]) 0)) (memN (M.func sym!"nthc" [x, 1]) wF) ↔
      clUnN wF x k := by
  rw [forma1_and hM x k (fun a => memN a wF), clUnN]

theorem wfAllF_iff (hM : Estandar M) (wF wT : Nat) :
    (∀ i, i < lenN wF →
      Or (M.func sym!"nthc" [wF, i] = consN 2 0) (Or (clAtomN wT (M.func sym!"nthc" [wF, i]))
        (Or (clEqN wT (M.func sym!"nthc" [wF, i])) (Or (clBinN wF (M.func sym!"nthc" [wF, i]) 5)
          (Or (clUnN wF (M.func sym!"nthc" [wF, i]) 6) (Or (clBinN wF (M.func sym!"nthc" [wF, i]) 7)
            (Or (clBinN wF (M.func sym!"nthc" [wF, i]) 8) (clUnN wF (M.func sym!"nthc" [wF, i]) 9)))))))) ↔
      wfAllFN wF wT := by
  constructor
  · intro h i hi; have := h i hi; rw [M_nthc hM i wF hi] at this; exact this
  · intro h i hi; rw [M_nthc hM i wF hi]; exact h i hi


/-- 🏁 **La guarda de FÓRMULA significa lo mismo en `M`.** -/
theorem M_hasWitF (hM : Estandar M) (v : Nat → Nat) (t : Term) :
    evalFormula M v (hasWitF t) ↔ hasWitFN (evalTerm M v t) := by
  simp only [hasWitF, isFC1, wfAll1, wfAll1Body, isTermCodeE1, shapeUn, shapeBin, shapeNul, argsIn, argsInBody,
    wfAllF, wfAllFBody, isFormCodeE2, lorAll, clBot, clAtom, clEq, clBin, clUn,
    land, lor, lt, In, lenc, nthc, cons, nil, zero,
    evalFormula, evalTerm, evalTerms, shiftEnv, liftTerm, liftTerms, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add,
    ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM, M_lift0, M_numeral hM,
    M_lt hM, M_mem hM, M_lenc hM, hM.hcons, hM.hzero]
  simp only [wfAll1_iff hM, clAtom_iff hM, clEq_iff hM, clBin_iff hM, clUn_iff hM]
  simp only [wfAllF_iff hM, hasWitFN]



/-! ## §5 · La sustitución y el lift, sobre los códigos BUENOS (`CodT`, `CodF`, ⇔ las guardas)

Las ecuaciones de codificación sólo hablan de códigos con forma (`varc`, `funcc`, `botc`…): sobre la basura, `M` es
libre. Sobre un código bueno, valen lo mismo que en `MNV`, por inducción sobre el código. -/

open ROBINSON_PlusPlus.Meta.RosserNumEval (CodT CodTs CodF codT_liftcN)

theorem M_pred (hM : Estandar M) (n : Nat) : M.func pred_sym [n] = n - 1 := by
  cases n with
  | zero =>
    have h := ax_de hM (φ := ax25_pred_zero) (by simp [axioms]) (fun _ => 0)
    simpa [ax25_pred_zero, pred, zero, evalFormula, evalTerm, evalTerms, hM.hzero] using h
  | succ n =>
    have h := ax_de hM (φ := ax26_pred_succ) (by simp [axioms]) (fun _ => 0) n
    simpa [ax26_pred_succ, forall_, pred, succ, evalFormula, evalTerm, evalTerms, shiftEnv, hM.hsucc] using h

mutual
theorem M_substtc (hM : Estandar M) {c : Nat} (h : CodT c) (k s : Nat) :
    M.func sym!"substtc" [k, s, c] = substtcN k s c :=
  match h with
  | .var n => by
      rw [substtcN_var]
      rcases Nat.lt_trichotomy k n with hkn | rfl | hkn
      · have h := ax_de hM (φ := ax_substtc_var_gt) (by simp [axioms]) (fun _ => 0) k s n
        simp [ax_substtc_var_gt, forall_3, substtc, varc, cons, nil, zero, pred, lt, evalFormula, evalTerm,
          evalTerms, shiftEnv, hM.hcons, hM.hzero, M_lt hM, M_pred hM] at h
        rw [h hkn, ite_eq_right (by omega), ite_eq_left hkn]
      · have h := ax_de hM (φ := ax_substtc_var_eq) (by simp [axioms]) (fun _ => 0) k s k
        simp [ax_substtc_var_eq, forall_3, substtc, varc, cons, nil, zero, evalFormula, evalTerm,
          evalTerms, shiftEnv, hM.hcons, hM.hzero] at h
        rw [h, ite_eq_left rfl]
      · have h := ax_de hM (φ := ax_substtc_var_lt) (by simp [axioms]) (fun _ => 0) k s n
        simp [ax_substtc_var_lt, forall_3, substtc, varc, cons, nil, zero, lt, evalFormula, evalTerm,
          evalTerms, shiftEnv, hM.hcons, hM.hzero, M_lt hM] at h
        rw [h hkn, ite_eq_right (by omega), ite_eq_right (by omega)]
  | .func sc ts hts => by
      have h := ax_de hM (φ := ax_substtc_func) (by simp [axioms]) (fun _ => 0) k s sc ts
      simp [ax_substtc_func, forall_4, substtc, substtsc, funcc, cons, nil, zero, succ, evalFormula, evalTerm,
        evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
      rw [h, M_substtsc hM hts k s, substtcN_func]
theorem M_substtsc (hM : Estandar M) {ts : Nat} (h : CodTs ts) (k s : Nat) :
    M.func sym!"substtsc" [k, s, ts] = substtscN k s ts :=
  match h with
  | .nil => by
      have h := ax_de hM (φ := ax_substtsc_nil) (by simp [axioms]) (fun _ => 0) k s
      simp [ax_substtsc_nil, forall_2, substtsc, nil, zero, evalFormula, evalTerm, evalTerms, shiftEnv,
        hM.hzero] at h
      rw [h, substtscN_zero]
  | .cons a r ha hr => by
      have h := ax_de hM (φ := ax_substtsc_cons) (by simp [axioms]) (fun _ => 0) k s a r
      simp [ax_substtsc_cons, forall_4, substtsc, substtc, cons, evalFormula, evalTerm, evalTerms, shiftEnv,
        hM.hcons] at h
      rw [h, M_substtc hM ha k s, M_substtsc hM hr k s, substtscN_consN]
end

mutual
theorem M_liftc (hM : Estandar M) {t : Nat} (h : CodT t) (c : Nat) :
    M.func sym!"liftc" [c, t] = liftcN c t :=
  match h with
  | .var n => by
      rw [liftcN_var]
      by_cases hn : n < c
      · have h := ax_de hM (φ := ax_liftc_var_lt) (by simp [axioms]) (fun _ => 0) c n
        simp [ax_liftc_var_lt, forall_2, liftc, varc, cons, nil, zero, lt, evalFormula, evalTerm,
          evalTerms, shiftEnv, hM.hcons, hM.hzero, M_lt hM] at h
        rw [h hn, ite_eq_left hn]
      · have h := ax_de hM (φ := ax_liftc_var_ge) (by simp [axioms]) (fun _ => 0) c n
        simp [ax_liftc_var_ge, forall_2, liftc, varc, cons, nil, zero, succ, lt, evalFormula, evalTerm,
          evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc, M_lt hM] at h
        rw [h (by omega), ite_eq_right hn]
  | .func sc ts hts => by
      have h := ax_de hM (φ := ax_liftc_func) (by simp [axioms]) (fun _ => 0) c sc ts
      simp [ax_liftc_func, forall_3, liftc, liftsc, funcc, cons, nil, zero, succ, evalFormula, evalTerm,
        evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
      rw [h, M_liftsc hM hts c, liftcN_func]
theorem M_liftsc (hM : Estandar M) {ts : Nat} (h : CodTs ts) (c : Nat) :
    M.func sym!"liftsc" [c, ts] = liftscN c ts :=
  match h with
  | .nil => by
      have h := ax_de hM (φ := ax_liftsc_nil) (by simp [axioms]) (fun _ => 0) c
      simp [ax_liftsc_nil, forall_, liftsc, nil, zero, evalFormula, evalTerm, evalTerms, shiftEnv,
        hM.hzero] at h
      rw [h, liftscN_zero]
  | .cons a r ha hr => by
      have h := ax_de hM (φ := ax_liftsc_cons) (by simp [axioms]) (fun _ => 0) c a r
      simp [ax_liftsc_cons, forall_3, liftsc, liftc, cons, evalFormula, evalTerm, evalTerms, shiftEnv,
        hM.hcons] at h
      rw [h, M_liftc hM ha c, M_liftsc hM hr c, liftscN_consN]
end



/-- `substfc`, sobre un código de fórmula bueno y un sustituyendo bueno (el que piden las guardas). -/
theorem M_substfc (hM : Estandar M) {A : Nat} (h : CodF A) :
    ∀ (k s : Nat), CodT s → M.func sym!"substfc" [k, s, A] = substfcN k s A := by
  induction h with
  | bot =>
    intro k s _
    have h := ax_de hM (φ := ax_substfc_bottom) (by simp [axioms]) (fun _ => 0) k s
    simp [ax_substfc_bottom, forall_2, substfc, botc, cons, nil, zero, succ, evalFormula, evalTerm, evalTerms,
      shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, substfcN_bot]
  | atom p ts hts =>
    intro k s _
    have h := ax_de hM (φ := ax_substfc_atom) (by simp [axioms]) (fun _ => 0) k s p ts
    simp [ax_substfc_atom, forall_4, substfc, substtsc, atomc, cons, nil, zero, succ, evalFormula, evalTerm,
      evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, M_substtsc hM hts k s, substfcN_atom]
  | eq a b ha hb =>
    intro k s _
    have h := ax_de hM (φ := ax_substfc_eq) (by simp [axioms]) (fun _ => 0) k s a b
    simp [ax_substfc_eq, forall_4, substfc, substtc, eqc, cons, nil, zero, succ, evalFormula, evalTerm,
      evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, M_substtc hM ha k s, M_substtc hM hb k s, substfcN_eq]
  | impl a b _ _ iha ihb =>
    intro k s hs
    have h := ax_de hM (φ := ax_substfc_impl) (by simp [axioms]) (fun _ => 0) k s a b
    simp [ax_substfc_impl, forall_4, substfc, implc, cons, nil, zero, succ, evalFormula, evalTerm,
      evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, iha k s hs, ihb k s hs, substfcN_impl]
  | all a _ iha =>
    intro k s hs
    have h := ax_de hM (φ := ax_substfc_forall) (by simp [axioms]) (fun _ => 0) k s a
    simp [ax_substfc_forall, forall_3, substfc, liftc, forallc, cons, nil, zero, succ, evalFormula, evalTerm,
      evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, M_liftc hM hs 0, iha (k + 1) (liftcN 0 s) (codT_liftcN hs 0), substfcN_forall]
  | and a b _ _ iha ihb =>
    intro k s hs
    have h := ax_de hM (φ := ax_substfc_and) (by simp [axioms]) (fun _ => 0) k s a b
    simp [ax_substfc_and, forall_4, substfc, andc, cons, nil, zero, succ, evalFormula, evalTerm,
      evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, iha k s hs, ihb k s hs, substfcN_and]
  | or a b _ _ iha ihb =>
    intro k s hs
    have h := ax_de hM (φ := ax_substfc_or) (by simp [axioms]) (fun _ => 0) k s a b
    simp [ax_substfc_or, forall_4, substfc, orc, cons, nil, zero, succ, evalFormula, evalTerm,
      evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, iha k s hs, ihb k s hs, substfcN_or]
  | ex a _ iha =>
    intro k s hs
    have h := ax_de hM (φ := ax_substfc_ex) (by simp [axioms]) (fun _ => 0) k s a
    simp [ax_substfc_ex, forall_3, substfc, liftc, exc, cons, nil, zero, succ, evalFormula, evalTerm,
      evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, M_liftc hM hs 0, iha (k + 1) (liftcN 0 s) (codT_liftcN hs 0), substfcN_ex]

/-- `liftfc`, sobre un código de fórmula bueno. -/
theorem M_liftfc (hM : Estandar M) {A : Nat} (h : CodF A) : ∀ c : Nat, M.func sym!"liftfc" [c, A] = liftfcN c A := by
  induction h with
  | bot =>
    intro c
    have h := ax_de hM (φ := ax_liftfc_bottom) (by simp [axioms]) (fun _ => 0) c
    simp [ax_liftfc_bottom, forall_, liftfc, botc, cons, nil, zero, succ, evalFormula, evalTerm, evalTerms,
      shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, liftfcN_bot]
  | atom p ts hts =>
    intro c
    have h := ax_de hM (φ := ax_liftfc_atom) (by simp [axioms]) (fun _ => 0) c p ts
    simp [ax_liftfc_atom, forall_3, liftfc, liftsc, atomc, cons, nil, zero, succ, evalFormula, evalTerm,
      evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, M_liftsc hM hts c, liftfcN_atom]
  | eq a b ha hb =>
    intro c
    have h := ax_de hM (φ := ax_liftfc_eq) (by simp [axioms]) (fun _ => 0) c a b
    simp [ax_liftfc_eq, forall_3, liftfc, liftc, eqc, cons, nil, zero, succ, evalFormula, evalTerm,
      evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, M_liftc hM ha c, M_liftc hM hb c, liftfcN_eq]
  | impl a b _ _ iha ihb =>
    intro c
    have h := ax_de hM (φ := ax_liftfc_impl) (by simp [axioms]) (fun _ => 0) c a b
    simp [ax_liftfc_impl, forall_3, liftfc, implc, cons, nil, zero, succ, evalFormula, evalTerm,
      evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, iha c, ihb c, liftfcN_impl]
  | all a _ iha =>
    intro c
    have h := ax_de hM (φ := ax_liftfc_forall) (by simp [axioms]) (fun _ => 0) c a
    simp [ax_liftfc_forall, forall_2, liftfc, forallc, cons, nil, zero, succ, evalFormula, evalTerm,
      evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, iha (c + 1), liftfcN_forall]
  | and a b _ _ iha ihb =>
    intro c
    have h := ax_de hM (φ := ax_liftfc_and) (by simp [axioms]) (fun _ => 0) c a b
    simp [ax_liftfc_and, forall_3, liftfc, andc, cons, nil, zero, succ, evalFormula, evalTerm,
      evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, iha c, ihb c, liftfcN_and]
  | or a b _ _ iha ihb =>
    intro c
    have h := ax_de hM (φ := ax_liftfc_or) (by simp [axioms]) (fun _ => 0) c a b
    simp [ax_liftfc_or, forall_3, liftfc, orc, cons, nil, zero, succ, evalFormula, evalTerm,
      evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, iha c, ihb c, liftfcN_or]
  | ex a _ iha =>
    intro c
    have h := ax_de hM (φ := ax_liftfc_ex) (by simp [axioms]) (fun _ => 0) c a
    simp [ax_liftfc_ex, forall_2, liftfc, exc, cons, nil, zero, succ, evalFormula, evalTerm,
      evalTerms, shiftEnv, hM.hcons, hM.hzero, hM.hsucc] at h
    rw [h, iha (c + 1), liftfcN_ex]



/-! ## §6 · Los códigos cerrados de términos, fórmulas y listas de fórmulas -/

mutual
theorem M_termCodeM (hM : Estandar M) (v : Nat → Nat) (t : Term) : evalTerm M v (termCodeM t) = codeNatTerm t := by
  match t with
  | .var n =>
    show M.func cons_sym [evalTerm M v (numeralM 0),
        M.func cons_sym [evalTerm M v (numeralM n), M.func zero_sym []]] = consN 0 (consN n 0)
    rw [M_numeral hM, M_numeral hM, hM.hzero, hM.hcons, hM.hcons]
  | .func s ts =>
    show M.func cons_sym [evalTerm M v (numeralM 1),
        M.func cons_sym [evalTerm M v (strCodeM s),
          M.func cons_sym [evalTerm M v (termsCodeM ts), M.func zero_sym []]]] =
      consN 1 (consN (codeNatStr s) (consN (codeNatTerms ts) 0))
    rw [M_numeral hM, M_str hM, M_termsCodeM hM v ts, hM.hzero, hM.hcons, hM.hcons, hM.hcons]
theorem M_termsCodeM (hM : Estandar M) (v : Nat → Nat) (ts : List Term) :
    evalTerm M v (termsCodeM ts) = codeNatTerms ts := by
  match ts with
  | [] => show M.func zero_sym [] = 0; exact hM.hzero
  | t :: ts' =>
    show M.func cons_sym [evalTerm M v (termCodeM t), evalTerm M v (termsCodeM ts')] =
      consN (codeNatTerm t) (codeNatTerms ts')
    rw [M_termCodeM hM v t, M_termsCodeM hM v ts', hM.hcons]
end

theorem M_formCodeM (hM : Estandar M) (v : Nat → Nat) : ∀ φ : Formula, evalTerm M v (formCodeM φ) = codeNat φ
  | .bottom => by
      show M.func cons_sym [evalTerm M v (numeralM 2), M.func zero_sym []] = consN 2 0
      rw [M_numeral hM, hM.hzero, hM.hcons]
  | .atom p ts => by
      show M.func cons_sym [evalTerm M v (numeralM 3),
          M.func cons_sym [evalTerm M v (strCodeM p),
            M.func cons_sym [evalTerm M v (termsCodeM ts), M.func zero_sym []]]] =
        consN 3 (consN (codeNatStr p) (consN (codeNatTerms ts) 0))
      rw [M_numeral hM, M_str hM, M_termsCodeM hM, hM.hzero, hM.hcons, hM.hcons, hM.hcons]
  | .eq t u => by
      show M.func cons_sym [evalTerm M v (numeralM 4),
          M.func cons_sym [evalTerm M v (termCodeM t),
            M.func cons_sym [evalTerm M v (termCodeM u), M.func zero_sym []]]] =
        consN 4 (consN (codeNatTerm t) (consN (codeNatTerm u) 0))
      rw [M_numeral hM, M_termCodeM hM, M_termCodeM hM, hM.hzero, hM.hcons, hM.hcons, hM.hcons]
  | .impl a b => by
      show M.func cons_sym [evalTerm M v (numeralM 5),
          M.func cons_sym [evalTerm M v (formCodeM a),
            M.func cons_sym [evalTerm M v (formCodeM b), M.func zero_sym []]]] =
        consN 5 (consN (codeNat a) (consN (codeNat b) 0))
      rw [M_numeral hM, M_formCodeM hM v a, M_formCodeM hM v b, hM.hzero, hM.hcons, hM.hcons, hM.hcons]
  | Formula.forall a => by
      show M.func cons_sym [evalTerm M v (numeralM 6),
          M.func cons_sym [evalTerm M v (formCodeM a), M.func zero_sym []]] =
        consN 6 (consN (codeNat a) 0)
      rw [M_numeral hM, M_formCodeM hM v a, hM.hzero, hM.hcons, hM.hcons]
  | .and a b => by
      show M.func cons_sym [evalTerm M v (numeralM 7),
          M.func cons_sym [evalTerm M v (formCodeM a),
            M.func cons_sym [evalTerm M v (formCodeM b), M.func zero_sym []]]] =
        consN 7 (consN (codeNat a) (consN (codeNat b) 0))
      rw [M_numeral hM, M_formCodeM hM v a, M_formCodeM hM v b, hM.hzero, hM.hcons, hM.hcons, hM.hcons]
  | .or a b => by
      show M.func cons_sym [evalTerm M v (numeralM 8),
          M.func cons_sym [evalTerm M v (formCodeM a),
            M.func cons_sym [evalTerm M v (formCodeM b), M.func zero_sym []]]] =
        consN 8 (consN (codeNat a) (consN (codeNat b) 0))
      rw [M_numeral hM, M_formCodeM hM v a, M_formCodeM hM v b, hM.hzero, hM.hcons, hM.hcons, hM.hcons]
  | .ex a => by
      show M.func cons_sym [evalTerm M v (numeralM 9),
          M.func cons_sym [evalTerm M v (formCodeM a), M.func zero_sym []]] =
        consN 9 (consN (codeNat a) 0)
      rw [M_numeral hM, M_formCodeM hM v a, hM.hzero, hM.hcons, hM.hcons]

theorem M_listFormCodeM (hM : Estandar M) (v : Nat → Nat) :
    ∀ L : List Formula, evalTerm M v (listFormCodeM L) = codeNatList L
  | [] => by show M.func zero_sym [] = 0; exact hM.hzero
  | f :: fs => by
      show M.func cons_sym [evalTerm M v (formCodeM f), evalTerm M v (listFormCodeM fs)] =
        consN (codeNat f) (codeNatList fs)
      rw [M_formCodeM hM, M_listFormCodeM hM v fs, hM.hcons]



/-! ## §7 · El ancla, y lo que necesita la cadena: `carc` de una línea, `allIn` -/

/-- El valor de `axiomsCodeT` en `M` es el código de los 142: el ancla es teorema (`prf_ancla`), `M` es sólida, y
    el código cerrado se evalúa igual. -/
theorem M_axiomsCodeT (hM : Estandar M) : M.func sym!"axiomsCodeT" [] = codeNatList axioms := by
  have h := prf_sound hM ROBINSON_PlusPlus.Meta.Representability2Prf.prf_ancla (fun _ => 0)
  simp only [evalFormula, axiomsCodeT, evalTerm, evalTerms, M_listFormCodeM hM] at h
  exact h

theorem M_carc' (hM : Estandar M) {x : Nat} (hx : ¬ x = 0) : M.func sym!"carc" [x] = carN x := by
  obtain ⟨a, b, rfl, _⟩ := consN_de hx; rw [M_carc hM, carN_consN]

theorem M_allIn (hM : Estandar M) (c : Nat) : ∀ L : Nat, M.rel sym!"allIn" [c, L] ↔ allInN c L := by
  intro L
  induction L using Nat.strongRecOn with
  | ind L ih =>
    by_cases hL : L = 0
    · subst hL
      have h := ax_de hM (φ := ax_allIn_nil) (by simp [axioms]) (fun _ => 0) c
      simp [ax_allIn_nil, forall_, allIn, nil, zero, evalFormula, evalTerm, evalTerms, shiftEnv, hM.hzero] at h
      exact ⟨fun _ => allInN_zero c, fun _ => h⟩
    · obtain ⟨a, b, rfl, hb⟩ := consN_de hL
      have h := ax_de hM (φ := ax_allIn_cons) (by simp [axioms]) (fun _ => 0) c a b
      simp [ax_allIn_cons, forall_3, _root_.iff, allIn, In, land, cons, evalFormula, evalTerm, evalTerms,
        shiftEnv, hM.hcons, M_mem hM] at h
      rw [allInN_consN, ← ih b hb]
      exact ⟨fun hh => h.1 hh, fun hh => h.2 hh.1 hh.2⟩

/-! ## §8 · `lineWF` de `M` es el de verdad (con `V` el valor de `axiomsCodeT` en `M`) -/

set_option hygiene false in
/-- Abre en `M` el axioma `ax_lineWF_*` de una etiqueta, para la línea `x`. -/
macro "abre_lw " ax:ident : tactic => `(tactic| (
  have h := ax_de hM (φ := $ax) (by simp [axioms]) (fun _ => 0) x
  simp [$ax:ident, forall_, _root_.iff, lineWF, lenc, nthc, carc, implc, andc, orc, forallc, exc, botc, eqc,
    substfc, liftfc, In, axiomsCodeT, cons, nil, zero, succ, land, evalFormula, evalTerm, evalTerms, shiftEnv,
    hM.hcons, hM.hzero, hM.hsucc, M_numeral hM, M_lenc hM, M_hasWit hM, M_hasWitF hM, M_mem hM,
    M_termCodeM hM] at h))

open ROBINSON_PlusPlus.Meta.RosserNumEval (codT_of_hasWitN codF_of_hasWitFN codF_liftfcN codT_codeNatTerm)

set_option hygiene false in
/-- Con `lenN x = n` (la RHS ya abierta, en `hlen`): `x` no es `0`, la etiqueta es la de verdad, y queda la RHS. -/
macro "cierra_lw" : tactic => `(tactic| (
  have hx : ¬ x = 0 := by intro e; subst e; simp [lenN_zero] at hlen
  rw [M_nthc hM 1 x (by omega)] at htag
  refine (lineWFN_of_tag htag (by decide)).2 ⟨hlen, ?_⟩))

set_option hygiene false in
/-- Las etiquetas SIN guarda y de longitud 4 (`p1`, `c1`, `c2`, `c3`, `j1`, `j2`). -/
macro "lw4 " ax:ident : tactic => `(tactic| (
  abre_lw $ax
  obtain ⟨hlen, hr⟩ := (h htag).1 hwf
  cierra_lw
  rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_nthc hM 3 x (by omega)] at hr
  exact hr))

set_option hygiene false in
/-- Las de longitud 5 sin guarda (`p2`, `j3`). -/
macro "lw5 " ax:ident : tactic => `(tactic| (
  abre_lw $ax
  obtain ⟨hlen, hr⟩ := (h htag).1 hwf
  cierra_lw
  rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_nthc hM 3 x (by omega), M_nthc hM 4 x (by omega)] at hr
  exact hr))

set_option hygiene false in
/-- Las de longitud 3 sin guarda (`efq`, `eqrefl`, `p3`, `gen`). -/
macro "lw3 " ax:ident : tactic => `(tactic| (
  abre_lw $ax
  obtain ⟨hlen, hr⟩ := (h htag).1 hwf
  cierra_lw
  rw [M_carc' hM hx, M_nthc hM 2 x (by omega)] at hr
  exact hr))

variable (hM : Estandar M) (x : Nat) (hwf : M.rel sym!"lineWF" [x])
local notation "Vm" => M.func sym!"axiomsCodeT" []

include hM hwf in
theorem lw_0 (htag : M.func sym!"nthc" [x, 1] = 0) : lineWFN Vm x := by lw4 ax_lineWF_p1
include hM hwf in
theorem lw_1 (htag : M.func sym!"nthc" [x, 1] = 1) : lineWFN Vm x := by lw5 ax_lineWF_p2
include hM hwf in
theorem lw_2 (htag : M.func sym!"nthc" [x, 1] = 2) : lineWFN Vm x := by lw4 ax_lineWF_c1
include hM hwf in
theorem lw_3 (htag : M.func sym!"nthc" [x, 1] = 3) : lineWFN Vm x := by lw4 ax_lineWF_c2
include hM hwf in
theorem lw_4 (htag : M.func sym!"nthc" [x, 1] = 4) : lineWFN Vm x := by lw4 ax_lineWF_c3
include hM hwf in
theorem lw_5 (htag : M.func sym!"nthc" [x, 1] = 5) : lineWFN Vm x := by lw4 ax_lineWF_j1
include hM hwf in
theorem lw_6 (htag : M.func sym!"nthc" [x, 1] = 6) : lineWFN Vm x := by lw4 ax_lineWF_j2
include hM hwf in
theorem lw_7 (htag : M.func sym!"nthc" [x, 1] = 7) : lineWFN Vm x := by lw5 ax_lineWF_j3
include hM hwf in
theorem lw_8 (htag : M.func sym!"nthc" [x, 1] = 8) : lineWFN Vm x := by lw3 ax_lineWF_efq
include hM hwf in
theorem lw_9 (htag : M.func sym!"nthc" [x, 1] = 9) : lineWFN Vm x := by
  abre_lw ax_lineWF_q1
  obtain ⟨hlen, hA, ht, hc⟩ := (h htag).1 hwf
  cierra_lw
  rw [M_nthc hM 2 x (by omega)] at hA
  rw [M_nthc hM 3 x (by omega)] at ht
  rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_nthc hM 3 x (by omega),
    M_substfc hM (codF_of_hasWitFN hA) 0 _ (codT_of_hasWitN ht)] at hc
  exact ⟨hA, ht, hc⟩
include hM hwf in
theorem lw_10 (htag : M.func sym!"nthc" [x, 1] = 10) : lineWFN Vm x := by
  abre_lw ax_lineWF_q2
  obtain ⟨hlen, hA, ht, hc⟩ := (h htag).1 hwf
  cierra_lw
  rw [M_nthc hM 2 x (by omega)] at hA
  rw [M_nthc hM 3 x (by omega)] at ht
  rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_nthc hM 3 x (by omega),
    M_substfc hM (codF_of_hasWitFN hA) 0 _ (codT_of_hasWitN ht)] at hc
  exact ⟨hA, ht, hc⟩
include hM hwf in
theorem lw_11 (htag : M.func sym!"nthc" [x, 1] = 11) : lineWFN Vm x := by
  abre_lw ax_lineWF_q3
  obtain ⟨hlen, hB, hc⟩ := (h htag).1 hwf
  cierra_lw
  rw [M_nthc hM 3 x (by omega)] at hB
  rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_nthc hM 3 x (by omega),
    M_liftfc hM (codF_of_hasWitFN hB) 0] at hc
  exact ⟨hB, hc⟩
include hM hwf in
theorem lw_12 (htag : M.func sym!"nthc" [x, 1] = 12) : lineWFN Vm x := by lw3 ax_lineWF_eqrefl
include hM hwf in
theorem lw_13 (htag : M.func sym!"nthc" [x, 1] = 13) : lineWFN Vm x := by
  abre_lw ax_lineWF_leibniz
  obtain ⟨hlen, hA, ht, hu, hc⟩ := (h htag).1 hwf
  cierra_lw
  rw [M_nthc hM 2 x (by omega)] at hA
  rw [M_nthc hM 3 x (by omega)] at ht
  rw [M_nthc hM 4 x (by omega)] at hu
  rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_nthc hM 3 x (by omega), M_nthc hM 4 x (by omega),
    M_substfc hM (codF_of_hasWitFN hA) 0 _ (codT_of_hasWitN ht),
    M_substfc hM (codF_of_hasWitFN hA) 0 _ (codT_of_hasWitN hu)] at hc
  exact ⟨hA, ht, hu, hc⟩
include hM hwf in
theorem lw_14 (htag : M.func sym!"nthc" [x, 1] = 14) : lineWFN Vm x := by lw3 ax_lineWF_p3
include hM hwf in
theorem lw_15 (htag : M.func sym!"nthc" [x, 1] = 15) : lineWFN Vm x := by
  abre_lw ax_lineWF_thy
  obtain ⟨hlen, hr⟩ := (h htag).1 hwf
  cierra_lw
  rw [M_carc' hM hx] at hr
  exact hr
include hM hwf in
theorem lw_16 (htag : M.func sym!"nthc" [x, 1] = 16) : lineWFN Vm x := by
  abre_lw ax_lineWF_mp
  have hlen := (h htag).1 hwf
  have hx : ¬ x = 0 := by intro e; subst e; simp [lenN_zero] at hlen
  rw [M_nthc hM 1 x (by omega)] at htag
  exact (lineWFN_of_tag htag (by decide)).2 hlen
include hM hwf in
theorem lw_17 (htag : M.func sym!"nthc" [x, 1] = 17) : lineWFN Vm x := by lw3 ax_lineWF_gen
include hM hwf in
theorem lw_18 (htag : M.func sym!"nthc" [x, 1] = 18) : lineWFN Vm x := by
  abre_lw ax_lineWF_ind
  obtain ⟨hlen, hA, hc⟩ := (h htag).1 hwf
  cierra_lw
  rw [M_nthc hM 2 x (by omega)] at hA
  have hA' := codF_of_hasWitFN hA
  rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_liftfc hM hA' 1,
    M_substfc hM (codF_liftfcN hA' 1) 0 _ (codT_codeNatTerm _),
    M_substfc hM hA' 0 _ (codT_codeNatTerm _)] at hc
  exact ⟨hA, hc⟩
include hM hwf in
theorem lw_19 (htag : M.func sym!"nthc" [x, 1] = 19) : lineWFN Vm x := by
  abre_lw ax_lineWF_qconf
  obtain ⟨hlen, hA, hc⟩ := (h htag).1 hwf
  cierra_lw
  rw [M_nthc hM 2 x (by omega)] at hA
  rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_nthc hM 3 x (by omega),
    M_liftfc hM (codF_of_hasWitFN hA) 0] at hc
  exact ⟨hA, hc⟩
include hM hwf in
theorem lw_20 (htag : M.func sym!"nthc" [x, 1] = 20) : lineWFN Vm x := by
  abre_lw ax_lineWF_listInd
  obtain ⟨hlen, hA, hc⟩ := (h htag).1 hwf
  cierra_lw
  rw [M_nthc hM 2 x (by omega)] at hA
  have hA' := codF_of_hasWitFN hA
  rw [M_carc' hM hx, M_nthc hM 2 x (by omega), M_liftfc hM hA' 1, M_liftfc hM (codF_liftfcN hA' 1) 2,
    M_substfc hM (codF_liftfcN (codF_liftfcN hA' 1) 2) 0 _ (codT_codeNatTerm _),
    M_substfc hM hA' 0 _ (codT_codeNatTerm _)] at hc
  exact ⟨hA, hc⟩



/-! ## §9 · De `lineWF` en `M` a `lineWFN`, por la etiqueta (`ax_lineWF_inv`) -/

theorem M_tagDisj (hM : Estandar M) (v : Nat → Nat) (t : Term) : ∀ n : Nat,
    evalFormula M v (tagDisj t n) → ∃ K, And (K ≤ n) (M.func sym!"nthc" [evalTerm M v t, 1] = K) := by
  intro n
  induction n with
  | zero =>
    intro h
    simp [tagDisj, lineTag, nthc, succ, zero, evalFormula, evalTerm, evalTerms, hM.hsucc, hM.hzero,
      M_numeral hM] at h
    exact ⟨0, Nat.le_refl 0, h⟩
  | succ n ih =>
    intro h
    simp only [tagDisj, lor, evalFormula] at h
    rcases h with h | h
    · simp [lineTag, nthc, succ, zero, evalFormula, evalTerm, evalTerms, hM.hsucc, hM.hzero, M_numeral hM] at h
      exact ⟨n + 1, Nat.le_refl _, h⟩
    · obtain ⟨K, hK, e⟩ := ih h; exact ⟨K, by omega, e⟩

include hM hwf in
/-- 🏁 **Si `M` cree que `x` es una línea bien formada, lo es** (con el `V` de `M`). -/
theorem M_lineWF : lineWFN (M.func sym!"axiomsCodeT" []) x := by
  have h := ax_de hM (φ := ax_lineWF_inv) (by simp [axioms]) (fun _ => 0) x
  simp only [ax_lineWF_inv, forall_, evalFormula, lineWF] at h
  have hx := h (by simpa [evalTerm, evalTerms, shiftEnv] using hwf)
  obtain ⟨K, hK, htag⟩ := M_tagDisj hM _ _ 20 hx
  simp only [evalTerm, shiftEnv] at htag
  match K, hK, htag with
  | 0, _, e => exact lw_0 hM x hwf e
  | 1, _, e => exact lw_1 hM x hwf e
  | 2, _, e => exact lw_2 hM x hwf e
  | 3, _, e => exact lw_3 hM x hwf e
  | 4, _, e => exact lw_4 hM x hwf e
  | 5, _, e => exact lw_5 hM x hwf e
  | 6, _, e => exact lw_6 hM x hwf e
  | 7, _, e => exact lw_7 hM x hwf e
  | 8, _, e => exact lw_8 hM x hwf e
  | 9, _, e => exact lw_9 hM x hwf e
  | 10, _, e => exact lw_10 hM x hwf e
  | 11, _, e => exact lw_11 hM x hwf e
  | 12, _, e => exact lw_12 hM x hwf e
  | 13, _, e => exact lw_13 hM x hwf e
  | 14, _, e => exact lw_14 hM x hwf e
  | 15, _, e => exact lw_15 hM x hwf e
  | 16, _, e => exact lw_16 hM x hwf e
  | 17, _, e => exact lw_17 hM x hwf e
  | 18, _, e => exact lw_18 hM x hwf e
  | 19, _, e => exact lw_19 hM x hwf e
  | 20, _, e => exact lw_20 hM x hwf e
  | k + 21, hk, _ => exact absurd hk (by omega)



/-! ## §10 · Las premisas (`mp`, `gen`), la cadena y `runFn` -/

theorem dec3 {x : Nat} (h : lenN x = 3) : ∃ a b c, x = consN a (consN b (consN c 0)) := by
  have hx : ¬ x = 0 := by intro e; subst e; simp [lenN_zero] at h
  obtain ⟨a, r, rfl, _⟩ := consN_de hx
  rw [lenN_consN] at h
  have hr : ¬ r = 0 := by intro e; subst e; simp [lenN_zero] at h
  obtain ⟨b, r', rfl, _⟩ := consN_de hr
  rw [lenN_consN] at h
  have hr' : ¬ r' = 0 := by intro e; subst e; simp [lenN_zero] at h
  obtain ⟨c, r'', rfl, _⟩ := consN_de hr'
  rw [lenN_consN] at h
  have : r'' = 0 := by
    rcases Nat.eq_zero_or_pos r'' with e | hpos
    · exact e
    · obtain ⟨d, s, rfl, _⟩ := consN_de (Nat.pos_iff_ne_zero.mp hpos); rw [lenN_consN] at h; omega
  subst this; exact ⟨a, b, c, rfl⟩

/-- Si `M` cree que las premisas de una línea bien formada están en `c`, lo están: sólo `mp` y `gen` tienen. -/
theorem M_allIn_prems (hM : Estandar M) {V c x : Nat} (hwf : lineWFN V x)
    (h : M.rel sym!"allIn" [c, M.func sym!"premsOf" [x]]) : allInN c (premsOfN x) := by
  rw [M_allIn hM] at h
  by_cases h16 : nthN x 1 = 16
  · have hlen : lenN x = 3 := (lineWFN_of_tag h16 (by decide)).1 hwf
    obtain ⟨a, b, d, rfl⟩ := dec3 hlen
    have hb : b = 16 := by simpa [nthN_cs, nthN_cz] using h16
    subst hb
    have hp := ax_de hM (φ := ax_premsOf_mp) (by simp [axioms]) (fun _ => 0) a d
    simp [ax_premsOf_mp, forall_2, premsOf, implc, cons, nil, zero, succ, evalFormula, evalTerm, evalTerms,
      shiftEnv, hM.hcons, hM.hzero, hM.hsucc, M_numeral hM] at hp
    rw [hp] at h
    simpa [premsOfN, nthN_cs, nthN_cz] using h
  · by_cases h17 : nthN x 1 = 17
    · have hlen : lenN x = 3 := ((lineWFN_of_tag h17 (by decide)).1 hwf).1
      obtain ⟨a, b, d, rfl⟩ := dec3 hlen
      have hb : b = 17 := by simpa [nthN_cs, nthN_cz] using h17
      subst hb
      have hp := ax_de hM (φ := ax_premsOf_gen) (by simp [axioms]) (fun _ => 0) a d
      simp [ax_premsOf_gen, forall_2, premsOf, cons, nil, zero, succ, evalFormula, evalTerm, evalTerms,
        shiftEnv, hM.hcons, hM.hzero, hM.hsucc, M_numeral hM] at hp
      rw [hp] at h
      simpa [premsOfN, nthN_cs, nthN_cz] using h
    · rw [premsOfN, ite_eq_right h16, ite_eq_right h17]; exact allInN_zero c

/-- 🏁 **Si `M` cree que `p` es una cadena válida desde `c`, lo es**, y `runFn` vale lo mismo. -/
theorem M_cadena (hM : Estandar M) : ∀ (p c : Nat), M.rel sym!"chainOk" [c, p] →
    And (chainOkN (M.func sym!"axiomsCodeT" []) c p) (M.func sym!"runFn" [c, p] = runFnN c p) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro c hc
    by_cases hp : p = 0
    · subst hp
      have h := ax_de hM (φ := ax_runFn_nil) (by simp [axioms]) (fun _ => 0) c
      simp [ax_runFn_nil, forall_, runFn, nil, zero, evalFormula, evalTerm, evalTerms, shiftEnv, hM.hzero] at h
      exact ⟨chainOkN_zero _ c, by rw [h, runFnN_zero]⟩
    · obtain ⟨l, r, rfl, hr⟩ := consN_de hp
      have h := ax_de hM (φ := ax_chainOk_cons) (by simp [axioms]) (fun _ => 0) c l r
      simp [ax_chainOk_cons, forall_3, _root_.iff, chainOk, lineOk, lineWF, allIn, premsOf, land, concat, carc,
        cons, nil, zero, evalFormula, evalTerm, evalTerms, shiftEnv, hM.hcons, hM.hzero] at h
      obtain ⟨⟨hwf, hal⟩, hrest⟩ := h.1 hc
      have hlw := M_lineWF hM l hwf
      have hl0 : ¬ l = 0 := by
        intro e; subst e
        have := hlw.1; have h2 := hlw.2
        rw [nthN_zero_l] at h2 this
        simp [lineWFT, lenN_zero] at h2
      rw [M_carc' hM hl0, M_concat hM] at hrest
      obtain ⟨ihc, ihr⟩ := ih r hr _ hrest
      have hrf := ax_de hM (φ := ax_runFn_cons) (by simp [axioms]) (fun _ => 0) c l r
      simp [ax_runFn_cons, forall_3, runFn, concat, carc, cons, nil, zero, evalFormula, evalTerm, evalTerms,
        shiftEnv, hM.hcons, hM.hzero] at hrf
      refine ⟨(chainOkN_consN _ c l r).2 ⟨⟨hlw, M_allIn_prems hM hlw hal⟩, ihc⟩, ?_⟩
      rw [hrf, M_carc' hM hl0, M_concat hM, ihr, runFnN_consN]



/-! ## §11 · 🏁 `prf_of_prov` y E10 para TODO `Estandar M` -/

theorem M_provCodeC' (hM : Estandar M) (φ : Formula) (v : Nat → Nat) :
    evalFormula M v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) →
      ∃ p, And (M.rel sym!"chainOk" [0, p]) (memN (codeNat φ) (M.func sym!"runFn" [0, p])) := by
  intro h
  rw [ROBINSON_PlusPlus.Meta.ProofChain.provCodeC', eval_substFormula_zero,
    ← ROBINSON_PlusPlus.Meta.Representability.formCodeM_eq, M_formCodeM hM] at h
  simp only [ROBINSON_PlusPlus.Meta.ProofChain.provFormulaC', land, chainOk, In, runFn, nil, zero,
    evalFormula, evalTerm, evalTerms, shiftEnv, hM.hzero, M_mem hM] at h
  exact h

/-- 🏁 **Lo que un modelo estándar CUALQUIERA cree demostrable, lo es.** -/
theorem prf_of_prov_de (hM : Estandar M) (φ : Formula) (v : Nat → Nat) :
    evalFormula M v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) → Prf φ := by
  intro hp
  obtain ⟨p, hc, hm⟩ := M_provCodeC' hM φ v hp
  obtain ⟨hch, hrun⟩ := M_cadena hM p 0 hc
  rw [hrun] at hm
  rw [M_axiomsCodeT hM] at hch
  have h := ROBINSON_PlusPlus.Meta.SolidezVerificador.cadena_buena
    ROBINSON_PlusPlus.Meta.SolidezVerificador.bueno_codeNatList (decodeL p) 0
    ROBINSON_PlusPlus.Meta.SolidezVerificador.bueno_zero hch (codeNat φ) hm
  rwa [ROBINSON_PlusPlus.Meta.SolidezVerificador.dec_codeNat] at h

/-- 🏁 **`Prov` es FIEL en todo modelo estándar.** -/
theorem modelo_prov_iff_de (hM : Estandar M) (φ : Formula) (v : Nat → Nat) :
    evalFormula M v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) ↔ Prf φ :=
  ⟨prf_of_prov_de hM φ v, fun h => prf_sound hM (ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf h) v⟩

/-- 🏁 **E10: `G` es VERDADERA en todo modelo estándar.** -/
theorem godelCN_verdadera_de (hM : Estandar M) (v : Nat → Nat) :
    evalFormula M v ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN := by
  have hfp := prf_sound hM ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_godelCN_fixedpoint v
  apply hfp.2
  intro hp
  exact ROBINSON_PlusPlus.Meta.Consistencia.goedel_I (prf_of_prov_de hM _ _ hp)

/-- 🏁 **E10: `Con` es VERDADERA en todo modelo estándar.** -/
theorem con_verdadera_de (hM : Estandar M) (v : Nat → Nat) :
    evalFormula M v ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' :=
  fun hp => ROBINSON_PlusPlus.Meta.Consistencia.consistencia (prf_of_prov_de hM _ _ hp)

/-- El control de que la hipótesis no es vacía: `MNV V₀` es estándar (`estandar_MN`), y la instancia es
    `prf_of_prov` de `Meta/SolidezVerificador.lean`. -/
theorem control_instancia (φ : Formula) (v : Nat → Nat) :
    evalFormula (ROBINSON_PlusPlus.Meta.ModeloEstandar.MNV ROBINSON_PlusPlus.Meta.ModeloCodigo.V₀) v
      (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) → Prf φ :=
  prf_of_prov_de ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN φ v

/-! ## §12 · ⛔ El control del ANCLA: sin él, `Prov` puede mentir (T75b, ADR‑175)

`Estandar M` pide los 142, ancla incluida. Sin el ancla no basta: `MNV V` satisface los 141 de la base para TODO `V`
(`MN_coreAxioms`, `MN_codingAxioms`), y en `MNV V` la regla `thy` acepta lo que haya en `V`. Con `V⊥` —la lista del
código de `⊥` sola— la cadena de UNA línea `⟨⌜⊥⌝, 15⟩` es una prueba de `⊥`, y `Con` es FALSA. El ancla falla en
`MNV V⊥`, y no hace falta evaluar su numeral: si valiera, `MNV V⊥` sería estándar y `con_verdadera_de` haría
verdadera `Con`. -/

section ControlAncla
open ROBINSON_PlusPlus.Meta.ModeloEstandar

/-- En `MNV V`, `Prov(⌜φ⌝)` es la existencia de una cadena que `chainOkN V` acepta y que concluye `φ`. -/
theorem MN_provCodeC'_iff {V : Nat} (φ : Formula) (v : Nat → Nat) :
    evalFormula (MNV V) v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) ↔
      ∃ p, And (chainOkN V 0 p) (memN (codeNat φ) (runFnN 0 p)) := by
  rw [ROBINSON_PlusPlus.Meta.ProofChain.provCodeC', eval_substFormula_zero,
    ← ROBINSON_PlusPlus.Meta.Representability.formCodeM_eq, ev_formCodeM]
  simp only [ROBINSON_PlusPlus.Meta.ProofChain.provFormulaC', land, chainOk, In, runFn, nil, zero,
    in_sym, zero_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MN_chainOk, MN_mem, MN_runFn, MN_zero]

/-- La línea `thy` que concluye `a`: `⟨a, 15⟩`. -/
def lineaThy (a : Nat) : Nat := consN a (consN 15 0)

theorem chain_thy {V a : Nat} (h : memN a V) : chainOkN V 0 (consN (lineaThy a) 0) := by
  rw [chainOkN_consN]
  have h1 : nthN (lineaThy a) 1 = 15 := by rw [lineaThy, nthN_cs, nthN_cz]
  refine ⟨⟨(lineWFN_of_tag h1 (by decide)).2 ⟨?_, ?_⟩, ?_⟩, chainOkN_zero _ _⟩
  · rw [lineaThy, lenN_consN, lenN_consN, lenN_zero]
  · rw [lineaThy, carN_consN]; exact h
  · rw [premsOfN, ite_eq_right (by rw [h1]; decide), ite_eq_right (by rw [h1]; decide)]
    exact allInN_zero 0

theorem run_thy (a : Nat) : memN a (runFnN 0 (consN (lineaThy a) 0)) := by
  rw [runFnN_consN, runFnN_zero, concatN_zero, lineaThy, carN_consN, memN_consN]
  exact Or.inl rfl

/-- `MNV V` cree demostrable todo lo que está en `V`, para TODO `V`: una cadena de una línea `thy`. -/
theorem prov_de_mem {V : Nat} (φ : Formula) (h : memN (codeNat φ) V) (v : Nat → Nat) :
    evalFormula (MNV V) v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) :=
  (MN_provCodeC'_iff φ v).2 ⟨_, chain_thy h, run_thy _⟩

/-- `V⊥`: la lista de UN código, el de `⊥`. -/
def Vbot : Nat := consN (codeNat Formula.bottom) 0

theorem MNbot_base (v : Nat → Nat) : contextSatisfies (MNV Vbot) v axiomsBase := by
  intro φ hφ
  cases List.mem_append.mp hφ with
  | inl h => exact MN_coreAxioms v φ h
  | inr h => exact ROBINSON_PlusPlus.Meta.ModeloCodificacion.MN_codingAxioms v φ h

theorem MNbot_no_con (v : Nat → Nat) :
    ¬ evalFormula (MNV Vbot) v ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' :=
  fun hc => hc (prov_de_mem Formula.bottom ((memN_consN _ _ _).2 (Or.inl rfl)) v)

/-- ⛔ **El control del ancla**: `MNV V⊥` satisface los 141 de la base, `Con` es FALSA en él (cree demostrable `⊥`),
    y el ancla FALLA —sin evaluar su numeral: si valiera, `MNV V⊥` sería estándar y `con_verdadera_de` lo
    impediría—. Es el ancla la que fija el sentido de `Prov`; hermano de `control_tc_cons`. -/
theorem control_ancla : And (∀ v, contextSatisfies (MNV Vbot) v axiomsBase)
    (And (∀ v, ¬ evalFormula (MNV Vbot) v ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula')
      (¬ ∀ v, evalFormula (MNV Vbot) v ax_axiomsCodeT_def)) := by
  refine ⟨MNbot_base, MNbot_no_con, fun ha => ?_⟩
  have hM : Estandar (MNV Vbot) :=
    { hzero := MN_zero, hsucc := MN_succ, hcons := MN_cons,
      haxs := fun v φ hφ => by
        rw [axioms_split] at hφ
        cases List.mem_append.mp hφ with
        | inl h => exact MNbot_base v φ h
        | inr h => rw [List.mem_singleton.mp h]; exact ha v }
  exact MNbot_no_con (fun _ => 0) (con_verdadera_de hM _)

end ControlAncla

end ROBINSON_PlusPlus.Meta.RigidezEstandar

#print axioms ROBINSON_PlusPlus.Meta.RigidezEstandar.M_hasWitF
#print axioms ROBINSON_PlusPlus.Meta.RigidezEstandar.M_substfc
#print axioms ROBINSON_PlusPlus.Meta.RigidezEstandar.M_lineWF
#print axioms ROBINSON_PlusPlus.Meta.RigidezEstandar.M_cadena
#print axioms ROBINSON_PlusPlus.Meta.RigidezEstandar.prf_of_prov_de
#print axioms ROBINSON_PlusPlus.Meta.RigidezEstandar.modelo_prov_iff_de
#print axioms ROBINSON_PlusPlus.Meta.RigidezEstandar.godelCN_verdadera_de
#print axioms ROBINSON_PlusPlus.Meta.RigidezEstandar.con_verdadera_de
#print axioms ROBINSON_PlusPlus.Meta.RigidezEstandar.control_ancla
