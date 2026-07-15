/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CodeDecode
import ROBINSON_PlusPlus.Meta.Representability2

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.CodeDecode
open ROBINSON_PlusPlus.Meta.HilbertSeq
open ROBINSON_PlusPlus.Meta.Representability2

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.ChainDecode

/-!
## META — NIVEL D real (§43·A.2): DECODIFICADOR de CADENAS (módulo A de `PLAN-NEGVERIFIER.md`)

Inversos de los codificadores de prueba `lineJustif` / `lineCode'` / `proofCode'`
(`Meta/Representability2.lean`). Construido sobre `CodeDecode` (fórmulas/términos).

### ⚠️ El codificador es LOSSY para `thy`/`mp`/`gen` ⟹ **sección**, no *retract*

`lineJustif` **descarta los índices** de tres reglas (ver `Representability2.lean:46`):
* `thy k    ↦ cons 15̇ nil`                       — la `k` NO se guarda;
* `mp i j   ↦ cons 16̇ (cons ⌜acc[j]⌝ nil)`        — guarda la **premisa resuelta**, no `i`/`j`;
* `gen i    ↦ cons 17̇ (cons ⌜acc[i]⌝ nil)`        — guarda `acc[i]`, no `i`.

Por tanto `decodeChain (proofCode' rs []) = some rs` (**retract**, como decía el plan) es **FALSO**
(dos `thy 3`/`thy 5` con la misma conclusión, o dos `mp i j`/`mp i' j`, producen el mismo código).
Lo correcto —y lo que `VerifierSound` (módulo E) necesita— es la **SECCIÓN**:
`decodeChain t = some rs → proofCode' rs [] = t ∧ checkProof rs ≠ none`. Los índices se recuperan
**por búsqueda** en el acumulador (`findIdx`). Para los **18 tags limpios** el retract SÍ vale
(`decodeRule_lineJustif_clean`); para `thy`/`mp`/`gen`, la sección bajo well‑formedness
(`decodeRule_{thy,mp,gen}_section`).

**Ensamblado (`decodeChain_checkProof`/`decodeChain_prf`):** de hecho lo que el módulo E necesita NO es
el retract sintáctico `proofCode' rs = t` (que `peelArgs` no garantiza para códigos con «cola basura»),
sino la **SOLIDEZ**: `decodeChain t = some rs → checkProof rs ≠ none`, y de ahí `Prf` de cada conclusión
vía `derivation_to_prf`. La clave es que `decodeLine` **verifica** `stepConcl acc r = some f`.

### Nota de rendimiento

Un `match` sobre `Term` con las 21 formas anidadas revienta el `whnf` (`String.decEq` en el
discriminante). Se **pela** el justif a `List Term` (`peelArgs`) y se matchea `(tag : Nat, args)` —
superficial y barato.
-/

/-! ### Igualdad decidible y buscador de índices (para recuperar los índices de `thy`/`mp`/`gen`)

`Term`/`Formula` sólo derivan `BEq` (estructural, anidado) — **no** `DecidableEq` ni `LawfulBEq`, y
el handler de `deriving DecidableEq` no cubre el anidamiento (`func : String → List Term`). Se
construye a mano (mutuo para `Term`) y se usa un buscador propio `findIdx` con `=` (no `List.idxOf?`,
que va por `BEq` y exigiría `LawfulBEq`). -/

mutual
private def decEqTerm : (a b : Term) → Decidable (a = b)
  | .var n, .var m => if h : n = m then .isTrue (by rw [h]) else .isFalse (by simp [h])
  | .func s1 l1, .func s2 l2 =>
      if hs : s1 = s2 then
        match decEqListTerm l1 l2 with
        | .isTrue hl => .isTrue (by rw [hs, hl])
        | .isFalse hl => .isFalse (by simp [hs, hl])
      else .isFalse (by simp [hs])
  | .var _, .func _ _ => .isFalse (by simp)
  | .func _ _, .var _ => .isFalse (by simp)
private def decEqListTerm : (l1 l2 : List Term) → Decidable (l1 = l2)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (by simp)
  | _ :: _, [] => .isFalse (by simp)
  | a :: as, b :: bs =>
      match decEqTerm a b with
      | .isTrue ha => match decEqListTerm as bs with
          | .isTrue has => .isTrue (by rw [ha, has])
          | .isFalse has => .isFalse (by simp [ha, has])
      | .isFalse ha => .isFalse (by simp [ha])
end

instance : DecidableEq Term := decEqTerm
deriving instance DecidableEq for Formula

/-- Índice de la **primera** aparición de `f` en `l` (con `DecidableEq`). Recupera los índices que
    `lineJustif` descarta en `thy`/`mp`/`gen`. -/
def findIdx (f : Formula) : List Formula → Option Nat
  | [] => none
  | g :: gs => if g = f then some 0 else (findIdx f gs).map (· + 1)

/-- **Solidez de `findIdx`**: el índice devuelto apunta a `f`. -/
theorem findIdx_sound (f : Formula) : ∀ (l : List Formula) (i : Nat),
    findIdx f l = some i → l[i]? = some f := by
  intro l
  induction l with
  | nil => intro i h; simp [findIdx] at h
  | cons g gs ih =>
      intro i h
      simp only [findIdx] at h
      by_cases hg : g = f
      · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; simp [hg]
      · rw [if_neg hg] at h
        rcases hj : findIdx f gs with _ | j
        · rw [hj] at h; simp at h
        · rw [hj] at h; simp only [Option.map] at h; injection h with h; subst h
          simp only [List.getElem?_cons_succ]; exact ih j hj

/-- **Completitud de `findIdx`**: si `f` aparece en `l`, la búsqueda tiene éxito. -/
theorem findIdx_isSome_of_getElem (f : Formula) : ∀ (l : List Formula) (i : Nat),
    l[i]? = some f → (findIdx f l).isSome = true := by
  intro l
  induction l with
  | nil => intro i h; simp at h
  | cons g gs ih =>
      intro i h
      simp only [findIdx]
      by_cases hg : g = f
      · rw [if_pos hg]; rfl
      · rw [if_neg hg]
        cases i with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; exact absurd h hg
        | succ j =>
            simp only [List.getElem?_cons_succ] at h
            rcases hk : findIdx f gs with _ | k
            · have := ih j h; rw [hk] at this; simp at this
            · simp

/-- `decodeForm`/`decodeTerm` invierten también `formCode`/`termCode` (capa Meta), vía los puentes
    `formCodeM_eq`/`termCodeM_eq`. -/
theorem decodeForm_formCode (A : Formula) : decodeForm (formCode A) = some A := by
  rw [← ROBINSON_PlusPlus.Meta.Representability.formCodeM_eq]; exact decodeForm_formCodeM A
theorem decodeTerm_termCode (t : Term) : decodeTerm (termCode t) = some t := by
  rw [← ROBINSON_PlusPlus.Meta.Representability.termCodeM_eq]; exact decodeTerm_termCodeM t

/-- Pela un término‑lista `cons a₀ (cons a₁ … nil)` a `[a₀, a₁, …]`. -/
def peelArgs : Term → List Term
  | .func s [a, b] => if s == cons_sym then a :: peelArgs b else []
  | _ => []

@[simp] theorem peelArgs_nil : peelArgs nil = [] := rfl
@[simp] theorem peelArgs_cons (a b : Term) : peelArgs (cons a b) = a :: peelArgs b := by
  simp only [peelArgs, cons, beq_self_eq_true, if_true]

/-- Reglas por tag (0..20) + lista de argumentos (match superficial sobre `List Term`).
    `thy`/`mp`/`gen` recuperan sus índices por búsqueda en `axioms`/`acc`. -/
def decodeRuleTag (acc : List Formula) (f : Formula) : Nat → List Term → Option Rule
  | 0, [cA, cB] => (decodeForm cA).bind fun A => (decodeForm cB).map fun B => Rule.p1 A B
  | 1, [cA, cB, cC] => (decodeForm cA).bind fun A => (decodeForm cB).bind fun B => (decodeForm cC).map fun C => Rule.p2 A B C
  | 2, [cA, cB] => (decodeForm cA).bind fun A => (decodeForm cB).map fun B => Rule.c1 A B
  | 3, [cA, cB] => (decodeForm cA).bind fun A => (decodeForm cB).map fun B => Rule.c2 A B
  | 4, [cA, cB] => (decodeForm cA).bind fun A => (decodeForm cB).map fun B => Rule.c3 A B
  | 5, [cA, cB] => (decodeForm cA).bind fun A => (decodeForm cB).map fun B => Rule.j1 A B
  | 6, [cA, cB] => (decodeForm cA).bind fun A => (decodeForm cB).map fun B => Rule.j2 A B
  | 7, [cA, cB, cC] => (decodeForm cA).bind fun A => (decodeForm cB).bind fun B => (decodeForm cC).map fun C => Rule.j3 A B C
  | 8, [cA] => (decodeForm cA).map fun A => Rule.efq A
  | 9, [cA, cT] => (decodeForm cA).bind fun A => (decodeTerm cT).map fun t => Rule.q1 A t
  | 10, [cA, cT] => (decodeForm cA).bind fun A => (decodeTerm cT).map fun t => Rule.q2 A t
  | 11, [cA, cB] => (decodeForm cA).bind fun A => (decodeForm cB).map fun B => Rule.q3 A B
  | 12, [cT] => (decodeTerm cT).map fun t => Rule.eqrefl t
  | 13, [cA, cT1, cT2] => (decodeForm cA).bind fun A => (decodeTerm cT1).bind fun t1 => (decodeTerm cT2).map fun t2 => Rule.leibniz A t1 t2
  | 14, [cA] => (decodeForm cA).map fun A => Rule.p3 A
  | 18, [cA] => (decodeForm cA).map fun A => Rule.ind A
  | 19, [cP, cC] => (decodeForm cP).bind fun P => (decodeForm cC).map fun C => Rule.qconf P C
  | 20, [cA] => (decodeForm cA).map fun A => Rule.listInd A
  | 15, _ => (findIdx f axioms).map Rule.thy
  | 16, [cfj] => (decodeForm cfj).bind fun fj =>
      (findIdx fj acc).bind fun j => (findIdx (Formula.impl fj f) acc).map fun i => Rule.mp i j
  | 17, [cg] => (decodeForm cg).bind fun g => (findIdx g acc).map fun i => Rule.gen i
  | _, _ => none

/-- Inverso de `lineJustif acc` dada la conclusión `f` (necesaria para `thy`/`mp`/`gen`). -/
def decodeRule (acc : List Formula) (f : Formula) (jT : Term) : Option Rule :=
  match peelArgs jT with
  | tagT :: args => (decodeNat tagT).bind fun tag => decodeRuleTag acc f tag args
  | [] => none

/-- Inverso de `lineCode' acc f r = cons ⌜f⌝ (lineJustif acc r)`: decodifica la
    conclusión (cabeza) y la regla, **verificando** que la regla concluye la cabeza
    (`stepConcl acc r = some f`). Ese chequeo es lo que garantiza que el acumulador que
    `decodeChainAux` hila coincide con el de `checkAux` ⟹ la cadena decodificada **verifica**. -/
def decodeLine (acc : List Formula) : Term → Option (Formula × Rule)
  | .func cs [conclT, justifT] =>
      if cs == cons_sym then
        (decodeForm conclT).bind fun f =>
          (decodeRule acc f justifT).bind fun r =>
            if stepConcl acc r = some f then some (f, r) else none
      else none
  | _ => none

/-- Inverso de `proofCode'`, hilando el acumulador de conclusiones. -/
def decodeChainAux (acc : List Formula) : Term → Option (List Rule)
  | .func s [] => if s == zero_sym then some [] else none
  | .func s [lineT, rest] =>
      if s == cons_sym then
        (decodeLine acc lineT).bind fun fr =>
          (decodeChainAux (acc ++ [fr.1]) rest).map fun rs => fr.2 :: rs
      else none
  | _ => none

def decodeChain (t : Term) : Option (List Rule) := decodeChainAux [] t

/-- Reglas cuya codificación NO descarta información (todas menos `thy`/`mp`/`gen`). -/
def cleanRule : Rule → Bool
  | .thy _ | .mp _ _ | .gen _ => false
  | _ => true

set_option maxHeartbeats 400000 in
/-- **RETRACT sobre los 18 tags limpios**: `decodeRule acc f (lineJustif acc r) = some r`.
    (Para `thy`/`mp`/`gen` sólo vale la sección, ver la cabecera.) -/
theorem decodeRule_lineJustif_clean (acc : List Formula) (f : Formula) (r : Rule)
    (hcl : cleanRule r = true) : decodeRule acc f (lineJustif acc r) = some r := by
  cases r <;>
    simp_all only [cleanRule, lineJustif, decodeRule, peelArgs_cons, peelArgs_nil,
      decodeNat_numeralM, decodeRuleTag, decodeForm_formCode, decodeTerm_termCode,
      Option.bind, Option.map, reduceCtorEq]


/-! ### La SECCIÓN de `thy`/`mp`/`gen` (los tres tags LOSSY)

`lineJustif` descarta sus índices, así que el *retract* falla; pero bajo **well‑formedness**
(`stepConcl acc r = some f`, lo que garantiza `checkAux` para las líneas de una cadena válida) vale la
**sección**: `decodeRule` recupera un `r'` que (1) tiene éxito, (2) es **sólido** (`stepConcl acc r' =
some f`) y (3) **re‑codifica** al mismo justif (`lineJustif acc r' = lineJustif acc r`). Los índices se
recuperan con `findIdx`; su corrección (`findIdx_sound`/`findIdx_isSome_of_getElem`) cierra las tres. -/

theorem decodeRule_thy_eq (acc : List Formula) (f : Formula) (k : Nat) :
    decodeRule acc f (lineJustif acc (Rule.thy k)) = (findIdx f axioms).map Rule.thy := by
  simp only [lineJustif, decodeRule, peelArgs_cons, peelArgs_nil, decodeNat_numeralM,
    decodeRuleTag, Option.bind]

theorem decodeRule_thy_section (acc : List Formula) (f : Formula) (k : Nat)
    (hstep : stepConcl acc (Rule.thy k) = some f) :
    ∃ k', And (decodeRule acc f (lineJustif acc (Rule.thy k)) = some (Rule.thy k'))
      (And (stepConcl acc (Rule.thy k') = some f)
           (lineJustif acc (Rule.thy k') = lineJustif acc (Rule.thy k))) := by
  have hmem : axioms[k]? = some f := hstep
  have hsome : (findIdx f axioms).isSome = true := findIdx_isSome_of_getElem f axioms k hmem
  rcases hk' : findIdx f axioms with _ | k'
  · rw [hk'] at hsome; simp at hsome
  · exact ⟨k', by rw [decodeRule_thy_eq, hk']; rfl,
                  findIdx_sound f axioms k' hk', rfl⟩

theorem decodeRule_mp_eq (acc : List Formula) (f : Formula) (i j : Nat) :
    decodeRule acc f (lineJustif acc (Rule.mp i j)) =
      (findIdx (acc[j]?.getD Formula.bottom) acc).bind fun j' =>
        (findIdx (Formula.impl (acc[j]?.getD Formula.bottom) f) acc).map fun i' => Rule.mp i' j' := by
  simp only [lineJustif, decodeRule, peelArgs_cons, peelArgs_nil, decodeNat_numeralM,
    decodeRuleTag, decodeForm_formCode, Option.bind]

theorem decodeRule_mp_section (acc : List Formula) (f : Formula) (i j : Nat)
    (hstep : stepConcl acc (Rule.mp i j) = some f) :
    ∃ i' j', And (decodeRule acc f (lineJustif acc (Rule.mp i j)) = some (Rule.mp i' j'))
      (And (stepConcl acc (Rule.mp i' j') = some f)
           (lineJustif acc (Rule.mp i' j') = lineJustif acc (Rule.mp i j))) := by
  -- extraer acc[i]? = some fi, acc[j]? = some fj0, mpConcl fi fj0 = some f
  simp only [stepConcl] at hstep
  rcases hi : acc[i]? with _ | fi
  · rw [hi] at hstep; simp at hstep
  rcases hj : acc[j]? with _ | fj0
  · rw [hi, hj] at hstep; simp at hstep
  rw [hi, hj] at hstep
  simp only [Option.bind] at hstep
  have hfi : fi = Formula.impl fj0 f := mpConcl_eq hstep
  -- premisa buscada = acc[j]?.getD ⊥ = fj0
  have hgetD : acc[j]?.getD Formula.bottom = fj0 := by rw [hj]; rfl
  -- las dos búsquedas tienen éxito
  have hsj : (findIdx fj0 acc).isSome = true := findIdx_isSome_of_getElem fj0 acc j hj
  have hii : acc[i]? = some (Formula.impl fj0 f) := by rw [hi, hfi]
  have hsi : (findIdx (Formula.impl fj0 f) acc).isSome = true :=
    findIdx_isSome_of_getElem (Formula.impl fj0 f) acc i hii
  rcases hj' : findIdx fj0 acc with _ | j'
  · rw [hj'] at hsj; simp at hsj
  rcases hi' : findIdx (Formula.impl fj0 f) acc with _ | i'
  · rw [hi'] at hsi; simp at hsi
  refine ⟨i', j', ?_, ?_, ?_⟩
  · rw [decodeRule_mp_eq, hgetD, hj', Option.bind, hi']; rfl
  · -- stepConcl acc (mp i' j') = some f
    show (acc[i']?).bind (fun fi' => (acc[j']?).bind (fun fj' => mpConcl fi' fj')) = some f
    rw [findIdx_sound (Formula.impl fj0 f) acc i' hi', findIdx_sound fj0 acc j' hj']
    simp [Option.bind, mpConcl]
  · -- re-encoding: lineJustif (mp i' j') = lineJustif (mp i j)
    show cons (numeralM 16) (cons (formCode (acc[j']?.getD Formula.bottom)) nil) =
         cons (numeralM 16) (cons (formCode (acc[j]?.getD Formula.bottom)) nil)
    rw [findIdx_sound fj0 acc j' hj', hj]

theorem decodeRule_gen_eq (acc : List Formula) (f : Formula) (i : Nat) :
    decodeRule acc f (lineJustif acc (Rule.gen i)) =
      (findIdx (acc[i]?.getD Formula.bottom) acc).map fun i' => Rule.gen i' := by
  simp only [lineJustif, decodeRule, peelArgs_cons, peelArgs_nil, decodeNat_numeralM,
    decodeRuleTag, decodeForm_formCode, Option.bind]

theorem decodeRule_gen_section (acc : List Formula) (f : Formula) (i : Nat)
    (hstep : stepConcl acc (Rule.gen i) = some f) :
    ∃ i', And (decodeRule acc f (lineJustif acc (Rule.gen i)) = some (Rule.gen i'))
      (And (stepConcl acc (Rule.gen i') = some f)
           (lineJustif acc (Rule.gen i') = lineJustif acc (Rule.gen i))) := by
  simp only [stepConcl] at hstep
  rcases hi : acc[i]? with _ | g0
  · rw [hi] at hstep; simp at hstep
  rw [hi] at hstep
  simp only [Option.map] at hstep
  -- hstep : some (∀ g0) = some f  ⟹  f = ∀ g0
  injection hstep with hf; subst hf
  have hgetD : acc[i]?.getD Formula.bottom = g0 := by rw [hi]; rfl
  have hsi : (findIdx g0 acc).isSome = true := findIdx_isSome_of_getElem g0 acc i hi
  rcases hi' : findIdx g0 acc with _ | i'
  · rw [hi'] at hsi; simp at hsi
  refine ⟨i', ?_, ?_, ?_⟩
  · rw [decodeRule_gen_eq, hgetD, hi']; rfl
  · show (acc[i']?).map Formula.forall = some (Formula.forall g0)
    rw [findIdx_sound g0 acc i' hi']; rfl
  · show cons (numeralM 17) (cons (formCode (acc[i']?.getD Formula.bottom)) nil) =
         cons (numeralM 17) (cons (formCode (acc[i]?.getD Formula.bottom)) nil)
    rw [findIdx_sound g0 acc i' hi', hi]


/-! ### Ensamblaje: la cadena decodificada VERIFICA (solidez) ⟹ puente a `Prf`

La pieza que `VerifierSound` (módulo E) consume: si `decodeChain` acepta un código, las reglas que
produce **son una derivación válida** (`checkProof` tiene éxito), y por tanto —vía la solidez meta ya
existente `derivation_to_prf`— cada una de sus conclusiones es `Prf`. Clave: `decodeLine` verifica
`stepConcl acc r = some f`, así que el acumulador que `decodeChainAux` hila coincide con el de
`checkAux`. (Ojo: esto es **solidez**, no el retract sintáctico `proofCode' rs = t`, que `peelArgs`
no garantiza para códigos con «cola basura».) -/

/-- `decodeLine` sólo acepta líneas cuya regla **concluye** la cabeza. -/
theorem decodeLine_sound {acc : List Formula} {lineT : Term} {f : Formula} {r : Rule}
    (h : decodeLine acc lineT = some (f, r)) : stepConcl acc r = some f := by
  cases lineT with
  | var n => simp [decodeLine] at h
  | func cs args =>
      match args, h with
      | [], h => simp [decodeLine] at h
      | [_], h => simp [decodeLine] at h
      | [conclT, justifT], h =>
          simp only [decodeLine] at h
          by_cases hcs : (cs == cons_sym) = true
          · rw [if_pos hcs] at h
            rcases hcf : decodeForm conclT with _ | f'
            · rw [hcf] at h; simp at h
            · rw [hcf] at h; simp only [Option.bind] at h
              rcases hdr : decodeRule acc f' justifT with _ | r'
              · rw [hdr] at h; simp at h
              · rw [hdr] at h; simp only [Option.bind] at h
                by_cases hst : stepConcl acc r' = some f'
                · rw [if_pos hst] at h; injection h with h; rw [Prod.mk.injEq] at h
                  obtain ⟨hf, hr⟩ := h; subst hf hr; exact hst
                · rw [if_neg hst] at h; simp at h
          · rw [if_neg hcs] at h; simp at h
      | _ :: _ :: _ :: _, h => simp [decodeLine] at h

/-- **Solidez de `decodeChainAux`**: una cadena decodificada verifica bajo su acumulador. -/
theorem decodeChainAux_checkAux (t : Term) (acc : List Formula) :
    ∀ (rs : List Rule), decodeChainAux acc t = some rs → ∃ L, checkAux rs acc = some L := by
  fun_induction decodeChainAux acc t with
  | case1 acc s hs =>
      intro rs h; simp only [Option.some.injEq] at h; subst h
      exact ⟨acc, by simp [checkAux]⟩
  | case2 acc s hs => intro rs h; simp at h
  | case3 acc s lineT rest hs ih =>
      intro rs h
      rcases hl : decodeLine acc lineT with _ | ⟨f, r⟩
      · rw [hl] at h; simp at h
      · rw [hl] at h; simp only [Option.bind] at h
        rcases hc : decodeChainAux (acc ++ [f]) rest with _ | rs'
        · rw [hc] at h; simp at h
        · rw [hc] at h; simp only [Option.map] at h; injection h with h; subst h
          have hstep : stepConcl acc r = some f := decodeLine_sound hl
          obtain ⟨L, hL⟩ := ih (f, r) rs' hc
          exact ⟨L, by simp only [checkAux, hstep, hL]⟩
  | case4 acc s lineT rest hs => intro rs h; simp at h
  | case5 t acc h1 h2 => intro rs h; simp at h

/-- **Solidez de `decodeChain`**: lo que decodifica es una **derivación válida**. -/
theorem decodeChain_checkProof {t : Term} {rs : List Rule}
    (h : decodeChain t = some rs) : ∃ L, checkProof rs = some L :=
  decodeChainAux_checkAux t [] rs h

/-- **Puente a `Prf`** (lo que consume el módulo E): si `φ` está entre las conclusiones de una cadena
    que `decodeChain` acepta, entonces `Prf φ`. -/
theorem decodeChain_prf {t : Term} {rs : List Rule} {φ : Formula}
    (h : decodeChain t = some rs) (hmem : ∀ L, checkProof rs = some L → φ ∈ L) : Prf φ := by
  obtain ⟨L, hL⟩ := decodeChain_checkProof h
  exact derivation_to_prf ⟨L, hL, hmem L hL⟩

end ROBINSON_PlusPlus.Meta.ChainDecode

export ROBINSON_PlusPlus.Meta.ChainDecode (
  decodeForm_formCode decodeTerm_termCode
  peelArgs peelArgs_nil peelArgs_cons
  decodeRuleTag decodeRule decodeLine decodeChainAux decodeChain
  cleanRule decodeRule_lineJustif_clean
  findIdx findIdx_sound findIdx_isSome_of_getElem
  decodeRule_thy_eq decodeRule_mp_eq decodeRule_gen_eq
  decodeRule_thy_section decodeRule_mp_section decodeRule_gen_section
  decodeLine_sound decodeChainAux_checkAux decodeChain_checkProof decodeChain_prf
)
