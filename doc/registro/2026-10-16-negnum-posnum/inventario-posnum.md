# Inventario de PosNum

**Last updated:** 2026-10-16 — registro (ADR‑146): el informe final de un agente de sólo lectura, CONDENSADO (las
citas, los enunciados y las referencias fichero:línea, tal cual). Lo que dice del árbol es de esa fecha (HEAD
`24e3b55`); no se actualiza.

Read-only; nothing compiled. **READ** = seen in the source; **INFERRED** = the agent's reasoning, not checked by Lean.
Paths are relative to `ROBINSON_PlusPlus/Meta/` unless said otherwise.

**Short answer.** D1 already builds an explicit closed proof-code **term**, `proofCode' rs []`, and proves both halves
of Pf for it. The only real gap to PosNum is one lemma never written: that this term equals a numeral,
`Prf (proofCode' rs acc =eq numeral n)`. All the other pieces exist and are model-free. The audit sentence «no hay
ningún lema `proofCode' … =eq numeral`» is still true.

## 1. `repr_pos'_prf` and its proof (READ)

`theorem repr_pos'_prf {φ : Formula} (h : Prf φ) : Prf (provCodeC' φ)` (Representability2Prf.lean:462). Proof
(463-466):
```lean
obtain ⟨rs, L, hchk, hmem⟩ := prf_iff_derivation.mp h
have hchk' : checkAux rs [] = some L := by simpa [checkProof] using hchk
exact provCodeC'_intro_prf φ (proofCode' rs [])
  (prf_chainOk_track rs [] L hchk') (prf_In_runFn_of_mem hchk' hmem)
```
* The witness P = `proofCode' rs []` is a cons-tree TERM, not a numeral.
* The ∃ is introduced in `provCodeC'_intro_prf (φ) (p : Term) (h1 : Prf (chainOk nil p)) (h2 : Prf (In (formCode φ)
  (runFn nil p))) : Prf (provCodeC' φ)` (445-457). The Pf body for P is only a local `have hbody` (448-449), not
  exported.
* Encoders: `lineJustif acc : Rule → Term` (Representability2.lean:60-82), 21 cases, tags `numeralM 0…20`;
  `lineCode' acc f r := cons (formCode f) (lineJustif acc r)` (86-87); `proofCode'` (90-95). `Rule`, `stepConcl`,
  `checkAux`, `checkProof`, `Derivation`, `prf_to_derivation`, `prf_iff_derivation` in HilbertSeq.lean (85-402).
  `ruleCode`/`rulesCode`/`Dem`/`dem_tracks` (HilbertSeq.lean:419-473) are a DIFFERENT encoder, unused by D1.
* Key lemmas: `prf_runFn_track` (Representability2Prf.lean:67-68), `prf_In_runFn_of_mem` (96-98),
  `prf_chainOk_track` (245-247, case by case with `prf_lineWF_*`/`prf_premsOf_*` of ReprPrf.lean; the guards are
  discharged by `prf_hasWitF_fc` / `prf_hasWit_tc`, Representability2.lean:120-125).
* Purity: `repr_pos'_prf` is in `PUROS` (PurezaTitulares.lean:45); its cone is 701 declarations / 5 070 lines.

## 2. Codes vs numerals (READ)

* Three numeral functions: `numeralM` (Minimal/Axioms.lean:592-594), `Godel.numeral` (Godel.lean:78-80),
  `Full.numeral` (Full/Numerals.lean:51-53), linked by Lean `=` only: `numeralM_eq` (CheckArith.lean:55),
  `numeral_bridge` (CodeArith.lean:51). `formCode` uses `numeral`; `lineJustif` uses `numeralM`.
* Existing: `prf_cons_eval (a b) : Prf (cons (numeral a) (numeral b) =eq numeral (consN a b))` (CodeNumeralPrf.lean:
  102-106); `prf_cons_eval_of` (117-121); `prf_formCode_numeral : ∀ φ, Prf (formCode φ =eq numeral (codeNat φ))`
  (155-182); `prf_termCode_numeral`/`prf_termsCode_numeral` (138-151); `prf_charsCode_numeral` (130-133);
  `prf_strCode_numeral` (135-136); `prf_termCodeM_numeral` (SubstTreeReflect.lean:171-173).
* The `numeralM` version `prf_cons_evalM (a b) : Prf (cons (numeralM a) (numeralM b) =eq numeralM (consN a b))`
  exists only in a probe (sondeos/RosserBasura.lean:136-140), a CI control.
* Not existing: `prf_cons_numeral`, `prf_consN`, `numeralM_cons`; no numeral lemma for `proofCode'`, `lineCode'`,
  `lineJustif`, `listFormCode`; no Nat mirror of them. The only Nat code for lists is `codeNatList`
  (ModeloCodigo.lean:555-557), with no `Prf` counterpart.

## 3. `stdChain_proofCode'`, `CTree`, `STree` (READ)

`stdChain_proofCode' : ∀ rs acc, ∃ l : List Term, StdChain l ∧ objList l = proofCode' rs acc` (OmegaReflect.lean:
235-252); `Verifies φ t := land (chainOk nil t) (In (formCode φ) (runFn nil t))` (96-97) is exactly Pf(t, ⌜φ⌝). Pure
syntax, outside the cone; the audit's T66 proposes retiring the module. `CTree`/`STree` (CodeTreeReflect.lean:66-71,
SubstTreeReflect.lean:88-96) are reifications of the `lineWF` right-hand sides used by D3; pure syntax, nothing about
proof codes. INFERRED: for PosNum, `stdChain_proofCode'` only documents the leaves to evaluate (`formCode`,
`termCode`, `numeralM k`, `nil`).

## 4. Bounded quantifiers and order (READ; all `Prf`, model-free)

`prf_bdAll_numeral` (CodeWitnessPrf.lean:870-872); `prf_bdAll_of_bound` (900-904); `prf_lt_trichotomy`
(NatMulPrf.lean:295-300); `prf_lt_irrefl` (288); `prf_lt_succ_split` (BoundedInPrf.lean:220-221);
`prf_lt_succ_split'` (BdAllIntroPrf.lean:93); `prf_not_lt_zero` (NatArithPrf.lean:176); `prf_lt_succ_of_lt`
(BdAllIntroPrf.lean:77); `prf_lt_succ_self` (:292); `prf_le_of_lt` (NatOrderPrf.lean:112); `prf_le_refl` (:120);
`prf_lt_numeralM` (LineWFTrackedPrf.lean:554); `crit_num_ne` (CodeWitnessPrf.lean:176-184); `le a b := lt a b ∨ a =eq
b` (Minimal/Axioms.lean:160). Not found: `prf_le_numeral_cases`, any formula-level `prf_bdEx_*`.

## 5. The decoding direction at the META level (READ)

`Prf` is a `Prop`, so there is no function from a derivation to a number; there is `prf_to_derivation : Prf φ → ∃ rs,
Derivation rs φ` (HilbertSeq.lean:383). `runFnN` (ModeloCodigo.lean:504) and `chainOkN V c p` (:608) are pure Nat
arithmetic. The link object ↔ Nat goes only through the model today (`MNV V`, `ev_provCodeC'`, and W1
`verificador_solido`, whose thy case uses `V₀_eq_codigo`). There is no syntactic lemma `chainOkN … → Prf (chainOk …
(numeralM …))`.

## Lo que falta para PosNum (INFERRED, not compiled)

1. The only real gap: `Prf (proofCode' rs acc =eq numeral N)`, with a Nat mirror (`codeNatJustif` / `codeNatLine` /
   `codeNatProof`, copying Representability2.lean:60-95) or as `∃ n`: one lemma for `lineJustif` (21 cases), one for
   `lineCode'` (`prf_cons_eval_of (prf_formCode_numeral f) …`), and the induction over `rs`, the skeleton of
   `prf_runFn_track`. Leaves: `formCode`, `termCode` covered; `numeralM k` by `rw [numeralM_eq]`; `nil` is
   definitionally `numeral 0`.
2. Assembly: `prf_iff_derivation`, then `prf_chainOk_track` and `prf_In_runFn_of_mem`, then transport with
   `prf_chainOk_subst2`, `prf_congr_runFn_2`, `prf_eq_subst_in`, then `prf_and_intro`.
3. A `Pf` definition (two variables, from the matrix at ProofChain.lean:108) and its substitution lemma.
4. Not needed for PosNum: the model, W1, `chainOkN`, the guards.
5. Rosser-side gap: no `z ≤ n̄` case lemma; derivable from `prf_lt_succ_split` + `prf_not_lt_zero`.
6. Risks: no `simp`/`rfl`/`decide` on p; thy lines for the anchor carry `numeralM (codeNat (psiD axiomsBase))`.
7. Acceptance: add the result to `PUROS`.

Measured sizes of the analogues: `prf_formCode_numeral` 28 lines; `prf_termCode_numeral` + `prf_termsCode_numeral`
14; `lineJustif` 23; `proofCode'` 6; `codeNat` 9; `prf_runFn_track` 26; `provCodeC'_intro_prf` 13; `repr_pos'_prf` 5;
`prf_chainOk_track` 196 (reused as is). The project's estimates: PosNum 70–120 lines (resultado.json:270), 40–80
according to the critique (informe.md:208).
