# Inventario del plan de Rosser: NegNum y PosNum de T

**Last updated:** 2026-10-16 — registro (ADR‑146): el informe final de un agente de sólo lectura, CONDENSADO (las citas y las cifras, tal cual). Lo que
dice del árbol es de esa fecha (HEAD `24e3b55`); no se actualiza.

Nothing was modified or compiled. This was read-only: Read, Grep and git reads at HEAD `24e3b55`.

**Tags:** **[R]** = read in the cited document; **[T]** = checked today in the code; **[I]** = my own inference.

**Abbreviations** (root `E:/dropbox/github/lean4/ROBINSON_PlusPlus/`): D130 = `doc/historia/DECISIONS-001-130.md`;
DEC = `DECISIONS.md`; RJ = `doc/registro/2026-10-05-adr122-d7-rosser/resultado.json`; INF =
`doc/registro/2026-10-14-t01-rosser/informe.md`; AUD = `doc/AUDITORIA-SUELO-2026-10-12.md`; NSH =
`doc/historia/NEXT-STEPS-hasta-2026-10-14.md`; PNV = `PLAN-NEGVERIFIER.md`; SRR = `sondeos/RosserReflexion.lean`;
SRB = `sondeos/RosserBasura.lean`; M/ = `ROBINSON_PlusPlus/Meta/`; Ax = `ROBINSON_PlusPlus/Minimal/Axioms.lean`.

**The plan only exists as a registro.** The stages are RJ:230-279, the risks RJ:280-289, the recommendation RJ:290
and the critique RJ:292 (one long line with §ROSSER 1-5). ADR-122 §2 (D130:9373-9382) only summarizes it. T01 asked
for it to be versioned as `doc/PLAN-ROSSER.md` (AUD:171), and that file does not exist.

**Nothing of Rosser is built.** No `.lean` file declares NegNum, PosNum, `rosser_de` or `rosser_ext`; the names only
appear in prose (SRR:36,38; `sondeos/ExtensionPorReduccion.lean:20`) [T].

## (a) The stage plan as it stands

| Stage (RJ name) | Status | Estimate as written [R] |
|---|---|---|
| Etapa 0 «Sondeo (sondeos/), antes de tocar Meta/» | PARCIAL | «120–200 líneas (ESTIMACIÓN)» |
| Etapa 1 «Evaluación externa de la capa de listas sobre numerales» | FALTA | «150–250 líneas (ESTIMACIÓN)» |
| Etapa 2 «NumEval por reflexión» | H done but excluded; P FALTA | «100–180 líneas (ESTIMACIÓN). Ruta P: 350–600.» |
| Etapa 3 «GuardNeg: refutación hereditaria de hasWit/hasWitF» | PARCIAL (cases only) | «350–550 líneas (ESTIMACIÓN)» |
| Etapa 4 «NegLineWF: ¬lineWFN V₀ x ⇒ Prf ¬lineWF x̄» | FALTA | «450–650 líneas (ESTIMACIÓN)» |
| Etapa 5 «NegChain y NegNum (y un dividendo)» | FALTA | «150–250 líneas (ESTIMACIÓN)» |
| Etapa 6 «PosNum» | FALTA | «70–120 líneas (ESTIMACIÓN)» |
| Etapa 7 «Rosser» | FALTA (the pieces it uses exist) | «150–250 líneas (ESTIMACIÓN)» |

**Etapa 0** (RJ:232-235). Goal: three proofs of concept (reflection for substfc/liftfc; «una refutación de guarda de
profundidad 2»; «una línea q1 con ranura basura y conclusión de forma correcta»). Estimate «120–200 líneas
(ESTIMACIÓN)»; measured 406 file lines / 194 declaration lines (D130:9589-9591, :9625; INF:67-70).
* 0.1 Reflection — HECHO, only by route H: `prf_eval_substfc_num` SRR:128, `prf_eval_liftfc_num` SRR:143; calls
  `prf_sound` at SRR:130, 145, 156, 162 and W1 at SRR:119-123. ADR-145 keeps it only as a measurement and a T08
  mutant. Its syntactic replacement is FALTA: the «calibración de la ruta P en UNA etiqueta» (AUD:104-109),
  «100–250 (cifra del crítico)» (AUD:172; INF:205).
* 0.2 Depth-2 guard — PARCIAL (cases only): `prf_neg_hasWit_zero` SRB:84, `prf_neg_hasWit_tag` :95,
  `prf_neg_hasWit_num` :121, `prf_neg_hasWit_prof2` :167. Missing: the general hereditary version by induction on the
  numeral; a good tag with a bad shape; anything on `hasWitF` (D130:9586-9588; SRB:41-43; NSH:26-28).
* 0.3 Junk q1 line — FALTA (D130:9588-9589, :9624; T64 at AUD:929). Remaining Etapa 0 work = T64: «ESTIMACIÓN:
  300–700 líneas» (AUD:932).

**Etapa 1** (RJ:238-241). Split a numeral into `cons`; «lenc/nthc (i<len)/carc/concat/runFn nil de un numeral =
numeral»; ¬In and ¬allIn on numeral lists; rewrite a numeral line as `cons c̄ (cons K̄ (objList args))`; a generic
evaluator of constructor terms. «150–250 líneas (ESTIMACIÓN)», risk «Bajo». FALTA (RJ:195). Pieces [T]:
`prf_cons_eval` M/CodeNumeralPrf.lean:102, `prf_cons_eval_of` :117, `prf_in_cons_iff` M/ChainPrf.lean:359,
`prf_not_in_nil` :367, `crit_num_ne` M/CodeWitnessPrf.lean:176, `prf_lt_numeralM` M/LineWFTrackedPrf.lean:554,
hand-written instances SRB:136-164.

**Etapa 2** (RJ:244-247). Route H: evaluate substfc/liftfc on numerals by reflection. Route P: «la evaluación
SINTÁCTICA sobre numerales: un análogo de ArithPrf.lean:181-475 con un predicado de "código bien formado" sobre Nat».
«100–180 líneas (ESTIMACIÓN). Ruta P: 350–600.» Base that exists: `prf_substTerm_arith`, `prf_liftTerm_arith`,
`prf_substFormula_arith`, `prf_liftFormula_arith` at M/ArithPrf.lean:181, :267, :361, :449 (CANONICAL codes only).

**Etapa 3** (RJ:250-253). GuardNeg: bad shapes on numerals; the ℕ characterization of the guards; term side by strong
induction on the numeral with an open witness; formula side (8 `lorAll` clauses, two witnesses); `ex_elim`
wrappers. «350–550 líneas (ESTIMACIÓN)» + «+60–150» for 3(c) in ℕ on route P (RJ:292 §ROSSER 1.4). Risk «Medio-alto».
PARCIAL (Etapa 0.2 cases only). Build pieces [T]: `prf_crit_In_rejects_open1` M/CodeWitnessPrf.lean:1150,
`crit_isTC1_junk_refuted_open` :1174, `CRIT_isFC1_rejects_varc` :1605, `prf_isTermCodeE1_of_In` :706,
`prf_isTermCodeE1_str` :316, `PrfH_inst_argsIn` :600, `crit_cOk2_absurd` :192, `prf_ex_elim_imp`
M/HilbertDeduction.lean:172, `prf_boundedIn_of_In` M/BoundedInPrf.lean:309, `prf_in_nthc`
M/SubstfcWitnessPrf.lean:555. hasWitF precedents only archived and non-compiling.

**Etapa 4** (RJ:256-259). NegLineWF: x = 0; length < 2; tag ≥ 21; wrong arity; the 19 structural tags; thy («prf_ancla,
¬In sobre listFormCodeM axioms …, y V₀_eq_codigo»); «las 8 proyecciones lineWF⇒guarda nuevas». «450–650 líneas
(ESTIMACIÓN); conviene partirlo en 2 módulos»; projections «unas 96 líneas». FALTA. Projections: 3 of 11 exist
(`prf_lineWF_q1_hasWit` M/ReprPrf.lean:1016, `prf_lineWF_q2_hasWit` :1029, `prf_lineWF_leibniz_hasWitF` :1042). The
thy-case template `prf_not_In_listFormCodeM` was retired with AxiomListCode (ADR-115), template in `pre-adr115`.
Pieces: `prf_lineWF_cons` M/LineWFConsPrf.lean:34, `prf_lineWF_inv` M/Sigma1AtomPrf.lean:369, `prf_of_tagDisj`
M/LineWFAssemblePrf.lean:55, `pcc_tag_vacuous` M/SubstTreeReflect.lean:1159, `tagConcl` and `prf_lineWF_neg_of_tag`
M/LineWFCases.lean:75, :224, `prf_ancla` M/Representability2Prf.lean:157.

**Etapa 5** (RJ:262-265). NegChain and NegNum; NegNum' (¬Prf φ ⇒ ∀q, Prf ¬Pf(q̄,⌜φ⌝)) «por la contrapositiva de W1»;
the dividend ∀n, Prf ¬Pf(n̄,⌜⊥⌝). «150–250 líneas (ESTIMACIÓN)». FALTA. Pieces: `prf_chainOk_iff_chainOkB`
M/ChainOkBoundedPrf.lean:832, `prf_lineWF_of_chainOk` M/D3BodyPrf.lean:80, `prf_boundedPremsIn_of_chainOk`
M/ChainNegPrf.lean:223; ChainNegPrf has 1 617 lines, 107 theorems, 30 `prf_*` (RJ:165: «29 de los 30 sirven sobre
numerales»). W1 (`verificador_solido` M/SolidezVerificador.lean:524) reaches the model only through `linea_thy` →
`V₀_eq_codigo`; W1(V) does not exist; «ESTIMACIÓN 15–30 líneas» (RJ:292; AUD:1034-1035).

**Etapa 6** (RJ:268-271). PosNum: ∃n, Prf (`proofCode' rs []` =eq numeral n), then Leibniz. «70–120 líneas
(ESTIMACIÓN)», risk «Bajo»; the critique says «40–80». FALTA: «Ningún lema `proofCode' … =eq numeral`» (RJ:206-209;
INF:66). Pieces: `repr_pos'_prf` M/Representability2Prf.lean:462 (in PUROS), `prf_chainOk_track` :245.

**Etapa 7** (RJ:274-277). ρ(x) := ∀y (Pf(y,x) → ∃z (le z y ∧ Pf(z, ¬x))), R by `prf_diagonal`; ⊬R by
`prf_bdAll_numeral`; ⊬¬R by `prf_lt_trichotomy`. «150–250 líneas (ESTIMACIÓN). Total de la ruta H: unas 1 400–2 250;
ruta P: 250–450 más.» Risk «El numeral de ⌜R⌝ es astronómico». Pieces done: `prf_diagonal` M/TarskiPrf.lean:49,
`prf_bdAll_numeral` M/CodeWitnessPrf.lean:870, `prf_lt_trichotomy` M/NatMulPrf.lean:295. Superseded by `rosser_ext`
over `PrfH E` (ADR-145), with Pf_E transport «200–400 líneas» (ESTIMACIÓN, ADR-144). Obligations (INF:73-79):
`IsSentence R`; R in `EV_TOK`; no simp/rfl/decide on ⌜R⌝.

**Totals as labelled in the sources:** route H «ESTIMACIÓN 1 400–2 250 líneas en siete etapas» (D130:9381); route P
«250–450 líneas más» (RJ:131), flagged as unlabelled by the critique; critique: route H «probablemente optimista»,
route P = H + 250–450 + 60–150; the old NegVerifier was 3 214 lines (MEDIDO, RJ:170); INF:218 «≈1 710–2 850 en
total». Calibration: W1 estimated 600–1 500, came in at about 490 (RJ:141); Etapa 0 estimated 120–200, is at 406
file / 194 declaration lines with 2 of 3 pieces (INF:222).

## (b) Known risks and obstacles for NegNum

1. GuardNeg is the riskiest piece (RJ:282; «Medio-alto», RJ:253): De Bruijn bookkeeping under ∃∃, 8 disjuncts,
   mutual term/formula recursion.
2. GuardNeg looks unavoidable, but only by an uncompiled model argument: the 142 axioms do not fix substfc on a junk
   slot (RJ:212-215, :287; RJ:292 §ROSSER 1.7). T75(d) proposes a second model as a test (AUD:1034).
3. The guards are Σ₁, so refuting them is Π₁ work; their refutation cannot come from Σ₁-completeness (RJ:292
   §ROSSER 1.2; ADR-124 §2.3, D130:9498).
4. Route purity: route H uses `prf_sound` in auxiliary lemmas, plus W1 through `V₀_eq_codigo` (RJ:283).
5. Huge numerals and kernel traps: ∀-lemmas, `rw` by hand, never simp/rfl/decide (RJ:284); the ADR-124 trap
   (`simp … at h` on closed codes: >14 GB; workaround: closed codes as variables of a `rfl` lemma, D130:9462-9478);
   log₂ of the code of `ax_tc_cons` ≈ 8,66·10⁷⁸ (INF:228); never `rfl` against V₀.
6. The ADR-130 kernel trap: `dsimp`/`simp only` on a mutual structural recursion is rejected; fix with `unfold` and
   functional induction (D130:9801-9817; T77). [I] Relevant to GuardNeg's mutual recursion.
7. Memory: split the 21-tag dispatch over numerals into modules («olean.private»/3221226505, RJ:285).
8. Precedents broken or with the wrong sign (archived hasWitF refuters; q1 precedents «tienen el signo contrario»,
   AUD:929; T18 renames).
9. T08 blind spots: by namespace only; must be applied to the INSTANCE, not to `rosser_de` (INF:225); `#print axioms`
   does not tell the routes apart.
10. The thy case as planned uses `V₀_eq_codigo` (impure); the way out is the Nat-level route or stating the oracle
    with `codeNatList axioms` (INF:183-185; RJ:292 D7 §1.4).

## (c) Syntactic vs through the model

Allowed under T08: RosserBasura §1–§4 (by reading); the build pieces of Etapas 1, 3, 4, 6 and 7; D1 (in PUROS);
ChainNegPrf's `prf_*`; the transport base (`prfH_iff_prf_impChain`, `formCode_impChain`); the Nat oracle
(`ModeloCodigo`: V₀, chainOkN, lineWFT, hasWitN, hasWitFN, codeNatList). Through the model: all of RosserReflexion;
RosserBasura §5; W1 through `linea_thy`; in the plan, Etapa 2 by route H, 3(c) by soundness, Etapa 4 thy via
`V₀_eq_codigo`, Etapa 5's NegNum' through W1. **[I] Key consequence:** Rosser's ⊬R half needs NegNum' on ¬R, which
only follows from ¬Prf ¬R through the contrapositive of W1, so a pure W1(V), instantiated with `codeNatList axioms`,
is on NegNum's critical path.

## PLAN-NEGVERIFIER

It planned `NegVerifier` over the retired ⊢ layer, in six modules (PNV:360-389), «~1 900–2 700 líneas · 8–11
sesiones» (PNV:714), revised to «~800‑1 300» (PNV:116). It went wrong in two places (`canon_ne` false; footprint
with refuted meta-rules, retired with ADR-115). Reusable only as a guide: the case tree of module C (PNV:566-577), the
runFn/¬In/¬chainOk structure of module D (PNV:597-617), the accepted/rejected split of module F (PNV:672-684), the
traps of §11 (PNV:729-740).

## Discrepancies

«5 usos de prf_sound» (AUD:170): RosserReflexion has 4 calls plus one docstring mention; AUD:105 cites SRR:126-127,
the statement is at :128-129; ADR-144 cites «1 400 a 2 850», the informe gives H 1 400–2 250 and P ≈1 710–2 850; SRB
cites `sondeos/MedirC_*.lean`, now archived; AUD T64 cites `NEXT-STEPS.md:26-28`, now NSH:26-28.
