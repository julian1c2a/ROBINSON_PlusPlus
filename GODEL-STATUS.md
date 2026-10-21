# Frente Gödel — estado y mapa

> **Estado actual:** el banner de [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) es la fuente única (T33, [ADR‑142](DECISIONS.md)).
> Los banners que se apilaban aquí están, tal cual, en [doc/historia/BANNERS.md](doc/historia/BANNERS.md).

**Last updated:** 2026-10-21 — [ADR‑185](DECISIONS.md) (T28): reescrito entero. El documento de antes —escrito el
2026‑06‑06 para el Nivel C con meta‑axiomas, con su «Resumen al día» del 2026‑07‑20 y un §4 que declaraba fuera de
alcance lo que hoy está demostrado— está, tal cual, en
[doc/historia/GODEL-STATUS-hasta-2026-10-21.md](doc/historia/GODEL-STATUS-hasta-2026-10-21.md).
**Author:** Julián Calderón Almendros

Este documento responde a tres preguntas: *¿de qué teoría hablan los teoremas de Gödel de este repositorio y qué
hipótesis de Gödel cumple?, ¿qué está formalizado?, ¿cómo se encadenan las pruebas?* Lo vigente, con la hipótesis de
cada teorema y quién la descarga, es [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) §1: si algo de aquí discrepa,
manda TEOREMAS.

---

## 1 · La teoría, y las hipótesis de Gödel

El sujeto no es la lista de `Minimal/` (sin esquema de inducción) sino **T_Prf**, lo que deriva el cálculo finitario
`Prf` (`Meta/Hilbert.lean`): los 142 axiomas de la lista `axioms`, los esquemas lógicos (con DNE y el confinamiento),
y la inducción y la inducción de listas para TODA fórmula, con MP y GEN. Contiene a PA. La descripción canónica, y lo
que se supone, en [AXIOMS.md](AXIOMS.md) §0.

| hipótesis de Gödel | cómo la cumple T_Prf | dónde |
|---|---|---|
| **axiomatización recursiva** | los 142 son una lista explícita (`axioms_len : axioms.length = 142`, por `rfl`), y lo que es una prueba lo decide un verificador interno (`validProofFn` y `chainOk`) | `Minimal/Axioms.lean`, `Full/Induction.lean`, `Meta/ProofChain.lean` |
| **la aritmetización** | los códigos son numerales (`codeNat`, `numeral`; la reparación de ADR‑012/013), `formCode` codifica las fórmulas y `provCodeC'` es el predicado de prueba | `Minimal/Axioms.lean`, `Meta/Provability.lean`, `Meta/CodeNumeralPrf.lean`, `Meta/ProofChain.lean` |
| **las condiciones de derivabilidad** | D1 `repr_pos'_prf`, D2 `d2_prf` y D3 `d3_prf_real`: teoremas, ninguna postulada; D3 es la Σ₁‑completitud demostrable del verificador | `Meta/Representability2Prf.lean`, `Meta/DerivCondPrf.lean`, `Meta/PremsBdAllPrf.lean` |
| **el punto fijo** | `prf_godelCN_fixedpoint` para la sentencia de Gödel `godelCN`, y `prf_diagonal` para un predicado cualquiera | `Meta/GodelTwoPrf.lean`, `Meta/TarskiPrf.lean` |
| **la consistencia** | el TEOREMA `consistencia : ConsistentH`, por un modelo de los 142 (`MNV V₀`) y la solidez de `Prf` (`prf_sound`). Relativa a Lean: PRA ⊢ Con(Lean) → Con(T_Prf) ([TEOREMAS](TEOREMAS-E-HIPOTESIS.md) §4) | `Meta/Consistencia.lean`, `Meta/SolidezPrf.lean` |
| **para `⊬¬G`, más que la consistencia** | la verdad en ℕ en vez de la ω‑consistencia: el verificador es sólido en el modelo (W1, `verificador_solido`) | `Meta/SolidezVerificador.lean` |

---

## 2 · Lo formalizado

| resultado | teoremas | qué usa la prueba ([TEOREMAS](TEOREMAS-E-HIPOTESIS.md) §1) |
|---|---|---|
| **Gödel I** | `goedel_first_prf (hcon : ConsistentH) : ¬ Prf godelCN`; sin hipótesis, `goedel_I`; la otra mitad, `goedel_I_neg : ¬ Prf ¬godelCN`; las dos juntas, `godelCN_indecidible` | (i) · (ii) · (iii) |
| **Gödel II** | `goedel_second_prf (hcon : ConsistentH) : ¬ Prf consistencyFormula'`; sin hipótesis, `goedel_II`; dentro de la teoría, `goedel_second_formalizado`; `prf_godel_iff_con` (G ⇔ Con') y `con_indecidible` | (i) · (ii) · (iii) |
| **Rosser** | `rosser`: ni R ni ¬R, desde la consistencia simple; `rosser_ext`, para toda extensión finita consistente T+E, por reducción a T (`prfH_iff_prf_impChain`) | (ii) · (i) |
| **Tarski** | `prf_tarski` y `tarski` (la teoría no define su verdad: el mentiroso, `liar`); `tarski_semantico` y `tarski_semantico_de`: ninguna fórmula define la verdad en ningún modelo estándar | (i) · (ii) · (iii) |
| **Löb** | `lob : Prf (Prov⌜φ⌝ ⇒ φ) → Prf φ`; Gödel II sale de él (`goedel_second_de_lob`) | (i) |
| **la verdad de G y de Con** | `godelCN_verdadera`, `con_verdadera` (E10), y en todo modelo estándar `godelCN_verdadera_de`, `con_verdadera_de`; los modelos estándar no son uno solo (`estandar_MN`, `estandar_MB`) | (iii) |

Lo que este frente declaraba fuera de alcance en junio —la demostración interna de Gödel II, Rosser y Tarski— está
hecho. Fuera de este repositorio: Gentzen (ε₀), que nacerá en el suyo (ADR‑140, T69).

---

## 3 · Cómo se encadenan

```text
codificación (formCode, codeNat) ─► verificador interno (validProofFn, chainOk, provCodeC')
        │                                   │
        ▼                                   ▼
punto fijo (prf_godelCN_fixedpoint)    D1 · D2 · D3  ───────────────► goedel_first_prf, goedel_second_prf,
        │                                                              prf_godel_iff_con, lob
        │                              W1(ax), PosNum, NegNum (los espejos en ℕ del verificador) ─► rosser_ext
        ▼
modelo MNV V₀ + solidez prf_sound ─► consistencia ─► goedel_I, goedel_II, tarski, rosser (sin hipótesis)
        │
        ├─► la verdad en el modelo: W1 (verificador_solido) y E10 ─► goedel_I_neg, con_indecidible
        └─► la semántica del modelo ─► tarski_semantico, tarski_semantico_de
```

La clase de cada titular —(i) sin el modelo, (ii) el modelo sólo para la consistencia, (iii) la verdad en el modelo—
la comprueba cada build para la (i) (`Meta/PurezaTitulares.lean`, T08), y los enunciados de los 29 titulares los fija el
contrato (`Meta/ContratoTitulares.lean`, T07).

---

## 4 · La historia, en cuatro líneas

La reparación de los códigos (ADR‑012/013) y la retirada de la capa `⊢`, que era sintácticamente completa y no podía ser
sujeto de incompletitud (ADR‑115); el ancla de la codificación, teorema (ADR‑117); el modelo y la consistencia, Gödel I y
II sin hipótesis (ADR‑120); `⊬¬G` y Tarski (ADR‑121); Rosser (ADR‑157); Löb (ADR‑159); los corolarios de Gödel II
(ADR‑162). El detalle, en [DECISIONS.md](DECISIONS.md) y en [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md).

## 5 · Referencias

- Gödel, K. (1931). *Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I*.
- Smullyan, R. (1992). *Gödel's Incompleteness Theorems*. Oxford University Press.
- Boolos, G., Burgess, J., Jeffrey, R. (2007). *Computability and Logic* (5ª ed.). Cambridge. — Capítulos 17‑18.
- [Incompleteness theorems — Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/goedel-incompleteness/)
