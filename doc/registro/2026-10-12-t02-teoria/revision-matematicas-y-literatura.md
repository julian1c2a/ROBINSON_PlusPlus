# Revisión adversarial de T02 · matemáticas y literatura

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

## Revisión adversarial de T02 / ADR‑134: matemáticas y literatura

Ninguna afirmación nueva es FALSA en sentido estricto. La más grave es la del punto 7, que contradice a la misma fuente que el texto cita (Buss 1998). Hay otras dos inexactitudes de fondo, en los puntos 4 y 8. Lo demás son omisiones de forma.

### Hallazgos

**H1 · INEXACTO (grave) · «Lo que no llega a Q es la VÍA de Hilbert–Bernays–Löb: en Q no se dispone de D3»**
- Dónde: `AXIOMS.md:296-297`, `DECISIONS.md:10202-10203`, `NEXT-STEPS.md:3700`.
- Problema: Buss, *Handbook* cap. II, §2.1.4, dice que los resultados «all hold as well for theories which only contain Q». Basta relativizar `Proof_T(w)` a `J(w) ∧ (Proof_T(w))^J`, donde J es un corte definible en el que Q interpreta S¹₂, y entonces «the proofs given in the next sections all still work». En §2.2.3 enuncia Gödel II para `T ⊇ Q`. Es decir, la vía HBL sí llega a Q con el predicado relativizado. Lo que no se sabe es si D3 vale para el predicado **sin relativizar**.
- Arreglo: «Para el predicado sin relativizar, D3 en Q no se sabe probar. Relativizado a un corte donde vale S¹₂, la vía HBL llega a Q (Buss 1998 §2.1.4 y §2.2.3; Pudlák 1985)».

**H2 · OMISIÓN · la nota dice «una frase FALSA y dos inexactas» (`AXIOMS.md:291`)**
- Problema: quedan sin marcar otras frases del mismo párrafo:
  - el «**Hecho clásico.** Q … no satisface las condiciones de HBL… no prueba su propia Σ₁‑completitud» (`:284-286`). La propia nota dice «que falle, no está publicado».
  - «para D2/D3 hace falta inducción» (`:286`). Con el corte, no hace falta.
  - El «**No.**» de `:281-282`. Por Pudlák, la lista sin inducción (r.e., consistente, contiene a Q) no demuestra su propia consistencia: Gödel II sí vale sin inducción.
- Arreglo: añadir esas tres frases a la nota.

**H3 · INEXACTO · «El título de §1.1 vale para la VÍA que sigue el proyecto» (`AXIOMS.md:304`)**
- Problema: que la inducción sea imprescindible ni siquiera está establecido para la vía. D3 sin inducción, sin relativizar, es una cuestión abierta, y relativizado sale (H1).
- Arreglo: «el título no está justificado: es una conjetura sobre esta vía».

**H4 · INEXACTO · «(es lo esperable, porque `t < h :: t`, por inducción fuerte)» (`AXIOMS.md:134`)**
- Contraejemplo del propio proyecto: con la codificación vieja, `cons a b = pair a (σb)` = T(a+b+1)+b+1 > b, así que `t < h :: t` ya valía. `sondeos/CantorSobreyectivo.lean` dice que la monotonía «sobrevive» al cambio. Aun así, `listInd` daba `Prf ⊥` (ADR‑114 L1‑1), mientras que `ind` con los 141 era verdadero en ℕ. Por tanto, `t < h :: t` no basta.
- Lo que hace falta exactamente, y nada de ello está en la lista:
  - (i) **Exhaustividad**: ∀L (L = nil ∨ ∃h∃t L = h :: t). Por `ax_L0` y Q3 equivale a la sobreyectividad de `pair`. Sale por `ind`: si z = π(x,y) con x>0, entonces σz = π(x−1, y+1); si x=0, σz = π(y+1, 0). Antes hay que probar que s·σs es par y la unicidad de `div2` (`ax17`, `ax21`, `ax24`).
  - (ii) `t < h :: t`, porque `pair h t ≥ t`.
  - (iii) La inducción fuerte, que se deriva de `ind`.
  - Hoy (i) se obtiene **de** `listInd` (`Meta/SubstfcWitnessPrf.lean:409`, `prf_nil_or_cons_all`).
- La conclusión («esperable») sí es correcta.
- Arreglo: «es lo esperable, porque σ∘pair es biyección ℕ²→ℕ≥1 (ADR‑113) —todo número es nil o un `::`— y t < h::t, con inducción fuerte. Con la codificación vieja t < h::t valía y `listInd` daba ⊥».

**H5 · INEXACTO / OMISIÓN · «Parte de ese uso es evitable»**
- Dónde: `AXIOMS.md:177`, `DECISIONS.md:10181`, `sondeos/InduccionTitulares.lean:43`.
- Problema: con el mismo criterio («por lectura»), los **cuatro** puntos de entrada de D1 son evitables, no sólo tres. El cuarto, `prf_mul_le_mono_right`, se deriva así:
  - si x = y, es congruencia;
  - si x < y, `ax13` da x+σk = y. Entonces y·c = c·(x+σk) = c·x + c·σk = x·c + σk·c (`ax10`, `ax12`).
  - Sea b = σk·c y apliquemos Q3 a b. Si b = 0, `ax4` da y·c = x·c. Si b = σd, `ax13` da x·c < y·c.
- Arreglo: «los cuatro son evitables por lectura; que D1 compile sin `ind` no está comprobado».

**H6 · INEXACTO leve · «suficientes, no necesarias (Jeroslow 1973)» (`AXIOMS.md:298`, `DECISIONS.md:10203`)**
- Problema: lo que hizo Jeroslow, según Kurahashi 2020 y el resumen del propio artículo:
  - prescinde de D2 a cambio de **reforzar** D3 (`Pr(t) → Pr(⌜Pr(t)⌝)` para todo término p.r.);
  - eso sólo prueba ⊬ Con^H = ∀x(Fml(x) ∧ Pr(x) → ¬Pr(¬̇x)), no ¬Pr(⌜0≠0⌝);
  - según Kurahashi, {D1, Σ₁C} no basta para ⊬ Con^L;
  - el resumen de Jeroslow dice que lo crucial son «versions of the third derivability condition».
- Arreglo: «hay otros conjuntos suficientes, cada uno para su enunciado de consistencia (Jeroslow 1973: sin D2, con D3 reforzada, para Con^H)».

**H7 · FORMA · «(que falle, no está publicado)» (`AXIOMS.md:297`)**
- Problema: es una negación sobre la literatura sin fuente. La respalda Visser en FOM (30‑09‑2010), según el buscador: «I do not think there is a published proof that one of the HBL conditions fails in Q». Añadía que la pregunta depende de la formalización. No pude abrir el mensaje (404).
- Arreglo: atribuirlo a Visser (FOM, 2010) y acotarlo al predicado sin relativizar.

**H8 · OMISIÓN · la nota de §5 de `MINIMAL-AXIOMS.md` no alcanza a §5.5**
- `MINIMAL-AXIOMS.md:387` dice que I∆₀+Exp es «más débil aún» que EFA. Es falso, porque son la misma teoría, y contradice la corrección de `:355`.
- `:394` dice que la prueba de Gödel I «requiere inducción». Contradice a `AXIOMS.md` §1.1 (Rosser, T ⊇ Q).
- Además, la cadena corregida quita PA⁻, que estaba bien colocado (Q ⊊ PA⁻ ⊊ IOpen ⊊ I∆₀). Es de FORMA.
- Arreglo: extender la nota a §5.5.2 y §5.5.3.

**H9 · OMISIÓN leve · «contiene a PA (por lectura)» (`AXIOMS.md:120`, `DECISIONS.md:10158`)**
- Problema: que estén los axiomas de PA da T_Prf ⊇ axiomas de PA. Para T_Prf ⊇ PA (todos sus teoremas) hace falta además que el cálculo lógico de `Prf` sea completo para FOL⁼ clásica. Lo es por lectura: es un Hilbert estándar con P1, P2, ∧, ∨, EFQ, DNE, Q1–Q3, `qconf`, reflexividad y Leibniz. Pero eso es justo la dirección DerivesSet₀ → Prf del puente T67, que §0.1 lista como inexistente.
- Arreglo: decirlo en una línea.

**H10 · FORMA · `DECISIONS.md:10162-10164`**
- Problema: el paréntesis presenta la parcialidad como si fuera la razón de que la conservatividad sea «una pretensión». No lo es: la parcialidad sólo impide que sea *definicional*. `AXIOMS.md` §0.1 sí separa bien las dos cosas.
- Además, la conservatividad sobre PA es lo esperable por el argumento estándar: se interpretan los símbolos con funciones definibles en PA, rellenando la basura como hace el modelo, y se traduce. Los símbolos libres se interpretan trivialmente. Es decir, no está *demostrada*, pero no es una cuestión abierta.
- Arreglo: separar las dos cosas como en §0.1.

**H11 · FORMA · «(el modelo lo rellena con 0)» (`AXIOMS.md:132-133`)**
- Problema: no es así para `premsOf` ni `validProofFn`. `premsOfN` da `[a⇒c, a]` en toda línea de tag 16, tenga la longitud que tenga. `vpfN` añade `stepN x`, aunque falle la condición de `mp`, `gen` o `thy` (`Meta/ModeloCodigo.lean:491-516`).
- Arreglo: «el modelo elige un valor».

**H12 · OMISIÓN leve · `Minimal/Axioms.lean:817-818`**
- Problema: la nota está en la sección que define `nthc`, pero sólo dice que `carc`/`cdrc` no fijan su valor en `nil`. `nthc(nil, i)` también queda libre; `lenc` sí es total.
- Arreglo: añadir `nthc`.

**H13 · INEXACTO leve · descripciones de la lista que siguen llamándola Q**
- Tres sitios, con notas al lado que los dan por buenos:
  - `AXIOMS.md:82` («≈ Robinson Q»), que la nota de `:85` valida («es cierto de la LISTA»);
  - `ESCALANDO_EL_PROYECTO.md:50` («Robinson Q (34 axiomas)»);
  - `GODEL-D-ARITHMETIZATION.md:54` («Q (= axiomas de Minimal)»).
- Problema: la lista contiene a PA⁻ entero y más. Por ejemplo, demuestra ∀n∃q (n = 2q ∨ n = 2q+1), que PA⁻ no demuestra: en ℤ[X]⁺, X no es par ni impar. Eso contradice §0.1.
- Arreglo: corregir las tres frases.

**H14 · INEXACTO leve · historia de las inconsistencias**
- `PLAN-SORTES.md:17` dice «lo ERA, por `ax_tc_cons`… desde ADR‑120 es consistente». Pero tras ADR‑012 `axioms ⊢ ⊥` seguía derivándose (`ax_list_induction`, L1‑2) hasta ADR‑115. Además, `Prf ⊥` valía con el cons viejo (L1‑1) hasta ADR‑113. ADR‑120 *probó* la consistencia; no la creó.
- `CodeNumeralPrf.lean:32` dice «la inconsistencia que TUVO», en singular.
- Arreglo: listar las inconsistencias y decir que ADR‑120 la probó.

**Detalle de forma:** el ADR cita «III.2.17» y `AXIOMS.md` «III.2.17 y III.2.22». Conviene unificarlo; los metadatos los verificó el otro agente.

### Comprobado y correcto

1. **Q3 sale de `ax2`, `ax5`, `ax13` y `ax19`.** `ax19` en (0, x) da tres casos:
   - 0 = x: es el primer disyunto.
   - 0 < x: `ax13` da ∃k 0+σk = x, y `ax5` da x = σ(0+k).
   - x < 0: `ax13` da x+σk = 0, `ax5` da σ(x+k) = 0, y eso contradice `ax2`.
   - La prueba es intuicionista. «La lista contiene a Q» es correcto: Q1, Q2 y Q4–Q7 son `ax2`, `ax3`, `ax4`, `ax5`, `ax8` y `ax9`.
2. **0+n = n y σm+n = σ(m+n).** Lo primero: 0+n = n+0 (`ax6`) = n (`ax4`). Lo segundo: σm+n = n+σm (`ax6`) = σ(n+m) (`ax5`) = σ(m+n) (`ax6` y Leibniz).
3. **Q ⊬ `ax6`, `ax7`, `ax10`–`ax12`.** Un solo modelo de Q, comprobado Q1–Q7, los falsa a la vez: ℕ∪{a,b}, con σa=a, σb=b.
   - Suma: n+a=b, n+b=a; a+n=a, b+n=b; a+a=b, a+b=a, b+a=b, b+b=a.
   - Producto: a·m=b y b·m=a (m≥1); m·a=a y m·b=b; 0·a=0·b=0; a·a=b, a·b=b, b·a=a, b·b=a.
   - Fallos: 0+a=b≠a=a+0; (a+0)+a=b≠a=a+(0+a); a·1=b≠a=1·a; (a·1)·1=a≠b=a·(1·1); a·(1+1)=b≠a=a·1+a·1.
4. **T_Prf ⊇ PA, salvo lo de H9.** `inductionFormula` (`Full/Induction.lean:236`) y `listInductionFormula` (`Hilbert.lean:132`) son esquemas de **axioma** para toda fórmula, y en De Bruijn tratan bien los parámetros. «No hay solidez respecto de todo modelo» es incluso cierto en sentido fuerte: los 142 son finitos, y si probaran toda la inducción, T sería reflexiva y demostraría su propia consistencia.
5. **La lista de §0.1 está completa y no le sobra nada**:
   - `√`, `/₂`, `%₂`, τ y `^` quedan determinados.
   - `Π_p` también, porque todo número es `pair p e` (Cantor es biyectivo), pese al comentario de `Axioms.lean:428`.
   - `tcFn` sólo tiene ecuaciones para 0 y σ, porque `ax_tc_cons` está retirado; queda total.
   - `##`, `∈`, `lenc`, `allIn`, `chainOk` y `runFn` son totales desde ADR‑113, aunque `runFn`, `substtsc` y `liftsc` heredan la libertad de `carc`/`substtc`/`liftc`.
   - `lineWF` queda determinado por los 21 bicondicionales y `ax_lineWF_inv`. Las cláusulas `lenc ≥ 2` neutralizan la basura de `nthc`.
   - `axiomsCodeT` está fijado.
   - Lo de `premsOf` «sólo sobre las líneas que cumplen `lineWF`» es cierto: la forma de cada ecuación de `premsOf` coincide con la `lenc` exigida, en los 21 tags.
6. **`MINIMAL-AXIOMS.md`.** «Fortalecimiento conservativo: FALSO» es correcto en cualquier fecha: `ax6` está desde, como tarde, el 2026‑05‑10, y el documento es del 2026‑06‑03. La cadena Q ⊊ I∆₀ ⊊ EA = I∆₀+exp ⊊ IΣ₁ ⊊ PA es correcta.
7. **Literatura**:
   - Q ⊬ Con_Q y la atribución a Pudlák 1985 son correctas: Visser 2026, Thm 3.3 (Q interpreta S¹₂ en un corte) y Thm 3.4 (si U interpreta Q + con(U), U es inconsistente).
   - Bezboruah–Shepherdson, «formalización natural», es correcto (función β, pruebas de Hilbert; de hecho cubre las subteorías de PA⁻).
   - S¹₂ basta para HBL1/HBL3 (Buss §2.1.2), y Buss numera de otro modo (HBL1 = distribución).
   - Gödel I sobre Q por Rosser es correcto (Buss §2.2.2).
   - «El ENUNCIADO de D1 no necesita la inducción» es correcto: es la Σ₁‑completitud externa.

### Fuentes
- [Kurahashi, A note on derivability conditions (arXiv 1902.00895)](https://arxiv.org/pdf/1902.00895)
- [Visser, On a Theorem by Bezboruah & Shepherdson (arXiv 2603.06068)](https://arxiv.org/abs/2603.06068)
- [Buss, Handbook of Proof Theory, cap. II (PDF)](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/handbookII/ChapterII.pdf)
- [Jeroslow 1973, resumen (Cambridge)](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/redundancies-in-the-hilbertbernays-derivability-conditions-for-godels-second-incompleteness-theorem1/23C526FB42C8D80D37336BAFD4045C13)
- [FOM, «Derivability conditions for Robinson arithmetic» (2010)](https://cs.nyu.edu/pipermail/fom/2010-September/015072.html) (no se pudo abrir: 404; citado por el buscador)
- [R. Zach, The Second Incompleteness Theorem for Weak Theories](https://richardzach.org/?p=2515)
