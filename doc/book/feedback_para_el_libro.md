# Feedback para la tarea del LIBRO — 2026‑09‑11

> **De**: la tarea de programación y prueba. **Para**: la tarea del libro.
> **Por qué existe**: `PLAN-LIBRO.md` §0 pone los `.lean` en sólo lectura para el libro, y los
> `doc/book/**` en sólo lectura para el desarrollo. Este fichero es la **única vía** por la que el
> desarrollo puede decirle al libro *«esto que imprimiste ya no es cierto»*.
> **Simétrico de** `doc/book/AUDITORIA-2026-09-10.md`, que hizo el camino contrario y encontró la
> causa raíz de la deriva documental del proyecto.

---

## 0 · Resumen en una frase

**El capítulo 17 y la tabla de resultados del capítulo 11 se han quedado falsos, y los capítulos
13–15 necesitan un párrafo nuevo cada uno** — porque el 2026‑09‑11 se midió la fuerza del cálculo
`axioms ⊢` y resultó ser **sintácticamente completo**, lo que obligó a **retirar** el `goedel_second'`
que el libro presenta y a **construir** el Segundo Teorema sobre `Prf`.

⚠️ **Y la buena noticia es más grande que la mala**: el proyecto **tiene hoy los dos teoremas de
Gödel** —el segundo, **ensamblado y sin hipótesis sueltas**—, y el episodio que lo produjo es el
mejor material de la Parte V que ha aparecido hasta ahora.

---

## 1 · ⛔ Lo que quedó FALSO y hay que corregir

### 1.1 · `goedel_second'` **ya no existe** (y no por deuda técnica)

Estaba en `Meta/GodelTwo.lean`; se **retiró** el 2026‑09‑11 ([ADR‑024](../../DECISIONS.md)), junto
con `con_imp_godel'`.

**Por qué**, y esto es lo que hay que contar: su hipótesis era `hgi : ¬ (axioms ⊢ G)`, sobre el
cálculo `⊢`. Y se midió que

```lean
theorem derives_completo (A) : (axioms ⊢ A) ∨ (axioms ⊢ neg A)   -- sin hipótesis
```

⇒ **`axioms ⊢` es sintácticamente COMPLETO**: decide toda sentencia. Luego `¬(axioms ⊢ G)` **no
significa** «`G` es indemostrable»: significa **«el cálculo REFUTA `G`»**. El teorema era una
implicación correcta y **no era incompletitud**.

### 1.2 · Qué ponerle en su lugar

```lean
goedel_second_prf (hcon : ConsistentOmega) : ¬ Prf consistencyFormula'
```

`Meta/GodelTwoPrf.lean`. **Una sola hipótesis —la misma que Gödel I— y ninguna suelta**: el punto
fijo y la necesitación se descargan dentro. ⭐ `prf_godelCN_fixedpoint` es **net‑0 PURO**: el punto
fijo sobre `Prf` no usa **ningún** axioma del proyecto.

### 1.3 · Dónde toca, en concreto

| dónde | qué dice hoy | qué pasa |
|---|---|---|
| **cap. 17** | reorientado el 2026‑09‑10 a *«qué hipótesis le quedan a `goedel_second'`»* | ⛔ **el teorema ya no existe**. El capítulo cambia de sujeto |
| **cap. 11**, tabla de resultados | «Gödel II, más el `d3` pendiente» → ya corregido a «con las tres condiciones demostradas» | 🔶 ahora además **está ensamblado**, y sobre `Prf` |
| **cap. 15** (condiciones de derivabilidad) | D1/D2/D3 demostradas | ✅ sigue siendo cierto, y ahora se puede añadir que **las tres existen sobre `Prf`**, que es lo que permitió el ensamblaje |
| **cap. 13** (Gödel I) | la hipótesis es `ConsistentOmega` | ⚠️ ver §3: **no es «consistencia simple»** |
| **`PLAN-LIBRO.md`**, base sancionada | 5 `axiom` | ✅ correcto |

⚠️ **Comprobad con `simbolos.py --estricto`**: cualquier `\ident{goedel_second'}` o
`\ident{con_imp_godel'}` que quede **romperá el control**, porque los símbolos ya no existen. Eso es
el control funcionando.

---

## 2 · ⭐⭐ El material nuevo, y es el mejor de la Parte V

### 2.1 · «Un cálculo que decide todo no puede ser el sujeto de un teorema de incompletitud»

La pregunta que lo abre es la que hizo el propietario al ver el teorema:

> *¿No es `(⊢ A) ∨ (⊢ ¬A)` la definición de completitud, y precisamente lo que Gödel I dice que no
> ocurre?*

**Sí.** Y la respuesta es lo que hace el episodio publicable:

```
Gödel I  =  consistente  +  suficientemente fuerte  +  r.e.  ⟹  INCOMPLETA
medido   =  `axioms ⊢` es COMPLETA
⇒           `axioms ⊢` NO es r.e.
```

Y **se ve dónde** deja de serlo: `raa` e `imp_intro` toman como premisa una **función de Lean**, es
decir cuantifican sobre **todas las demostraciones de la metateoría**. No hay procedimiento que
enumere eso. `{A | axioms ⊢ A}` es una **compleción tipo Lindenbaum**, no un sistema formal.

🔑 **La moraleja, que es exactamente de libro**: *la hipótesis «efectivamente axiomatizada» de Gödel
I no es una tecnicidad que se pueda saltar en la formalización — es lo que hace que el teorema
tenga contenido.* Un formalizador puede construir sin darse cuenta un cálculo cómodo que la
incumple, y entonces sus «teoremas de incompletitud» hablan de otra cosa.

### 2.2 · La exclusividad **es** la consistencia, y la prueba es clásica

Segunda observación del propietario, también exacta: el `∨` es **inclusivo**, y la completitud que
uno quiere decir es «exactamente una». Esa mitad que falta —`¬(L ∧ R)`— **no es otra propiedad: es
la consistencia**, porque de `⊢ A` y `⊢ ¬A` sale `⊢ ⊥` por un `mp`. Está demostrado
(`derives_decide_exactamente_una`).

⚠️ **Y hay un matiz que merece recuadro propio**: `derives_completo` se demuestra con **excluido
medio en la metateoría**. Es un **metateorema clásico**; intuicionísticamente no saldría. Conviene
separar los dos planos, porque en este proyecto se tocan:

| plano | ¿clásico? | por qué |
|---|---|---|
| lógica **objeto** (`Derives`) | sí | el meta‑axioma `dne`, explícitamente |
| **metateoría** (Lean) | sí, y aquí se usa | `by_cases` sobre `axioms ⊢ A` |

⇒ *la completitud medida es un hecho clásico sobre un cálculo clásico.* Lo que **sí** sale sin EM es
`refuta_lo_que_no_prueba` — y basta para la conclusión de que `⊢` no es r.e.

### 2.3 · `gen` no era la ω‑regla, y el docstring lo decía mal

`FOL/MetaRules.lean` llamaba «ω‑regla» a `gen`. **No lo es**: la ω‑regla toma `A[n̄]` para cada
**numeral**; `gen` lo toma para **todo `Term`** —variables libres incluidas—, luego su premisa es
**estrictamente mayor** y como **regla** es **más débil**. Corregido en `FOL` el 2026‑09‑11.

⭐ Es un buen ejemplo corto de §2.6 —*un docstring es testimonio, nunca evidencia*— aplicado a la
**librería base**, no al proyecto.

---

## 3 · ⚠️ Y una cosa que el libro debe decir con cuidado: qué es `ConsistentOmega`

`ConsistentOmega := ¬ (axioms ⊢ ⊥)`. Es la hipótesis de **los dos** teoremas de Gödel del proyecto.

Con la medición de §2.1 **ya no se puede presentar como «consistencia simple» a secas**: como
`axioms ⊢` es completo, dice que una **compleción completa** de `axioms` es consistente — en fuerza,
cercano a suponer **solidez**.

| | |
|---|---|
| ✅ **lo que NO invalida** | las conclusiones son sobre **`Prf`**, que sí es r.e. y no completo. **Los teoremas dicen lo que parecen decir** |
| ⚠️ **lo que hay que escribir** | que la hipótesis es **más fuerte** que «Q++ es consistente» |
| ⬜ **abierto** | si bastaría `ConsistentH := ¬ Prf ⊥`, que sería **estrictamente mejor**. Hay `ConsistentOmega → ConsistentH`; **la vuelta no existe**. Es **P‑4** de `PLAN-PRUEBAS.md` |

📌 **Sugerencia editorial**: esto pide un `muro` en el capítulo 13, al lado del que ya distingue
`ConsistentOmega` de `OmegaConsistent` (M‑5 de `MATERIALES.md`). Son **tres** nombres parecidos con
tres contenidos distintos, y ahora uno de ellos ha cambiado de significado.

---

## 4 · Las cifras, para los banners del libro

| | |
|---|---|
| build | **144 jobs** |
| módulos activos | **130** (Minimal 11 + Meta 108 + Full 11) |
| `axiom` de Lean | **5** — `ax_induction_prim`, `ax_list_induction`, `ax_p_tfa`, `ax_axiomsCodeT_eq`, `prf_axiomsCodeT_eq`. **Ninguno gödeliano** |
| axiomas objeto | **141** = 34 `coreAxioms` + 107 `codingAxioms`; y los 34 = **24 primitivos + 10 derivables** |
| `sorry` | **0** |

---

## 5 · Documentos nuevos que el libro puede citar

| | |
|---|---|
| `doc/AUDITORIA-2026-09-11.md` | la auditoría de dos ciclos: diez hallazgos, y §4 —**lo que ningún control garantiza**— que es material directo de la Parte V |
| `PLAN-PRUEBAS.md` | qué garantiza cada control y **qué no** |
| `TEOREMAS-E-HIPOTESIS.md` | teorema → hipótesis → **quién la descarga**. La defensa contra que vuelva a pasar lo del cap. 17 |
| `DECISIONS.md` ADR‑022/023/024 | la clase de testigos, el censo de axiomas, y `⊢` vs `Prf` |
| `Meta/OmegaStrength.lean` | **la medición**, con la respuesta a la pregunta de §2.1 escrita en su docstring |

---

**Para responder**: anotad en `doc/book/MATERIALES.md` qué se consume y qué se descarta, como con
las demás entradas. Si algo de aquí resulta **falso al comprobarlo contra el árbol**, decidlo — el
canal va en las dos direcciones, y la auditoría del 2026‑09‑10 demostró que el libro acierta.
