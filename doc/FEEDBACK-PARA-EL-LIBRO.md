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

⛔ **YA ESTÁ ROTO, y lo hemos comprobado**: `python3 scripts/simbolos.py --estricto` falla hoy con

    ✗ \ident{goedel_second'} no nombra nada declarado en el repo
      (cap-condiciones-derivabilidad.tex, cap-representabilidad-d1.tex)

Eso es **el control funcionando**, no un accidente. **Dos arreglos posibles**, los dos del libro:

1. **el bueno** — reescribir esos dos puntos con `goedel_second_prf` (ver §3bis: el resultado es
   **más fuerte** de lo que el libro cuenta hoy);
2. **el de urgencia** — declarar `goedel_second'` y `con_imp_godel'` en
   `simbolos-exentos.json` con razón **`retirado`**, que es justo para lo que existe ese fichero.

⚠️ **No lo hemos tocado nosotros**: `doc/book/**` es vuestro (PLAN‑LIBRO §0), y por eso este
documento vive ahora en **`doc/`** y no dentro de `doc/book/`.

📌 **Y en CI**: los controles del libro se ejecutan en el job `libro`, que **sólo se dispara cuando
el push toca `doc/book/`**. Razón: el libro y el código son **dos tareas con commits separados**, y
los controles de cada una corren sobre sus propios commits. ⇒ **vuestro próximo push ejecutará
`simbolos.py` y fallará hasta que apliquéis (1) o (2).**

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

## 3bis · 🏁🏁 **ADDENDUM del mismo día — y cambia el §3 entero para mejor**

Lo de arriba deca que `ConsistentOmega` había que contarlo con cuidado. **Ya no hace falta**: se
midió (**P‑4**) que basta la hipótesis **mínima**, y los enunciados cabecera cambiaron:

```lean
goedel_first_prf  (hcon : ConsistentH) : ¬ Prf godelCN
goedel_second_prf (hcon : ConsistentH) : ¬ Prf consistencyFormula'
```

con `ConsistentH := ¬ Prf ⊥` — *el cálculo finitario no demuestra `⊥`*, que es **exactamente** la
hipótesis que el libro quiere poder escribir: **consistencia simple, y del cálculo del que se habla**.

⭐⭐ **Y el footprint, que es el dato bonito para imprimir**: cae de

    [3 de Lean] + dne + gen + imp_intro + ax_induction_prim + ax_list_induction
                + ax_axiomsCodeT_eq + prf_axiomsCodeT_eq

a

    [propext, Classical.choice, Quot.sound, prf_axiomsCodeT_eq]

**Un solo axioma del proyecto.** Las ω‑reglas y los dos esquemas de inducción entraban **por la
hipótesis vieja**, que hablaba de `⊢`.

🔑 **Material de libro, y de los buenos**: *una hipótesis mal elegida no sólo debilita el enunciado
— arrastra al footprint todo lo que ella necesita.* Cambiarla por la mínima limpió **seis**
dependencias de golpe. Y el resultado que el libro puede anunciar es mucho más fuerte de lo que
ayer parecía:

> **La cadena de Gödel de este proyecto es ENTERAMENTE FINITARIA**: Gödel I y Gödel II sobre `Prf`,
> desde la consistencia simple del propio `Prf`, con D1/D2/D3 demostradas y **un único axioma** —el
> ancla de codificación— entre el resultado y los tres axiomas de Lean.

⚠️ ⇒ El `muro` que §3 pedía para el cap. 13 **sigue teniendo sentido**, pero cambia de asunto:
ya no es «cuidado, la hipótesis es más fuerte de lo que parece» sino **«hay TRES nombres parecidos
—`ConsistentH`, `ConsistentOmega`, `OmegaConsistent`— y el que se usa es el más débil de los
tres»**, que es la buena noticia.

---

## 4 · Las cifras, para los banners del libro

| | |
|---|---|
| build | **145 jobs** |
| módulos activos | **130** (Minimal 11 + Meta 109 + Full 11) |
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

---

## 📌 2026‑09‑12 — cuatro cosas del libro que el desarrollo ha dejado obsoletas

> Este bloque lo escribe la **tarea de desarrollo**. `doc/book/**` es de la **tarea del LIBRO**
> (PLAN‑LIBRO §0), así que **no se ha tocado ni un `.tex`**. Aquí van los avisos.

### 1 · ⛔ `cap-representabilidad-d1.tex:70` cita `AXIOMS.md` **POR NÚMERO DE FILA**

Dice literalmente: *«en el inventario de `AXIOMS.md` como los **axiomas 5 y 6**, uno por cálculo»*.

⚠️ **Eso es un acoplamiento que ningún control detecta**, y se ha roto **dos veces el mismo día**:
se retiró `ax_p_tfa` (que era el 4) y el ancla `Prf` dejó de ser `axiom` (era el 6).

✅ **Ya arreglado del lado del desarrollo**: `AXIOMS.md` **ha retirado la columna `#`**. Ahora los
axiomas se citan **por nombre**. ⇒ El texto del libro debe decir algo como *«las dos anclas de
codificación, una por cálculo»*, sin números.

### 2 · El censo de axiomas ha cambiado dos veces: **5 → 4 → 3**

| | |
|---|---|
| `prf_axiomsCodeT_eq` | **ya no es `axiom`** — es la clase `AnclaEq` ([ADR‑026](../DECISIONS.md)) |
| `ax_p_tfa` | **retirado** (medido huérfano) |

Quedan **tres**: `ax_induction_prim`, `ax_list_induction`, `ax_axiomsCodeT_eq`.

### 3 · ⛔⛔ Y el matiz SIN EL CUAL la cifra es un sobreclaim

`goedel_first_prf` y `goedel_second_prf` dan hoy footprint **`[propext, Classical.choice,
Quot.sound]` — cero axiomas del proyecto**. **No escribir eso a secas.** Su tipo es

    ∀ [AnclaEq], ConsistentH → ¬ Prf godelCN

⇒ **el postulado no desapareció: se movió del footprint a la FIRMA**, y **no hay ninguna
`instance : AnclaEq` en el árbol**. Decirlo sin esta frase sería **M‑8 con otro nombre**.

### 4 · `AXIOMS.md` publicaba una afirmación **medible‑mente falsa** sobre `ax_p_tfa`

Decía *«teorema en `Full`, postulado en `Minimal`»*. **No existe en `Full/` ningún teorema con ese
enunciado**: `tfa_numeral` tiene otro dominio (`Nat` vs `Term`), otra unicidad (`Perm` vs igualdad
objeto) y otra hipótesis (meta vs objeto). Si el libro repitió esa frase, hay que corregirla.
