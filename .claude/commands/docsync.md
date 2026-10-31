---
description: Comprueba que la documentación cuadra con el código real (AI-GUIDE §27) y corrige lo que falle
---

**Last updated:** 2026-11-01 — revisado ENTERO en T21 (ADR‑235): cada afirmación, contra el código y `.github/workflows/build.yml`. Antes, 2026-09-11 (la marca que no tenía, puesta en T24, ADR‑233, con la fecha de su última revisión real).

Ejecuta el control de sincronía documentación ↔ código y **deja el repositorio en verde**.

## Qué hacer

1. Ejecuta `bash check-doc-sync.bash` con lake en el PATH (M‑6: desde PowerShell). Sin él dan rojo, por no poder
   medir, la VERDAD DEL CÓDIGO (los jobs) y [B], que vuelca el entorno de Lean con
   `lake env lean scripts/VolcarEntorno.lean`. Con --quick sólo se salta `lake build`: no mide los jobs ([A] y [A2]
   no los comparan, y --a2-deuda se niega, en rojo), y [B] sigue pidiendo lake y el build hecho. La CI lo corre
   sin --quick. *(✏️ 2026‑10‑31, T21, ADR‑235: decía «o --quick si no hace falta rebuild»; desde ADR‑166, [B]
   necesita lake.)*
2. **[A] cifras, [C] proyección, [D] marcas de tiempo** — son objetivos y rompen el check.
   **Corrígelos.** ⚠️ Al corregir una cifra, **no basta con el banner**: recorre también las
   tablas resumen, las secciones de «Próximos pasos» y las notas de auditoría antiguas. Ése es
   exactamente el fallo que este control existe para atrapar.
   Rompen también, y se corrigen igual: la VERDAD DEL CÓDIGO si no puede medir (los axiom, los sorry o, sin --quick,
   los jobs); [L], el cierre de imports del barril = el disco = git (ADR‑163); [EOL], ningún blob con CRLF en el
   índice (ADR‑200); [H], el PATH higiénico de los .bash versionados (ADR‑201); [I], las frases que un teorema vivo
   desmiente (⊬¬G, Rosser y Löb; ADR‑169); [N], las citas por número de línea (ADR‑209); [F], ningún .olean sin
   fuente; [H], el catálogo de sondeos/, en los dos sentidos (ADR‑084); [M], lo que nombra la columna «Verificación»
   de los MANDATORIES (ADR‑133); y [T], los titulares y sus filas en `TEOREMAS-E-HIPOTESIS.md` (ADR‑135).
3. **[B] citas muertas** — **rompe**: desde ADR‑084 (2026‑09‑22), con trinquete por símbolo; desde ADR‑166
   (2026‑10‑18), por cita, con la deuda en `doc/control/b-deuda.tsv` y, desde ADR‑167, techo en la base verificada.
   *(✏️ 2026‑10‑31, T21, ADR‑235: decía «desde ADR‑166 (2026‑10‑18) rompe».)* Por cada cita reportada, decide:
   * ¿el texto afirma que **ya está**? → corrígelo (apunta a lo vivo que lo sustituye).
   * ¿es una mención **histórica, planificada o descartada**? → pon un marcador de estado («retirado», «archivado»,
     «propuesto», «falta», «pendiente», «histórico»…) **a 100 bytes o menos de la cita, en su misma celda y en su
     misma oración**, sin otra cita en medio (entre dos, es de la más cercana; las unidas sólo por comas, «y» u «o»
     lo comparten). No marca negado («no está retirado»), como sustantivo («la propuesta», «por falta de») ni
     «hace falta». Un nombre que sólo declara un sondeo queda absuelto si la línea nombra ese sondeo («sondeos/X» o
     «X.lean»). ⛔ Una fecha NO es un marcador: no dice que lo citado esté retirado, y fechar una línea para que deje
     de reportarse es esquivar el control.
   * Si desaparece una cita muerta vieja, `bash check-doc-sync.bash --b-deuda` baja la tabla de la deuda; y si
     desaparece una cifra vieja del cuerpo, `bash check-doc-sync.bash --a2-deuda` (sin --quick) baja la de [A2].
4. Vuelve a ejecutar hasta que todo esté en verde.
5. Informa en el chat, distinguiendo **hallazgos reales** de ruido descartado.

## Contexto

Este control nace de dos fallos reales de 2026-08-22, documentados en `AI-GUIDE.md` §27 y en la
memoria `feedback-doc-audit-traps`:

* **Los documentos de estado se actualizan por su BANNER y no por su CUERPO.**
  `CURRENT-STATUS-PROJECT.md` tuvo banner correcto y, tres líneas más abajo, una tabla diciendo
  «113 jobs, 99 módulos» y citando un teorema borrado. Un ADR llevó **un mes** diciendo «no
  implementado» sobre algo hecho.
* **Al contar por familia de símbolos, hay que contar la familia entera.** El recuento de raíces
  de `cuarentena/` buscó sólo `prf_tc_cons` y perdió dos raíces que usan `prf_tc_nul`/`_un`/`_bin`.
  La cifra falsa (6 en vez de 8) circuló meses por cuatro documentos.

$ARGUMENTS

---

## 🆕 Bloques nuevos (2026‑09‑10h / 2026‑09‑11)

| | qué mira | ¿rompe? |
|---|---|---|
| **[A2]** | las mismas cifras que [A], en el **CUERPO** (de la línea 101 al final) de los autoritativos salvo `DECISIONS.md`; las viejas de hoy, contadas por (etiqueta, documento, cifra), en `doc/control/a2-deuda.tsv`, que sólo baja (`bash check-doc-sync.bash --a2-deuda`, sin --quick) y tiene techo en la base verificada | **rompe**, con trinquete por línea en los dos sentidos *(✏️ 2026‑10‑31, T21, ADR‑235: era aviso hasta ADR‑169, 2026‑10‑19)* |
| **[E]** | la **frescura del TITULAR**, por su sello, el primer «**Last updated:**» de cada .md versionado (salvo doc/book/) y de los autoritativos, contra la fecha del último commit que tocó el documento (la de hoy, si tiene cambios sin commitear). La deuda declarada en el script queda exenta mientras siga mal, cada documento por la razón de su tabla: E_DEUDA, la de contenido (marca vieja), y E_DEUDA_FORMATO, la de formato (sin marca; vacía desde el 2026‑10‑31); y las dos juntas no pueden tener un documento que no tengan las de la base verificada (el techo; T24, ADR‑233) | **rompe** (lo decide git), también si una deuda declarada ya está saldada y en un clon superficial *(✏️ 2026‑10‑31, T21, ADR‑235: era aviso, y contra la entrada más reciente de `CHANGELOG.md`, hasta ADR‑072, 2026‑09‑18)* |

⚠️ **[A2] y [E] rompen, y cada caso hay que LEERLO, no contarlo.** [A2] deja pasar la historia marcada
(«histórico», «previo», «entonces», «retirado»…, lo citado entre «…» y lo tachado), y una cifra vieja sin marcar o
está en su tabla de deuda o es rojo. [E] mira sólo la FECHA del sello: un banner puede estar **al día en sus cifras y
mintiendo en su frase** —así llegaron seis documentos autoritativos a llevar el mismo titular falso—, y si el sello se
sube sin releer la frase, ya no lo ve nadie, salvo [I] para las afirmaciones de su lista (hoy, ⊬¬G, Rosser y Löb). Al subir el sello,
relee lo que el titular afirma. *(✏️ 2026‑10‑31, T21, ADR‑235: decía «Los dos avisos»; [E] rompe desde ADR‑072,
2026‑09‑18, y [A2] desde ADR‑169, 2026‑10‑19.)*

⚠️ **Y [B] hay que ADJUDICARLO uno a uno** (rompe desde ADR‑084 y, por cita, desde ADR‑166: adjudicar es arreglar o
marcar), que es lo que M‑6 pide: al hacerlo por primera vez (2026‑09‑10h) salieron cuatro símbolos muertos leyéndose
como **frentes vivos**.

Detalle en `AI-GUIDE.md` §27.2 y §27.3.
