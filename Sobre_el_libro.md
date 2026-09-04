---
marp: true
---

# Sobre el libro

> ## ⚠️ NOTA HISTÓRICA — 2026-09-03
>
> Este documento **ya no es normativo**. Su contenido (la progresión pedagógica: arrancar por FOL,
> lenguaje natural, teoría objeto vs metateoría, gramática y reglas de inferencia explícitas antes
> de la autorreferencia) se ha **fusionado** en **[PLAN-LIBRO.md](PLAN-LIBRO.md)**, que es el plan
> único del libro. Si este fichero diverge de aquél, **manda `PLAN-LIBRO.md`**.
>
> Se conserva porque es el enunciado original de la intención del libro, en primera persona, y como
> tal es material citable para el propio libro.


Para comenzar, quiero que este libro sea más una guía personal que un manual técnico.

La primera parte será sobre de dónde partimos. Sobre lo dado en el proyecto FOL. Quiero que introduzca de forma fluida los distintos conceptos que se han desarrollado en el proyecto FOL, y será la base sobre la que trabajar. Necesitamos tener en forma matemática y formal esos conceptos introducidos y al menos las firmas de los teoremas y axiomas desarrollados en el proyecto FOL.

El siguiente punto debería ser totalmente en lenguaje natural: tiene que describir de forma clara el objetivo del presente proyecto, por partes:

- El desarrollo de una aritmética mínima, pero suficiente para poder autoreferenciarse y poder expresar propiedades de los números naturales.
- El desarrollo de la teoría aritmética de Peano, por lo menos en cuanto a axiomas admitidos y primeros teoremas que se necesiten en el presente proyecto.
- Introducimos los conceptos correspondientes a listas y secuencias que se han desarrollado en este proyecto (no sé si en FOL se habrá desarrollado algo), y que son necesarios para poder expresar propiedades de los números naturales y de la aritmética de Peano.
- Algo importante: tenemos que introducir la distinción entre la teoría objeto y la teoría meta, y explicar cómo se relacionan entre sí. Esto es crucial para poder hablar de autoreferencia y de propiedades de los números naturales dentro del marco de la teoría aritmética.
- Debemos dejar muy clara cuáles es la gramática y reglas de inferencia usadas en el lenguaje objeto (FOL) y cuáles para en el lenguaje meta (la teoría aritmética de Peano). Esto es importante para poder hablar de propiedades de los números naturales y de la aritmética de Peano dentro del marco de la teoría aritmética.
- Ahora podemos introducir la idea de autoreferencia, podemos exponer la paradoja del mentiroso con la que Gödel construye su teorema de incompletitud, y explicar cómo se puede construir una fórmula que se refiera a sí misma dentro del marco de la teoría aritmética.
- Explicamos el objetivo de Gödel: exponemos el problema correspondiente de la lista de David Hilbert, y explicamos primero cual será la respuesta de Gödel a ese problema. Nos limitaremos por lo pronto a Gödel I.
- Explicamos el teorema de incompletitud de Gödel I, y cómo se construye la fórmula que se refiere a sí misma. Explicamos cómo se construye la fórmula que se refiere a sí misma, y cómo se demuestra que no puede ser probada ni refutada dentro del marco de la teoría aritmética.
- Pasamos a exponer de forma matemática y formal todo lo dicho, y posteriormente, pasamos a ver su reflejo en el lenguaje que usamos: Lean 4.
- Damos una breve pasada sobre el teorema de incompletitud de Gödel II, y explicamos cómo se construye la fórmula que se refiere a sí misma, y cómo se demuestra que no puede ser probada ni refutada dentro del marco de la teoría aritmética.
- Damos una idea de las distintas fases de la demostración del teorema en el actual proyecto. Este libro siempre se referirá al material de este proyecto y al material del proyectoi FOL, y no a otros materiales. Por lo tanto, es importante que se haga una referencia clara a los distintos materiales que se han desarrollado en este proyecto y en el proyecto FOL, y cómo se relacionan entre sí.

El libro se desarrollará de forma activa en paralelo con el propio proyecto, de forma que será una forma en yo pueda seguir el desarrollo del mismo, y pueda ayudar a colaborar en el mismo. 
