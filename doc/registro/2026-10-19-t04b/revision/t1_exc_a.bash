#!/bin/bash
# t1: ¿qué líneas con una cifra VIEJA exime EXC_A? (copiado literal de check-doc-sync.bash, T04b)
EXC_A='hist(o|ó)rico|previo|antes|era |fueron|→|->|en su momento|entonces|ya no|~|p\. ej|ejemplo|umbral|(^|[^0-9-])[0-9]{1,3}-[0-9]{1,3}([^0-9-]|$)|«[^»]*[0-9]'
NB='(\*\*)?'
pat="[0-9]+$NB jobs"
F=$(mktemp)
cat > "$F" <<'L'
D:1:El build tiene 99 jobs y las constantes del entorno se vuelcan.
D:2:El build tiene 99 jobs, de manera reproducible.
D:3:La primera cifra: 99 jobs.
D:4:El build tiene 99 jobs (ver «ADR-121»).
D:5:| Build | 99 jobs | T04 → T05 |
D:6:El build tiene 99 jobs; los importantes, todos.
D:7:El build tiene 99 jobs y `A -> B` compila.
D:8:El build tiene 99 jobs (§27, «M‑13»).
D:9:El build tiene 99 jobs (cuadra «ADR·121»).
D:10:El build tiene 99 jobs ~~viejo~~ nuevo.
D:11:El build tiene 99 jobs, como dice «la tabla 3».
D:12:El build tiene 99 jobs (líneas 22-38 de AI-GUIDE).
D:13:El build tiene 99 jobs, cualquiera lo comprueba.
D:14:El build tiene 99 jobs; véase el ejemplo.
D:15:El build tiene 99 jobs. ES HISTÓRICO.
D:16:El build tiene 99 jobs.
D:17:El build tiene 99 jobs (lo «nuevo»).
D:18:El build tiene 99 jobs, «¬G 3».
L
for loc in C es_ES.UTF-8; do
  echo "== LC_ALL=$loc: líneas con «99 jobs» que SÍ ve el control (las demás quedan eximidas)"
  LC_ALL=$loc grep -nE "$pat" "$F" | LC_ALL=$loc grep -viE "$EXC_A" | cut -d: -f3 | tr '\n' ' '; echo
done
rm -f "$F"
