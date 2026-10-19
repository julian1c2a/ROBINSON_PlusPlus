#!/bin/bash
# t4: ¿qué fracción de las líneas de los documentos autoritativos queda eximida por EXC_A (y por cada alternativa)?
cd "$(dirname "$0")/$1" || exit 2
export LC_ALL=${LOC:-es_ES.UTF-8}
EXC_A='hist(o|ó)rico|previo|antes|era |fueron|→|->|en su momento|entonces|ya no|~|p\. ej|ejemplo|umbral|(^|[^0-9-])[0-9]{1,3}-[0-9]{1,3}([^0-9-]|$)|«[^»]*[0-9]'
T=$(mktemp); for d in $(cat ../docs.list); do grep -v '^[[:space:]]*$' "$d"; done > "$T"
tot=$(wc -l < "$T"); ex=$(grep -ciE -e "$EXC_A" "$T")
echo "líneas no vacías: $tot; eximidas por EXC_A: $ex ($((100*ex/tot)) %)"
for a in 'hist(o|ó)rico' 'previo' 'antes' 'era ' 'fueron' '→' '->' 'en su momento' 'entonces' 'ya no' '~' 'p\. ej' 'ejemplo' 'umbral' '(^|[^0-9-])[0-9]{1,3}-[0-9]{1,3}([^0-9-]|$)' '«[^»]*[0-9]'; do
  printf '  %-60s %5d\n' "$a" "$(grep -ciE -e "$a" "$T")"
done
echo "  «antes» DENTRO de otra palabra (constantes, importantes…): $(grep -ioE -e '[[:alpha:]]+antes' "$T" | wc -l)   ejemplos: $(grep -ioE -e '[[:alpha:]]+antes' "$T" | sort | uniq -c | sort -rn | head -6 | awk '{printf "%s(%s) ", $2, $1}')"
echo "  «era » DENTRO de otra palabra (fuera, primera, manera…): $(grep -ioE -e '[[:alpha:]]+era ' "$T" | wc -l)   ejemplos: $(grep -ioE -e '[[:alpha:]]+era ' "$T" | sort | uniq -c | sort -rn | head -6 | awk '{printf "%s(%s) ", $2, $1}')"
rm -f "$T"
