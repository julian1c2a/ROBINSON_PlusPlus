#!/bin/bash
# guarda_y_bloquea.bash
# Secuencia para guardar y bloquear un archivo .lean

if [ -z "$1" ]; then
    echo "Uso: bash guarda_y_bloquea.bash <archivo.lean> [mensaje de commit]"
    exit 1
fi

FILE="$1"
MSG="${2:-"Actualización de $FILE"}"

echo "Desbloqueando la lista..."
bash git-lock.bash unlock

echo "Desbloqueando $FILE..."
bash git-lock.bash unlock "$FILE"

echo "Añadiendo a git..."
git add .

echo "Haciendo commit..."
git commit -m "$MSG"

echo "Haciendo push..."
# ⛔ 2026-10-14 (ADR-136): en ROBINSON_PlusPlus `master` está protegido y sólo admite un commit con la CI ya
# verde: este push directo a `master` lo rechaza GitHub. El flujo es el de AI-GUIDE, `guarda_y_sube` (rama `ci/…`).
# Adaptar esta herramienta de la plantilla es T52 de doc/AUDITORIA-SUELO-2026-10-12.md.
git push

echo "Bloqueando $FILE..."
bash git-lock.bash lock "$FILE"

echo "Bloqueando la lista..."
bash git-lock.bash lock

echo "Completado."
