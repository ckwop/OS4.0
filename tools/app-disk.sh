#!/bin/sh
# app-disk.sh IMAGE [DIR]: make an app disk: a FAT volume labelled OS4APP
# holding the files and directories in DIR (none without DIR), except hidden
# ones and the top-level build and tests directories. It is FAT32 (64 MiB,
# sparse) unless DIR holds a file named .fat16 (then FAT16 with 512-byte
# clusters, so files span many). The OS reads app.fs from it at boot and never
# writes it (DECISIONS.md #99).
set -e
img=$1
dir=$2
[ -n "$img" ] || { echo "usage: app-disk.sh IMAGE [DIR]" >&2; exit 2; }
rm -f "$img"
if [ -n "$dir" ] && [ -e "$dir/.fat16" ]; then
    mkfs.fat -C -F 16 -s 1 -n OS4APP "$img" 16384 >/dev/null
else
    mkfs.fat -C -F 32 -n OS4APP "$img" 65536 >/dev/null
fi
[ -n "$dir" ] || exit 0
for f in "$dir"/*; do
    case "${f##*/}" in
        build|tests|"*") ;;
        *) mcopy -s -Q -i "$img" "$f" ::/ ;;
    esac
done
