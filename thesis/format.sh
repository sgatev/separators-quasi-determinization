#!/bin/sh

cd "$(dirname "$0")" || exit 1

for file in *.tex; do
   latexindent -s -l -m $file -o $file
done
