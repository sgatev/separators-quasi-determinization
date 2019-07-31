#!/bin/sh

for file in *.tex; do
   latexindent -s -l -m $file -o $file
done
