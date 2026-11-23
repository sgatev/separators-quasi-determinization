#!/bin/sh

cd "$(dirname "$0")" || exit 1

latexmk -latexoption="-shell-escape" -halt-on-error -xelatex main.tex
open -a Preview.app main.pdf
