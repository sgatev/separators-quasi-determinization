#!/bin/sh

latexmk -latexoption="-shell-escape" -halt-on-error -xelatex main.tex
open -a Preview.app main.pdf
