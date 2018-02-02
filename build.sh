#!/bin/bash
agda --latex src/Spread/Core.lagda
agda --latex src/Spread/Baire.lagda
latexmk -pdf paper
