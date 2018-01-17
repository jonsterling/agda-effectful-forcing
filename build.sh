#!/bin/bash
agda --latex src/Spread/Core.lagda
latexmk -pdf paper
