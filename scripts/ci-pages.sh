#!/usr/bin/env bash

set -euo pipefail

lake build DifferentProofs.Blueprint
lake env lean --run DifferentProofsBlueprintMain.lean --output _out/site

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-preview-manifest.json
