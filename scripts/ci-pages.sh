#!/usr/bin/env bash

set -euo pipefail

lake build DifferentProofsBlueprint.Blueprint

tmp_generator="$(mktemp "${TMPDIR:-/tmp}/different-proofs-blueprint-main.XXXXXX.lean")"
trap 'rm -f "$tmp_generator"' EXIT

cat > "$tmp_generator" <<'LEAN'
import VersoManual
import VersoBlueprint.PreviewManifest
import DifferentProofsBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc DifferentProofsBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
LEAN

lake env lean --run "$tmp_generator" --output _out/site

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-preview-manifest.json
