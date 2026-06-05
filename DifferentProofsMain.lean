import VersoManual
import VersoBlueprint.PreviewManifest
import DifferentProofs.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc DifferentProofs.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
