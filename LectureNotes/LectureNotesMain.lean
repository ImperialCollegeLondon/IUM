/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import LectureNotes

open Verso.Genre.Manual

-- def buildExercises (_ctxt : TraverseContext) (_state : TraverseState) : IO Unit :=
--   IO.println "Placeholder generator for output exercise and solution Lean code"

def myCSS : String :=
":root {
  --verso-code-keyword-color: #0000ff;
  --verso-code-const-color: #795E26;
  --verso-code-var-color: #991f99;
  --verso-code-color: #000000;
}

.hl.lean .inter-text {
  color: grey;
}

.hl.lean .token.typed {
  color: teal
}
"

def config : Config where
  emitTeX := false
  emitHtmlMulti := true
  emitHtmlSingle := true
  htmlDepth := 2
  -- TODO: once we're on a newer version of verso, this should use extraCss and not extraCssFiles
  extraCssFiles := #[("highlighting.css", myCSS)]

def main := manualMain (%doc LectureNotes) (config := config.addKaTeX)
