/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceMaskData

/-! # Compiling constant masks over copied-clause occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

/-- Expand every finite clause descriptor to one constant Boolean per
represented occurrence. -/
opaque descriptorOccurrenceMaskComputableInPolyTime
    (active : Bool) :
    TM2ComputableInPolyTime id id (descriptorOccurrenceMask active) :=
  FiniteBlockTransducer.computableInPolyTime
    (descriptorOccurrenceMaskBlock active)

end LeanTrominoes.PeriodicCNFStripReduction

end
