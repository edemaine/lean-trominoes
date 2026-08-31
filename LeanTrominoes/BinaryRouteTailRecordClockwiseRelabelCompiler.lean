/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordClockwiseRelabelData
import LeanTrominoes.FiniteStateTransducerTime

/-! # Compiler for clockwise binary route-tail relabeling -/

noncomputable section

namespace LeanTrominoes
namespace BinaryRouteTailRecordClockwiseRelabel

open Computability Turing

/-- Clockwise source-slot relabeling is a fixed finite-state linear-time
compiler. -/
noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime initial transition finish

end BinaryRouteTailRecordClockwiseRelabel
end LeanTrominoes

end
