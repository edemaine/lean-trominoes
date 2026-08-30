/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoundedDelimitedDirectionCancellationData
import LeanTrominoes.FiniteStateTransducerTime

/-! # Compiler for bounded cancellation in delimited direction words -/

noncomputable section

namespace LeanTrominoes
namespace BoundedDelimitedDirectionCancellation

open Computability Turing

noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  exact FiniteStateTransducer.computableInPolyTime
    .empty transition finish

end BoundedDelimitedDirectionCancellation
end LeanTrominoes

end
