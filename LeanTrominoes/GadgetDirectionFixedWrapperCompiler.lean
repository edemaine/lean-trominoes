/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.GadgetDirectionFixedWrapper

/-! # Polynomial-time fixed direction-word wrappers -/

noncomputable section

namespace LeanTrominoes
namespace Gadget
namespace DirectionFixedWrapper

open Computability Turing

local instance : Inhabited AxisDirection := ⟨.invalid⟩

/-- For any two fixed words, wrapping a direction stream is linear time. -/
noncomputable def computableInPolyTime
    (leading trailing : List AxisDirection) :
    TM2ComputableInPolyTime id id (output leading trailing) := by
  change TM2ComputableInPolyTime id id
    (FiniteStateTransducer.output .start (transition leading)
      (finish leading trailing))
  exact FiniteStateTransducer.computableInPolyTime
    .start (transition leading) (finish leading trailing)

end DirectionFixedWrapper
end Gadget
end LeanTrominoes

end
