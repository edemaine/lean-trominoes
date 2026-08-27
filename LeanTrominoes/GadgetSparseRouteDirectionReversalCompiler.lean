/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteReverseBlockTransducer
import LeanTrominoes.GadgetSparseRouteDirectionReversal
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time reversal of cardinal direction words -/

noncomputable section

namespace LeanTrominoes
namespace Gadget

open Computability Turing

/-- Reversal emits the opposite of each direction while traversing the word
backward. -/
def reverseDirectionBlock (direction : AxisDirection) :
    List AxisDirection :=
  [direction.opposite]

@[simp] theorem reverseFlatMap_reverseDirectionBlock
    (directions : List AxisDirection) :
    (directions.flatMap reverseDirectionBlock).reverse =
      reverseDirections directions := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      simp [reverseDirectionBlock, reverseDirections,
        List.reverse_cons, List.map_append, induction]

/-- Dynamic direction-word reversal is computable in exact linear time. -/
noncomputable def reverseDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id reverseDirections :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (FiniteReverseBlockTransducer.computableInPolyTime
      reverseDirectionBlock)
    reverseFlatMap_reverseDirectionBlock

end Gadget
end LeanTrominoes

end
