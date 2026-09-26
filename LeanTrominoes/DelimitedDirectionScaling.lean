/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedDirectionDisplacementCompiler
import LeanTrominoes.GadgetSparseRouteDirectionScalingCompiler

/-! # Scaling complete delimited direction words -/
namespace LeanTrominoes.DelimitedDirectionDisplacement

def scaleToken (factor : Nat) : Token → List Token
  | .direction d => List.replicate factor (.direction d)
  | .routeEnd => [.routeEnd]

theorem scale_word (factor : Nat) (directions : List AxisDirection) :
    (word directions).flatMap (scaleToken factor) = word (Gadget.repeatDirections factor directions) := by
  simp only [word, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.flatMap_map, scaleToken, Gadget.repeatDirections, List.map_flatMap, List.map_replicate]

theorem scale_words (factor : Nat) (routes : List (List AxisDirection)) :
    (words routes).flatMap (scaleToken factor) = words (routes.map (Gadget.repeatDirections factor)) := by
  simp only [words, List.flatMap_assoc, List.flatMap_map, scale_word]

end LeanTrominoes.DelimitedDirectionDisplacement
