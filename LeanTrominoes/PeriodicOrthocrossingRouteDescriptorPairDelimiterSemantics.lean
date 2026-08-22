/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairDelimiterBodySemantics
import LeanTrominoes.TM2EndDelimitedBlockMapData

/-! # Final delimiters of canonical route-descriptor pairs -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairFieldTags

open TM2EndDelimitedBlockMap

theorem blocksAux_append_pairEnd
    (reverseBlock body rest : List Token)
    (continues : ∀ token ∈ body, isPairEnd token = false) :
    blocksAux isPairEnd reverseBlock (body ++ .pairEnd :: rest) =
      (reverseBlock.reverse ++ body ++ [.pairEnd]) ::
        blocksAux isPairEnd [] rest := by
  induction body generalizing reverseBlock with
  | nil =>
      simp [blocksAux, isPairEnd]
  | cons token body induction =>
      have tokenContinues : isPairEnd token = false :=
        continues token (by simp)
      have bodyContinues : ∀ other ∈ body,
          isPairEnd other = false := by
        intro other member
        exact continues other (by simp [member])
      rw [List.cons_append, blocksAux]
      simp only [tokenContinues, Bool.false_eq_true, ↓reduceIte]
      rw [induction (token :: reverseBlock) bodyContinues]
      simp [List.reverse_cons, List.append_assoc]

end RouteDescriptorPairFieldTags
end PeriodicOrthocrossing
end LeanTrominoes
