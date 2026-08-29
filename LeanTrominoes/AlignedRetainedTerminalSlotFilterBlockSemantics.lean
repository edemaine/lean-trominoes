/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedRetainedTerminalSlotFilterSemantics

/-! # Four-block semantics of aligned retained-terminal slot filtering -/

namespace LeanTrominoes.AlignedRetainedTerminalSlotFilter

theorem selected_four_blocks_carrier
    (crossover carrier bend routed : List Slot) :
    selected
        (List.replicate crossover.length false ++
          (List.replicate carrier.length true ++
            (List.replicate bend.length false ++
              List.replicate routed.length false)))
        (crossover ++ (carrier ++ (bend ++ routed))) =
      carrier := by
  rw [selected_append
    (List.replicate crossover.length false)
    (List.replicate carrier.length true ++
      (List.replicate bend.length false ++
        List.replicate routed.length false))
    crossover (carrier ++ (bend ++ routed)) (by simp)]
  rw [selected_append
    (List.replicate carrier.length true)
    (List.replicate bend.length false ++
      List.replicate routed.length false)
    carrier (bend ++ routed) (by simp)]
  rw [selected_append
    (List.replicate bend.length false)
    (List.replicate routed.length false)
    bend routed (by simp)]
  simp

theorem selected_four_blocks_bend
    (crossover carrier bend routed : List Slot) :
    selected
        (List.replicate crossover.length false ++
          (List.replicate carrier.length false ++
            (List.replicate bend.length true ++
              List.replicate routed.length false)))
        (crossover ++ (carrier ++ (bend ++ routed))) =
      bend := by
  rw [selected_append
    (List.replicate crossover.length false)
    (List.replicate carrier.length false ++
      (List.replicate bend.length true ++
        List.replicate routed.length false))
    crossover (carrier ++ (bend ++ routed)) (by simp)]
  rw [selected_append
    (List.replicate carrier.length false)
    (List.replicate bend.length true ++
      List.replicate routed.length false)
    carrier (bend ++ routed) (by simp)]
  rw [selected_append
    (List.replicate bend.length true)
    (List.replicate routed.length false)
    bend routed (by simp)]
  simp

end LeanTrominoes.AlignedRetainedTerminalSlotFilter
