/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockIndexLookupSemantics
import LeanTrominoes.ListZipWithFourSemantics

/-! # Four-column zipping over block broadcasts -/

namespace LeanTrominoes.FiniteBlockIndices

/-- Zipping a flattened selector family with three block-broadcast columns
is the flattening of the corresponding source-wise mapped blocks. -/
theorem zipWith4_flatMap_broadcastValues
    {Source Selector First Second Third Target : Type*}
    (block : Source → List Selector)
    (combine : Selector → First → Second → Third → Target) :
    ∀ (source : List Source) (first : List First)
      (second : List Second) (third : List Third),
      source.length = first.length →
      source.length = second.length →
      source.length = third.length →
      List.zipWith4 combine
          (source.flatMap block)
          (broadcastValues (fun item => (block item).length) source first)
          (broadcastValues (fun item => (block item).length) source second)
          (broadcastValues (fun item => (block item).length) source third) =
        (List.zipWith4
          (fun item first second third =>
            (block item).map fun selector =>
              combine selector first second third)
          source first second third).flatten
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, sourceFirst, _, _ => by simp at sourceFirst
  | _ :: _, _ :: _, [], _, _, sourceSecond, _ => by simp at sourceSecond
  | _ :: _, _ :: _, _ :: _, [], _, _, sourceThird => by simp at sourceThird
  | item :: source, first :: firsts, second :: seconds, third :: thirds,
      sourceFirst, sourceSecond, sourceThird => by
      have firstLength : source.length = firsts.length := by
        exact Nat.succ.inj sourceFirst
      have secondLength : source.length = seconds.length := by
        exact Nat.succ.inj sourceSecond
      have thirdLength : source.length = thirds.length := by
        exact Nat.succ.inj sourceThird
      simp only [List.flatMap_cons, broadcastValues,
        List.zipWith_cons_cons, List.flatten_cons, List.zipWith4]
      change
        List.zipWith4 combine
            (block item ++ source.flatMap block)
            (List.replicate (block item).length first ++
              broadcastValues (fun later => (block later).length)
                source firsts)
            (List.replicate (block item).length second ++
              broadcastValues (fun later => (block later).length)
                source seconds)
            (List.replicate (block item).length third ++
              broadcastValues (fun later => (block later).length)
                source thirds) =
          (block item).map
              (fun selector => combine selector first second third) ++
            (List.zipWith4
              (fun later laterFirst laterSecond laterThird =>
                (block later).map fun selector =>
                  combine selector laterFirst laterSecond laterThird)
              source firsts seconds thirds).flatten
      rw [List.zipWith4_append_of_prefix_lengths combine
        (block item) (source.flatMap block)
        (List.replicate (block item).length first)
          (broadcastValues (fun later => (block later).length)
            source firsts)
        (List.replicate (block item).length second)
          (broadcastValues (fun later => (block later).length)
            source seconds)
        (List.replicate (block item).length third)
          (broadcastValues (fun later => (block later).length)
            source thirds)
        (by simp) (by simp) (by simp),
        List.zipWith4_replicate_three]
      rw [zipWith4_flatMap_broadcastValues block combine
        source firsts seconds thirds firstLength secondLength thirdLength]

end LeanTrominoes.FiniteBlockIndices
