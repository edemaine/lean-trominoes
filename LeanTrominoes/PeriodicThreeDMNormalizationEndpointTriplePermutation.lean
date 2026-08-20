/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationCellTypeComputability
import Mathlib.Data.List.Permutation

/-! # Endpoint-triple normalization ignores enumeration order -/

noncomputable section

namespace LeanTrominoes

open Gadget DegreeThreeVertexNormalization

namespace PeriodicThreeDM
namespace NormalizationCompiler

def endpointTripleDataList
    (data : EndpointTripleData) : List EndpointSideColor :=
  [data.1, data.2.1, data.2.2]

/-- An explicit three-element form of list permutation. -/
theorem perm_triple_cases {Value : Type*}
    {first second third otherFirst otherSecond otherThird : Value}
    (permuted : List.Perm
      [otherFirst, otherSecond, otherThird]
      [first, second, third]) :
    (otherFirst = first ∧ otherSecond = second ∧
        otherThird = third) ∨
      (otherFirst = first ∧ otherSecond = third ∧
        otherThird = second) ∨
      (otherFirst = second ∧ otherSecond = first ∧
        otherThird = third) ∨
      (otherFirst = second ∧ otherSecond = third ∧
        otherThird = first) ∨
      (otherFirst = third ∧ otherSecond = first ∧
        otherThird = second) ∨
      (otherFirst = third ∧ otherSecond = second ∧
        otherThird = first) := by
  have computed :
      [first, second, third].permutations =
        [[first, second, third],
          [second, first, third],
          [third, second, first],
          [second, third, first],
          [third, first, second],
          [first, third, second]] := by
    simp [List.permutations, List.permutationsAux,
      List.permutationsAux.rec, List.permutationsAux2]
  have member :
      [otherFirst, otherSecond, otherThird] ∈
        [first, second, third].permutations :=
    List.mem_permutations.mpr permuted
  rw [computed] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with order | order | order | order | order | order
  all_goals
    simp only [List.cons.injEq, and_true] at order
  · exact Or.inl order
  · exact Or.inr (Or.inr (Or.inl order))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr order))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl order)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl order))))
  · exact Or.inr (Or.inl order)

/-- Reordering three distinct side/color records does not change the
canonical port coloring selected from them. -/
theorem canonicalColorFromData_eq_of_perm
    (data otherData : EndpointTripleData)
    (permuted : List.Perm
      (endpointTripleDataList otherData) (endpointTripleDataList data))
    (sidesNodup :
      (endpointTripleDataList data).map Prod.fst |>.Nodup) :
    (fun port => canonicalColorFromData (some data, port)) =
      fun port => canonicalColorFromData (some otherData, port) := by
  rcases data with ⟨first, second, third⟩
  rcases otherData with ⟨otherFirst, otherSecond, otherThird⟩
  unfold endpointTripleDataList at permuted sidesNodup
  simp only at permuted sidesNodup ⊢
  rcases perm_triple_cases permuted with
    order | order | order | order | order | order
  all_goals
    rcases order with ⟨firstEq, secondEq, thirdEq⟩
    subst otherFirst
    subst otherSecond
    subst otherThird
    funext port
    rcases first with ⟨firstSide, firstColor⟩
    rcases second with ⟨secondSide, secondColor⟩
    rcases third with ⟨thirdSide, thirdColor⟩
    simp only [List.map_cons, List.map_nil] at sidesNodup
    cases firstSide <;> cases secondSide <;> cases thirdSide <;>
      cases port <;>
      simp_all [canonicalColorFromData, colorFromTripleData,
        omittedSide, boundarySide]

/-- Hence the final trichromatic order is invariant under endpoint-list
permutation whenever the three used sides are distinct. -/
theorem trichromaticOrderFromData_eq_of_perm
    (first second : EndpointTripleData)
    (permuted : List.Perm
      (endpointTripleDataList second) (endpointTripleDataList first))
    (sidesNodup :
      (endpointTripleDataList first).map Prod.fst |>.Nodup) :
    trichromaticOrderFromData (some first) =
      trichromaticOrderFromData (some second) := by
  unfold trichromaticOrderFromData
  exact congrArg trichromaticOrder
    (canonicalColorFromData_eq_of_perm
      first second permuted sidesNodup)

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
