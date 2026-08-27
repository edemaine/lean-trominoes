/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestHeaderData
import LeanTrominoes.PeriodicThreeDMNormalizationEndpointTriplePermutation

/-! # Route-request headers ignore endpoint enumeration order -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest

open DegreeThreeVertexNormalization
open NormalizationCompiler

/-- Reordering three distinct endpoint sides does not change their omitted
side. -/
theorem omittedSideFromData_some_eq_of_perm
    (data other : EndpointTripleData)
    (permuted : List.Perm
      (endpointTripleDataList other) (endpointTripleDataList data))
    (sidesNodup :
      (endpointTripleDataList data).map Prod.fst |>.Nodup) :
    omittedSideFromData (some data) =
      omittedSideFromData (some other) := by
  rcases data with ⟨first, second, third⟩
  rcases other with ⟨otherFirst, otherSecond, otherThird⟩
  unfold endpointTripleDataList at permuted sidesNodup
  simp only at permuted sidesNodup ⊢
  rcases perm_triple_cases permuted with
    order | order | order | order | order | order
  all_goals
    rcases order with ⟨firstEq, secondEq, thirdEq⟩
    subst otherFirst
    subst otherSecond
    subst otherThird
    rcases first with ⟨firstSide, firstColor⟩
    rcases second with ⟨secondSide, secondColor⟩
    rcases third with ⟨thirdSide, thirdColor⟩
    simp only [List.map_cons, List.map_nil] at sidesNodup
    cases firstSide <;> cases secondSide <;> cases thirdSide <;>
      simp_all [omittedSideFromData, omittedSide]

/-- All three choices at one endpoint are invariant under reordering its
three distinct fan records. -/
theorem EndpointHeaderData.choices_eq_of_perm
    (isTriple : Bool) (data other : EndpointTripleData)
    (endpoint : EndpointSideColor)
    (permuted : List.Perm
      (endpointTripleDataList other) (endpointTripleDataList data))
    (sidesNodup :
      (endpointTripleDataList data).map Prod.fst |>.Nodup) :
    let first : EndpointHeaderData :=
      ⟨isTriple, some data, endpoint⟩
    let second : EndpointHeaderData :=
      ⟨isTriple, some other, endpoint⟩
    first.firstChoice = second.firstChoice ∧
      first.secondChoice = second.secondChoice ∧
      first.finalChoice = second.finalChoice := by
  dsimp only
  have omittedEq := omittedSideFromData_some_eq_of_perm
    data other permuted sidesNodup
  have coloringEq := canonicalColorFromData_eq_of_perm
    data other permuted sidesNodup
  have countEq :
      (⟨isTriple, some data, endpoint⟩ : EndpointHeaderData).rotationCount =
        (⟨isTriple, some other, endpoint⟩ : EndpointHeaderData).rotationCount := by
    unfold EndpointHeaderData.rotationCount rotationCountFromData
    cases isTriple with
    | false => rfl
    | true =>
        simp only [if_true]
        exact congrArg
          (fun coloring =>
            rotationsToNorth (portOfColor coloring .red)) coloringEq
  have portEq :
      firstPortFromData (some data, endpoint) =
        firstPortFromData (some other, endpoint) := by
    unfold firstPortFromData
    rw [omittedEq]
  constructor
  · unfold EndpointHeaderData.firstChoice
    rw [omittedEq, portEq]
  constructor
  · unfold EndpointHeaderData.secondChoice
    rw [countEq, portEq]
  · unfold EndpointHeaderData.finalChoice EndpointHeaderData.secondPort
    rw [countEq, portEq]

end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes
