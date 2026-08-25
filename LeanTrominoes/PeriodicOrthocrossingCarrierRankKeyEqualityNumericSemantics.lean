/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityHorizontalNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityVerticalNumericSemantics

/-! # Numeric semantics of complete carrier-rank key equality -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyEquality

open SignedUnaryStrictLower

theorem decide_prod_eq
    {First Second : Type*} [DecidableEq First] [DecidableEq Second]
    (first second : First × Second) :
    (decide (first.1 = second.1) && decide (first.2 = second.2)) =
      decide (first = second) := by
  rcases first with ⟨firstHead, firstTail⟩
  rcases second with ⟨secondHead, secondTail⟩
  simp

theorem decide_carrierKey_eq
    (first second : Nat × Nat × Cell) :
    (decide ((first.1, first.2.1) = (second.1, second.2.1)) &&
      decide (first.2.2 = second.2.2)) = decide (first = second) := by
  rcases first with ⟨firstRoute, firstSegment, firstTranslation⟩
  rcases second with ⟨secondRoute, secondSegment, secondTranslation⟩
  by_cases routeEq : firstRoute = secondRoute <;>
    by_cases segmentEq : firstSegment = secondSegment <;>
      by_cases translationEq : firstTranslation = secondTranslation <;>
        simp [routeEq, segmentEq, translationEq]

theorem indexBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    indexBits (PeriodicCNF.numericRouteDescriptors formula) =
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup
      matrix datums fun first second =>
        decide ((first.key.1, first.key.2.1) =
          (second.key.1, second.key.2.1)) := by
  unfold indexBits combined
  change pairwise .conjunction
      (fieldBits .route (PeriodicCNF.numericRouteDescriptors formula))
      (fieldBits .segment (PeriodicCNF.numericRouteDescriptors formula)) = _
  rw [fieldBits_numericRouteDescriptors formula wellFormed degree
      isLocal forward nonempty .route,
    fieldBits_numericRouteDescriptors formula wellFormed degree
      isLocal forward nonempty .segment,
    pairwise_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  change (decide (first.key.1 = second.key.1) &&
      decide (first.key.2.1 = second.key.2.1)) = _
  exact decide_prod_eq
    (first.key.1, first.key.2.1) (second.key.1, second.key.2.1)

theorem translationBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    translationBits (PeriodicCNF.numericRouteDescriptors formula) =
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup
      matrix datums fun first second =>
        decide (first.key.2.2 = second.key.2.2) := by
  unfold translationBits combined
  change pairwise .conjunction
      (horizontalBits (PeriodicCNF.numericRouteDescriptors formula))
      (verticalBits (PeriodicCNF.numericRouteDescriptors formula)) = _
  rw [horizontalBits_numericRouteDescriptors formula wellFormed degree
      isLocal forward nonempty,
    verticalBits_numericRouteDescriptors formula wellFormed degree
      isLocal forward nonempty,
    pairwise_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  change (decide (first.key.2.2.1 = second.key.2.2.1) &&
      decide (first.key.2.2.2 = second.key.2.2.2)) = _
  exact decide_prod_eq first.key.2.2 second.key.2.2

/-- On valid numeric routes, the compiled matrix marks exactly the ordered
pairs of deduplicated carrier-rank data belonging to the same carrier key. -/
theorem bits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    bits (PeriodicCNF.numericRouteDescriptors formula) =
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup
      datums.flatMap fun first =>
        datums.map fun second => decide (first.key = second.key) := by
  unfold bits combined
  change pairwise .conjunction
      (indexBits (PeriodicCNF.numericRouteDescriptors formula))
      (translationBits (PeriodicCNF.numericRouteDescriptors formula)) = _
  rw [indexBits_numericRouteDescriptors formula wellFormed degree
      isLocal forward nonempty,
    translationBits_numericRouteDescriptors formula wellFormed degree
      isLocal forward nonempty,
    pairwise_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  change (decide ((first.key.1, first.key.2.1) =
        (second.key.1, second.key.2.1)) &&
      decide (first.key.2.2 = second.key.2.2)) = _
  exact decide_carrierKey_eq first.key second.key

end CarrierRankKeyEquality
end LeanTrominoes.PeriodicOrthocrossing
