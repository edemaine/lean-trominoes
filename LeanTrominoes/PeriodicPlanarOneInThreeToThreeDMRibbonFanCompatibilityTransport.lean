/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalized
import LeanTrominoes.PositionedPeriodicCNFRibbonScaling
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeRouteOrders

/-!
# Transporting ribbon fan compatibility

The final ribbon construction doubles its source drawing and then normalizes
clause anchors.  Neither operation changes the cyclic order of incidence
routes at variables or clauses.  This file proves those two transport facts
and packages them as clockwise compatibility for the padded normalized
presentation.
-/

namespace LeanTrominoes

namespace PeriodicOneInThreeToThreeDM

/-- Anchor normalization leaves the clause/literal index sequence of each
variable's occurrences unchanged. -/
theorem occurrencesOf_anchorNormalize_indices
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) :
    (occurrencesOf source.anchorNormalize atom).map Prod.snd =
      (occurrencesOf source atom).map Prod.snd := by
  let key := fun tagged : TaggedOccurrence Variable =>
    (tagged.1.atom, tagged.2)
  have project (tagged : List (TaggedOccurrence Variable)) :
      (tagged.filter fun occurrence =>
          decide (occurrence.1.atom = atom)).map Prod.snd =
        ((tagged.map key).filter fun occurrence =>
          decide (occurrence.1 = atom)).map Prod.snd := by
    induction tagged with
    | nil => rfl
    | cons head tail induction =>
        by_cases same : head.1.atom = atom <;>
          simp [same, key, induction]
  have taggedKeys :
      (PeriodicThreeSATThree.taggedLiterals
          source.anchorNormalize).map key =
        (PeriodicThreeSATThree.taggedLiterals source).map key := by
    unfold PeriodicThreeSATThree.taggedLiterals
      PeriodicCNF.anchorNormalize
    have clauseHelper
        (clause : PeriodicClause Variable)
        (clauseIndex : Nat) :
        ((clause.anchorNormalize.zipIdx.map fun taggedLiteral =>
              (taggedLiteral.1, clauseIndex, taggedLiteral.2)).map key) =
          ((clause.zipIdx.map fun taggedLiteral =>
              (taggedLiteral.1, clauseIndex, taggedLiteral.2)).map key) := by
      unfold PeriodicClause.anchorNormalize
      rw [List.zipIdx_map]
      simp [key, Function.comp_def]
    have helper
        (clauses : List (PeriodicClause Variable)) (start : Nat) :
        ((((clauses.map PeriodicClause.anchorNormalize).zipIdx start).flatMap
              fun taggedClause =>
                taggedClause.1.zipIdx.map fun taggedLiteral =>
                  (taggedLiteral.1, taggedClause.2, taggedLiteral.2)).map key) =
          (((clauses.zipIdx start).flatMap fun taggedClause =>
              taggedClause.1.zipIdx.map fun taggedLiteral =>
                (taggedLiteral.1, taggedClause.2, taggedLiteral.2)).map key) := by
      induction clauses generalizing start with
      | nil => rfl
      | cons clause rest induction =>
          simp only [List.map_cons, List.zipIdx_cons,
            List.flatMap_cons, List.map_append]
          exact congrArg₂ (fun first second => first ++ second)
            (clauseHelper clause start) (induction (start + 1))
    exact helper source.clauses 0
  unfold occurrencesOf
  rw [project, project, taggedKeys]

/-- Consequently, occurrence-slot lookup retains the same clause and literal
indices through anchor normalization. -/
theorem occurrenceAt_anchorNormalize_indices
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (slot : OccurrenceSlot) :
    (occurrenceAt source.anchorNormalize atom slot).map Prod.snd =
      (occurrenceAt source atom slot).map Prod.snd := by
  unfold occurrenceAt
  rw [← List.getElem?_map, ← List.getElem?_map,
    occurrencesOf_anchorNormalize_indices]

end PeriodicOneInThreeToThreeDM

namespace PositionedPeriodicCNF

/-- Positive uniform coordinate scaling preserves clockwise variable-route
order. -/
theorem VariableRoutesInOccurrenceOrder.scaleCoordinates
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {routes : IncidenceRoutes}
    (ordered : source.VariableRoutesInOccurrenceOrder routes)
    (factor : Nat)
    (factorPositive : 0 < factor) :
    (source.scale factor).VariableRoutesInOccurrenceOrder
      (scaleIncidenceRoutes factor routes) := by
  intro atom first second third
    firstLookup secondLookup thirdLookup
  have clockwise :=
    ordered atom first second third
      (by simpa using firstLookup)
      (by simpa using secondLookup)
      (by simpa using thirdLookup)
  have factorPositiveInt : (0 : Int) < factor := by
    exact_mod_cast factorPositive
  simpa [scaleIncidenceRoutes,
    AxisDirection.polylineLastDirection_scalePolyline
      factor factorPositiveInt] using clockwise

/-- Anchor normalization preserves clockwise variable-route order because
each occurrence keeps its presentation indices and the stored route family
is unchanged. -/
theorem VariableRoutesInOccurrenceOrder.anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {routes : IncidenceRoutes}
    (ordered : source.VariableRoutesInOccurrenceOrder routes)
    (placement : PeriodicVariablePlacement Variable) :
    (source.anchorNormalize placement).VariableRoutesInOccurrenceOrder
      routes := by
  intro atom first second third
    firstLookup secondLookup thirdLookup
  have recover :
      ∀ (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
        (normalized : PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable),
        PeriodicOneInThreeToThreeDM.occurrenceAt
            (source.anchorNormalize placement).erase atom slot =
          some normalized →
        ∃ original,
          PeriodicOneInThreeToThreeDM.occurrenceAt
              source.erase atom slot = some original ∧
            original.2 = normalized.2 := by
    intro slot normalized normalizedLookup
    have indices :=
      PeriodicOneInThreeToThreeDM.occurrenceAt_anchorNormalize_indices
        source.erase atom slot
    rw [← PositionedPeriodicCNF.erase_anchorNormalize] at indices
    rw [normalizedLookup] at indices
    cases originalLookup :
        PeriodicOneInThreeToThreeDM.occurrenceAt
          source.erase atom slot with
    | none => simp [originalLookup] at indices
    | some original =>
        refine ⟨original, rfl, ?_⟩
        simpa [originalLookup] using indices.symm
  rcases recover .first first firstLookup with
    ⟨originalFirst, originalFirstLookup, firstIndices⟩
  rcases recover .second second secondLookup with
    ⟨originalSecond, originalSecondLookup, secondIndices⟩
  rcases recover .third third thirdLookup with
    ⟨originalThird, originalThirdLookup, thirdIndices⟩
  have clockwise :=
    ordered atom originalFirst originalSecond originalThird
      originalFirstLookup originalSecondLookup originalThirdLookup
  simpa [firstIndices, secondIndices, thirdIndices] using clockwise

/-- Positive uniform coordinate scaling preserves clockwise ternary-clause
route order. -/
theorem TernaryClauseRoutesInClockwiseOrder.scaleCoordinates
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    {routes : IncidenceRoutes}
    (ordered : source.TernaryClauseRoutesInClockwiseOrder routes)
    (factor : Nat)
    (factorPositive : 0 < factor) :
    (source.scale factor).TernaryClauseRoutesInClockwiseOrder
      (scaleIncidenceRoutes factor routes) := by
  intro scaledClause clauseIndex scaledMember scaledArity
  rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map] at scaledMember
  rcases List.mem_map.mp scaledMember with
    ⟨taggedClause, taggedMember, scaledEq⟩
  rcases taggedClause with ⟨sourceClause, sourceClauseIndex⟩
  have indexEq : sourceClauseIndex = clauseIndex :=
    congrArg Prod.snd scaledEq
  subst clauseIndex
  have clauseEq :
      sourceClause.scale factor = scaledClause :=
    congrArg Prod.fst scaledEq
  have sourceArity : sourceClause.literals.length = 3 := by
    simpa [← clauseEq] using scaledArity
  have clockwise :=
    ordered sourceClause sourceClauseIndex taggedMember sourceArity
  have factorPositiveInt : (0 : Int) < factor := by
    exact_mod_cast factorPositive
  simpa [scaleIncidenceRoutes,
    AxisDirection.polylineFirstDirection_scalePolyline
      factor factorPositiveInt] using clockwise

/-- Anchor normalization preserves clockwise ternary-clause route order:
literal indices and the stored route family are unchanged. -/
theorem TernaryClauseRoutesInClockwiseOrder.anchorNormalize
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    {routes : IncidenceRoutes}
    (ordered : source.TernaryClauseRoutesInClockwiseOrder routes)
    (placement : PeriodicVariablePlacement Variable) :
    (source.anchorNormalize placement).TernaryClauseRoutesInClockwiseOrder
      routes := by
  intro normalizedClause clauseIndex normalizedMember normalizedArity
  change
    (normalizedClause, clauseIndex) ∈
      (source.clauses.map fun clause =>
        ⟨canonicalClausePosition placement clause,
          clause.literals.anchorNormalize⟩).zipIdx
    at normalizedMember
  rw [List.zipIdx_map] at normalizedMember
  rcases List.mem_map.mp normalizedMember with
    ⟨taggedClause, taggedMember, normalizedEq⟩
  rcases taggedClause with ⟨sourceClause, sourceClauseIndex⟩
  have indexEq : sourceClauseIndex = clauseIndex :=
    congrArg Prod.snd normalizedEq
  subst clauseIndex
  have clauseEq :
      (sourceClause.literals.anchorNormalize).length =
        normalizedClause.literals.length := by
    exact congrArg (fun clause => clause.literals.length)
      (congrArg Prod.fst normalizedEq)
  have sourceArity : sourceClause.literals.length = 3 := by
    rw [← clauseEq] at normalizedArity
    simpa [PeriodicClause.anchorNormalize] using normalizedArity
  exact ordered sourceClause sourceClauseIndex taggedMember sourceArity

end PositionedPeriodicCNF

namespace PeriodicPlanarOneInThreeToThreeDM

/-- The doubled and anchor-normalized source retains clockwise-compatible
coordinated ribbon fans. -/
theorem paddedNormalizedRibbonReady_sourceRibbonFansClockwiseCompatible
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      source.VariableRoutesInOccurrenceOrder presentation.routes)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes) :
    SourceRibbonFansClockwiseCompatible
      (normalizedRibbonReadyIncidencePresentation presentation.scaleTwo
        |>.toPlanarIncidencePresentation) := by
  let padded := presentation.scaleTwo
  let normalized := normalizedRibbonReadyIncidencePresentation padded
  apply sourceRibbonFansClockwiseCompatible_of_clockwiseRouteOrders
    normalized
  · simpa [normalizedPositionedSource] using
      PeriodicCNF.anchorNormalize_widthAtMost
        (source.scale 2).erase 3 (by simpa using width)
  · simpa [normalizedPositionedSource] using
      PeriodicCNF.anchorNormalize_occurrencesAtMost
        (source.scale 2).erase 3 (by simpa using occurrences)
  · simpa [normalizedPositionedSource] using
      PeriodicCNF.anchorNormalize_arityTwoOrThree
        (source.scale 2).erase (by simpa using arity)
  · apply sourceVariableDirectionsInOccurrenceOrder_of_routes
      normalized.toPlanarIncidencePresentation
    exact
      (variableOrdered.scaleCoordinates 2 (by decide)).anchorNormalize
        (placement.scale 2)
  · exact
      (clauseOrdered.scaleCoordinates 2 (by decide)).anchorNormalize
        (placement.scale 2)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
