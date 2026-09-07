/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalClauseIncomingDirectionBlocks
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedFormulaSemanticBridge
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPresentationProperties

/-! # Occurrence fields in actual clause and literal presentation order -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicPlanarOneInThreeToThreeDM
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Actual connector kind and literal polarity, before regrouping by variable. -/
def presentedLiteralFields {Variable : Type*} (source : PositionedPeriodicCNF Variable) :
    List (VariableConnectorKind × Bool) :=
  source.clauses.flatMap fun clause => clause.literals.zipIdx.map fun literal =>
    (connectorKindOfLiteralIndex literal.2, literal.1.value)

/-- A polarity-normalized source's literal fields depend only on the ordered
clause arities and the genuine literal indices. -/
theorem presentedLiteralFields_eq_of_polarityNormalized {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (normalized : PeriodicOneInThreePolarityNormalization.FormulaPolarityNormalized source.erase) :
    presentedLiteralFields source = source.erase.clauses.flatMap fun clause =>
      (List.range clause.length).map fun index =>
        (connectorKindOfLiteralIndex index,
          PeriodicCNF.ClauseProfilePolarityNormalization.normalizedPolarity index) := by
  unfold presentedLiteralFields PositionedPeriodicCNF.erase
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro clause member
  have clauseNormalized := normalized clause.literals (List.mem_map.mpr ⟨clause, member, rfl⟩)
  have values : clause.literals.zipIdx.map
      (fun literal => (connectorKindOfLiteralIndex literal.2, literal.1.value)) =
        clause.literals.zipIdx.map fun literal =>
          (connectorKindOfLiteralIndex literal.2,
            PeriodicCNF.ClauseProfilePolarityNormalization.normalizedPolarity literal.2) := by
    apply List.map_congr_left
    intro literal literalMember
    exact congrArg (Prod.mk (connectorKindOfLiteralIndex literal.2))
      (PeriodicOneInThreePolarityNormalization.literal_value_eq_normalizedPolarity_of_clause
        clauseNormalized literalMember)
  rw [values]
  change clause.literals.zipIdx.map
    ((fun index => (connectorKindOfLiteralIndex index,
      PeriodicCNF.ClauseProfilePolarityNormalization.normalizedPolarity index)) ∘ Prod.snd) = _
  rw [← List.map_map, List.zipIdx_map_snd, ← List.range_eq_range']

/-- The executable horizontal routed formula obeys the fixed terminal
polarity convention at every actual literal. -/
theorem horizontalRoutedFormulaComputed_polarityNormalized (source : PeriodicCNF Nat) :
    PeriodicOneInThreePolarityNormalization.FormulaPolarityNormalized
      (horizontalRoutedFormulaComputed source).erase := by
  rw [horizontalRoutedFormulaComputed_eq_semanticData]
  exact formula_polarityNormalized _ _ _

/-- Literal fields and the reversed stored route's variable-end direction. -/
def presentedOccurrenceFields {Variable : Type*} (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    List ((VariableConnectorKind × Bool) × AxisDirection) :=
  source.clauses.zipIdx.flatMap fun clause => clause.1.literals.zipIdx.map fun literal =>
    ((connectorKindOfLiteralIndex literal.2, literal.1.value),
      ((unitSubdivisionDirections (routes clause.2 literal.2)).getLastD .invalid).opposite)

theorem presentedOccurrenceFields_map_literalFields {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (presentedOccurrenceFields source routes).map Prod.fst = presentedLiteralFields source := by
  unfold presentedOccurrenceFields presentedLiteralFields
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  simpa only [List.flatMap_map] using
    congrArg (List.flatMap fun clause : PositionedPeriodicClause Variable =>
      clause.literals.zipIdx.map fun literal =>
        (connectorKindOfLiteralIndex literal.2, literal.1.value))
      (List.zipIdx_map_fst 0 source.clauses)

theorem presentedOccurrenceFields_map_directions {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (presentedOccurrenceFields source routes).map Prod.snd =
      (presentedIncidenceDirectionWords source routes).map
        (fun word => (word.getLastD .invalid).opposite) := by
  simp only [presentedOccurrenceFields, presentedIncidenceDirectionWords,
    List.map_flatMap, List.map_map, Function.comp_def]

/-- Padding and anchor normalization preserve all occurrence fields read by
variable fans, while retaining the exact clause and literal order. -/
theorem presentedOccurrenceFields_normalized_scale {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) (factor : Nat) (positive : 0 < factor) :
    presentedOccurrenceFields
        (normalizedPositionedSource (source.scale factor) (placement.scale factor))
        (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes) =
      presentedOccurrenceFields source routes := by
  simp only [presentedOccurrenceFields, normalizedPositionedSource,
    PositionedPeriodicCNF.anchorNormalize, PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map, List.flatMap_map, List.map_map, Function.comp_def,
    Prod.map_fst, Prod.map_snd, id_eq, PositionedPeriodicClause.scale_literals,
    PeriodicClause.anchorNormalize, PeriodicLiteral.anchorNormalize_value,
    PositionedPeriodicCNF.scaleIncidenceRoutes_apply,
    unitSubdivisionDirections_scalePolyline factor positive,
    List.getLastD_eq_getLast?, repeatDirections_getLast? factor positive]

end LeanTrominoes.PeriodicCNFStripReduction
