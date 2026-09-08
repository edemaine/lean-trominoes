/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedAtomOccurrences
import LeanTrominoes.PeriodicOneInThreeToThreeDMTaggedOccurrenceFieldLookup
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationExactRouteDirectionBlockList

/-! # Clause/literal-index fields retain exact normalized presentation order -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

/-- A field indexed by the actual clause and literal positions, presented in
clause-major and literal-minor order. -/
def presentedIncidenceIndexFields {Variable Field : Type*}
    (source : PositionedPeriodicCNF Variable) (field : Nat → Nat → Field) : List Field :=
  (PeriodicThreeSATThree.taggedLiterals source.erase).map
    (fun tagged => field tagged.2.1 tagged.2.2)

/-- Index-only fields use the actual ordered clause arities. -/
theorem presentedIncidenceIndexFields_eq_clauseRanges {Variable Field : Type*}
    (source : PositionedPeriodicCNF Variable) (field : Nat → Nat → Field) :
    presentedIncidenceIndexFields source field =
      source.clauses.zipIdx.flatMap (fun clause =>
        (List.range clause.1.literals.length).map (field clause.2)) := by
  simp only [presentedIncidenceIndexFields, PeriodicThreeSATThree.taggedLiterals,
    PositionedPeriodicCNF.erase, List.zipIdx_map, List.flatMap_map,
    List.map_flatMap, List.map_map, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq]
  apply List.flatMap_congr
  intro clause _member
  change clause.1.literals.zipIdx.map ((field clause.2) ∘ Prod.snd) = _
  rw [← List.map_map, List.zipIdx_map_snd, ← List.range_eq_range']

/-- Scaling and changing clause anchors preserve every index-only field. -/
theorem presentedIncidenceIndexFields_normalized_scale {Variable Field : Type*}
    (source : PositionedPeriodicCNF Variable) (placement : PeriodicVariablePlacement Variable)
    (factor : Nat) (field : Nat → Nat → Field) :
    presentedIncidenceIndexFields
        (normalizedPositionedSource (source.scale factor) (placement.scale factor)) field =
      presentedIncidenceIndexFields source field := by
  rw [presentedIncidenceIndexFields_eq_clauseRanges, presentedIncidenceIndexFields_eq_clauseRanges]
  simp only [normalizedPositionedSource, PositionedPeriodicCNF.anchorNormalize,
    PositionedPeriodicCNF.scale_clauses, List.zipIdx_map, List.flatMap_map,
    Prod.map_fst, Prod.map_snd, id_eq,
    PositionedPeriodicClause.scale_literals, PeriodicClause.anchorNormalize, List.length_map]

/-- The actual horizontal normalization preserves the full clause/literal
index-field stream. -/
theorem presentedIncidenceIndexFields_horizontal_normalized {Field : Type*}
    (source : PeriodicCNF Nat) (field : Nat → Nat → Field) :
    presentedIncidenceIndexFields (horizontalSemanticNormalizedRibbonSource source) field =
      presentedIncidenceIndexFields (horizontalRoutedFormulaComputed source) field := by
  unfold horizontalSemanticNormalizedRibbonSource
  rw [presentedIncidenceIndexFields_normalized_scale,
    horizontalRoutedFormulaComputed_eq_semanticData]

/-- The stored route-word presentation uses precisely these clause/literal
indices; no geometric information is lost by this reindexing. -/
theorem presentedIncidenceDirectionWords_eq_indexFields {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.presentedIncidenceDirectionWords source routes =
      presentedIncidenceIndexFields source (fun clauseIndex literalIndex =>
        Gadget.unitSubdivisionDirections (routes clauseIndex literalIndex)) := by
  simp only [PeriodicOneInThreePolarityNormalizationRouteSubdivision.presentedIncidenceDirectionWords,
    presentedIncidenceIndexFields, PeriodicThreeSATThree.taggedLiterals,
    PositionedPeriodicCNF.erase, List.zipIdx_map, List.flatMap_map,
    List.map_flatMap, List.map_map, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq]

end LeanTrominoes.PeriodicCNFStripReduction
