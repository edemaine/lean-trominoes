/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarNormalizationComponents
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierNormalizationDegree
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATPeriodicization

/-!
# Componentwise normalization of retained periodic planar SAT

The retained planar-SAT formula differs from the canonical formula only in
its straight-carrier equality family.  This file repeats the five-component
normalization interface with that family replaced, so global clause
deduplication can be bounded by separate crossover, retained-carrier, bend,
routed-clause, and routed-variable deduplication.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Retained straight-carrier clauses after periodic normalization, embedded
in the complete planar-SAT variable type. -/
def embeddedNormalizedRetainedCompleteCarrierClauses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (PeriodicClause (PeriodicPlanarSATVariable Variable)) :=
  (PeriodicEquality.normalizedFormulaClauses
    (normalizeCarrierNode
      (PeriodicCNF.incidenceGraph formula))
    (retainedDrawingCompleteCarrierLinks
      (PeriodicCNF.incidenceGraph formula))).map
        (@embedPeriodicCarrierClause Variable)

/-- Normalized retained straight carriers followed by the unchanged
normalized bend family. -/
def normalizedEmbeddedRetainedRouteWireClauses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (PeriodicClause (PeriodicPlanarSATVariable Variable)) :=
  embeddedNormalizedRetainedCompleteCarrierClauses formula ++
    embeddedNormalizedRouteBendClauses formula

/-- Periodicizing and anchor-normalizing the retained route-wire block gives
the retained normalized carrier family followed by the canonical bend
family. -/
theorem normalizedRetainedScopedDrawingRouteWireFormula_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (((retainedScopedDrawingRouteWireFormula
      (PeriodicCNF.incidenceGraph formula)).map fun clause =>
        clause.rename
          (@planarSATCoreVariableMap Variable)).map
            (periodicizePlanarSATClause formula)).map
              PeriodicClause.anchorNormalize =
      normalizedEmbeddedRetainedRouteWireClauses formula := by
  unfold retainedScopedDrawingRouteWireFormula
    retainedDrawingRouteWireFormula
    retainedDrawingCompleteCarrierFormula
    drawingRouteBendFormula
    normalizedEmbeddedRetainedRouteWireClauses
    embeddedNormalizedRetainedCompleteCarrierClauses
    embeddedNormalizedRouteBendClauses
    PeriodicEquality.normalizedFormulaClauses
  simp only [List.map_append, List.map_map]
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro clause _clauseMem
    exact
      (congrArg
        (fun periodicClause =>
          PeriodicClause.anchorNormalize periodicClause)
        (periodicizePlanarSATClause_carrier_core_rename
          formula clause)).trans
        (embedPeriodicCarrierClause_anchorNormalize
          (Variable := Variable)
          (PeriodicEquality.periodicizeClause
            (normalizeCarrierNode
              (PeriodicCNF.incidenceGraph formula)) clause)).symm
  · apply List.map_congr_left
    intro clause _clauseMem
    exact
      (congrArg
        (fun periodicClause =>
          PeriodicClause.anchorNormalize periodicClause)
        (periodicizePlanarSATClause_carrier_core_rename
          formula clause)).trans
        (embedPeriodicCarrierClause_anchorNormalize
          (Variable := Variable)
          (PeriodicEquality.periodicizeClause
            (normalizeCarrierNode
              (PeriodicCNF.incidenceGraph formula)) clause)).symm

/-- Anchor-normalized periodic clauses of the retained local route core. -/
def normalizedRetainedScopedDrawingPlanarSATCoreClauses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (PeriodicClause (PeriodicPlanarSATVariable Variable)) :=
  ((retainedScopedDrawingPlanarSATCore formula).map
    (periodicizePlanarSATClause formula)).map
      PeriodicClause.anchorNormalize

/-- The retained normalized core is the unchanged crossover family followed
by the retained route-wire family. -/
theorem normalizedRetainedScopedDrawingPlanarSATCoreClauses_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    normalizedRetainedScopedDrawingPlanarSATCoreClauses formula =
      normalizedScopedDrawingCrossoverClauses formula ++
        normalizedEmbeddedRetainedRouteWireClauses formula := by
  unfold normalizedRetainedScopedDrawingPlanarSATCoreClauses
    retainedScopedDrawingPlanarSATCore
    retainedDrawingRoutePlanarCoreFormula
    normalizedScopedDrawingCrossoverClauses
  simp only [List.map_append]
  apply congrArg₂ (· ++ ·)
  · rfl
  · exact
      normalizedRetainedScopedDrawingRouteWireFormula_eq formula

/-- Exact three-block decomposition of the normalized retained periodic
formula into its route core and two external source families. -/
theorem retainedDrawingPeriodicPlanarSATFormula_anchorNormalize_clauses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedDrawingPeriodicPlanarSATFormula
      formula).anchorNormalize.clauses =
      normalizedRetainedScopedDrawingPlanarSATCoreClauses formula ++
        normalizedRoutedClauseClauses formula ++
          PeriodicEquality.normalizedFormulaClauses
            (normalizePlanarSATNode
              (PeriodicCNF.incidenceGraph formula))
            (drawingRoutedVariableLinks formula) := by
  unfold retainedDrawingPeriodicPlanarSATFormula
    retainedDrawingPlanarSATFormula
    PeriodicCNF.anchorNormalize
    normalizedRetainedScopedDrawingPlanarSATCoreClauses
  simp only [List.map_append, List.append_assoc]
  rw [normalizedScopedDrawingRoutedClauseFormula_eq,
    normalizedScopedDrawingRoutedVariableFormula_eq]

/-- Exact five-family decomposition used for componentwise occurrence
accounting. -/
theorem
    retainedDrawingPeriodicPlanarSATFormula_anchorNormalize_five_components
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedDrawingPeriodicPlanarSATFormula
      formula).anchorNormalize.clauses =
      normalizedScopedDrawingCrossoverClauses formula ++
        (embeddedNormalizedRetainedCompleteCarrierClauses formula ++
          (embeddedNormalizedRouteBendClauses formula ++
            (normalizedRoutedClauseClauses formula ++
              PeriodicEquality.normalizedFormulaClauses
                (normalizePlanarSATNode
                  (PeriodicCNF.incidenceGraph formula))
                (drawingRoutedVariableLinks formula)))) := by
  rw [
    retainedDrawingPeriodicPlanarSATFormula_anchorNormalize_clauses,
    normalizedRetainedScopedDrawingPlanarSATCoreClauses_eq]
  unfold normalizedEmbeddedRetainedRouteWireClauses
  simp only [List.append_assoc]

/-- The normalized retained formula with each geometric family deduplicated
before concatenation. -/
def componentwiseDeduplicatedRetainedDrawingPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF (PeriodicPlanarSATVariable Variable) :=
  ⟨(normalizedScopedDrawingCrossoverClauses formula).dedup ++
    ((embeddedNormalizedRetainedCompleteCarrierClauses formula).dedup ++
      ((embeddedNormalizedRouteBendClauses formula).dedup ++
        ((normalizedRoutedClauseClauses formula).dedup ++
          (PeriodicEquality.normalizedFormulaClauses
            (normalizePlanarSATNode
              (PeriodicCNF.incidenceGraph formula))
            (drawingRoutedVariableLinks formula)).dedup)))⟩

/-- Occurrences in the retained componentwise formula split as the sum of
the same five component counts. -/
theorem
    componentwiseDeduplicatedRetainedDrawingPeriodicPlanarSATFormula_occurrence_count
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    (componentwiseDeduplicatedRetainedDrawingPeriodicPlanarSATFormula
      formula).variableOccurrences.count atom =
      (PeriodicCNF.variableOccurrences
        ⟨(normalizedScopedDrawingCrossoverClauses
          formula).dedup⟩).count atom +
      ((PeriodicCNF.variableOccurrences
        ⟨(embeddedNormalizedRetainedCompleteCarrierClauses
          formula).dedup⟩).count atom +
      ((PeriodicCNF.variableOccurrences
        ⟨(embeddedNormalizedRouteBendClauses
          formula).dedup⟩).count atom +
      ((PeriodicCNF.variableOccurrences
        ⟨(normalizedRoutedClauseClauses
          formula).dedup⟩).count atom +
      (PeriodicCNF.variableOccurrences
        ⟨(PeriodicEquality.normalizedFormulaClauses
          (normalizePlanarSATNode
            (PeriodicCNF.incidenceGraph formula))
          (drawingRoutedVariableLinks formula)).dedup⟩).count atom))) := by
  unfold
    componentwiseDeduplicatedRetainedDrawingPeriodicPlanarSATFormula
  exact
    PeriodicCNF.five_component_occurrence_count
      (normalizedScopedDrawingCrossoverClauses formula).dedup
      (embeddedNormalizedRetainedCompleteCarrierClauses formula).dedup
      (embeddedNormalizedRouteBendClauses formula).dedup
      (normalizedRoutedClauseClauses formula).dedup
      (PeriodicEquality.normalizedFormulaClauses
        (normalizePlanarSATNode
          (PeriodicCNF.incidenceGraph formula))
        (drawingRoutedVariableLinks formula)).dedup
      atom

/-- Unwrapped retained formula after anchor normalization and global clause
deduplication. -/
def retainedDeduplicatedDrawingPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF (PeriodicPlanarSATVariable Variable) :=
  (retainedDrawingPeriodicPlanarSATFormula
    formula).anchorNormalize.deduplicate

/-- Global retained clause deduplication cannot create more occurrences than
deduplicating its five normalized families separately. -/
theorem
    retainedDeduplicatedDrawingPeriodicPlanarSATFormula_variableOccurrences_sublist
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List.Sublist
      (retainedDeduplicatedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences
      (componentwiseDeduplicatedRetainedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences := by
  unfold retainedDeduplicatedDrawingPeriodicPlanarSATFormula
    componentwiseDeduplicatedRetainedDrawingPeriodicPlanarSATFormula
    PeriodicCNF.deduplicate
  rw [
    retainedDrawingPeriodicPlanarSATFormula_anchorNormalize_five_components]
  exact
    PeriodicCNF.deduplicate_five_components_variableOccurrences_sublist
      (normalizedScopedDrawingCrossoverClauses formula)
      (embeddedNormalizedRetainedCompleteCarrierClauses formula)
      (embeddedNormalizedRouteBendClauses formula)
      (normalizedRoutedClauseClauses formula)
      (PeriodicEquality.normalizedFormulaClauses
        (normalizePlanarSATNode
          (PeriodicCNF.incidenceGraph formula))
        (drawingRoutedVariableLinks formula))

end PeriodicOrthocrossing
end LeanTrominoes
