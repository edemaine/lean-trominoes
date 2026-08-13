/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedFormula
import LeanTrominoes.PeriodicCNFPlanarSATClauseIndex

/-!
# Clause metadata for the retained planar SAT formula

The retained presentation has the same five component kinds and the same
local drawings as the canonical finite formula.  Only membership in the
straight-carrier family changes.  This file reuses the existing metadata
type, substitutes the selected retained carrier list in its validity
predicate and enumeration, and proves exact projection to
`retainedDrawingPlanarSATFormula`.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

namespace DrawingPlanarSATClauseMetadata

/-- Validity of clause metadata for the retained finite presentation.  The
four non-carrier cases are unchanged. -/
def RetainedValid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable) : Prop :=
  let graph := PeriodicCNF.incidenceGraph formula
  match metadata.source with
  | .crossover crossing localClauseIndex =>
      crossing ∈ orientedCrossingHalo graph ∧
        (metadata.clause, localClauseIndex) ∈
          (drawingPlanarSATCrossoverFormulaAt
            (Variable := Variable) crossing).zipIdx
  | .carrier link localClauseIndex =>
      link ∈ retainedDrawingCompleteCarrierLinks graph ∧
        (metadata.clause, localClauseIndex) ∈
          (drawingPlanarSATCarrierFormulaAt
            (Variable := Variable) link).zipIdx
  | .bend routeBend localClauseIndex =>
      routeBend ∈ (drawingRouteBends graph).dedup ∧
        (metadata.clause, localClauseIndex) ∈
          (drawingPlanarSATBendFormulaAt
            (Variable := Variable) graph routeBend).zipIdx
  | .routedClause site =>
      site ∈ drawingClauseRouteSites formula ∧
        metadata.clause =
          (routedClauseAt formula site).rename
            planarSATExternalVariableMap
  | .routedVariable site armIndex arm link localClauseIndex =>
      site ∈ drawingVariableRouteSites formula ∧
        (link, armIndex) ∈
            (routedVariableLinksAt formula site).zipIdx ∧
          arm = link.first.duplicatorArm ∧
          (metadata.clause, localClauseIndex) ∈
            (drawingPlanarSATRoutedVariableFormulaAt link).zipIdx

end DrawingPlanarSATClauseMetadata

/-- Clause metadata for the selected retained carrier links. -/
def retainedDrawingPlanarSATCarrierClauseMetadata
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (DrawingPlanarSATClauseMetadata Variable) :=
  (retainedDrawingCompleteCarrierLinks graph).flatMap
    drawingPlanarSATCarrierClauseMetadataFor

@[simp]
theorem retainedDrawingPlanarSATCarrierClauseMetadata_clauses
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (retainedDrawingPlanarSATCarrierClauseMetadata
      (Variable := Variable) graph).map
        DrawingPlanarSATClauseMetadata.clause =
      (retainedDrawingCompleteCarrierFormula graph).map fun clause =>
        (clause.rename fun node =>
          (Sum.inl node :
            Sum CarrierNode
              (CrossingRecord × CrossoverInternal))).rename
          (@planarSATCoreVariableMap Variable) := by
  simp [retainedDrawingPlanarSATCarrierClauseMetadata,
    drawingPlanarSATCarrierClauseMetadataFor,
    drawingPlanarSATCarrierFormulaAt,
    retainedDrawingCompleteCarrierFormula, equalityFamily,
    List.map_flatMap, List.map_map, Function.comp_def]

theorem retainedDrawingPlanarSATCarrierClauseMetadataFor_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        drawingPlanarSATCarrierClauseMetadataFor
          (Variable := Variable) link) :
    metadata.RetainedValid formula := by
  rw [drawingPlanarSATCarrierClauseMetadataFor] at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember, metadataEqual⟩
  subst metadata
  simpa [DrawingPlanarSATClauseMetadata.RetainedValid] using
    And.intro linkMember taggedClauseMember

theorem retainedDrawingPlanarSATCarrierClauseMetadata_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        retainedDrawingPlanarSATCarrierClauseMetadata
          (Variable := Variable)
          (PeriodicCNF.incidenceGraph formula)) :
    metadata.RetainedValid formula := by
  rcases List.mem_flatMap.mp metadataMember with
    ⟨link, linkMember, metadataMember⟩
  exact retainedDrawingPlanarSATCarrierClauseMetadataFor_valid
    formula link linkMember metadataMember

theorem drawingPlanarSATCrossoverClauseMetadata_retainedValid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        drawingPlanarSATCrossoverClauseMetadata
          (Variable := Variable)
          (PeriodicCNF.incidenceGraph formula)) :
    metadata.RetainedValid formula := by
  rcases List.mem_flatMap.mp metadataMember with
    ⟨crossing, crossingMember, metadataMember⟩
  rw [drawingPlanarSATCrossoverClauseMetadataFor] at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember, metadataEqual⟩
  subst metadata
  exact ⟨crossingMember, taggedClauseMember⟩

theorem drawingPlanarSATBendClauseMetadata_retainedValid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        drawingPlanarSATBendClauseMetadata
          (Variable := Variable)
          (PeriodicCNF.incidenceGraph formula)) :
    metadata.RetainedValid formula := by
  rcases List.mem_flatMap.mp metadataMember with
    ⟨routeBend, routeBendMember, metadataMember⟩
  rw [drawingPlanarSATBendClauseMetadataFor] at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember, metadataEqual⟩
  subst metadata
  simpa [DrawingPlanarSATClauseMetadata.RetainedValid] using
    And.intro routeBendMember taggedClauseMember

theorem drawingPlanarSATRoutedClauseMetadata_retainedValid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈ drawingPlanarSATRoutedClauseMetadata formula) :
    metadata.RetainedValid formula := by
  rw [drawingPlanarSATRoutedClauseMetadata] at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨site, siteMember, metadataEqual⟩
  subst metadata
  exact ⟨siteMember, rfl⟩

theorem drawingPlanarSATRoutedVariableClauseMetadata_retainedValid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈ drawingPlanarSATRoutedVariableClauseMetadata formula) :
    metadata.RetainedValid formula := by
  rcases List.mem_flatMap.mp metadataMember with
    ⟨site, siteMember, metadataMember⟩
  rcases List.mem_flatMap.mp metadataMember with
    ⟨taggedLink, linkMember, metadataMember⟩
  rw [drawingPlanarSATRoutedVariableClauseMetadataFor] at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember, metadataEqual⟩
  subst metadata
  simpa [DrawingPlanarSATClauseMetadata.RetainedValid] using
    And.intro siteMember
      (And.intro linkMember taggedClauseMember)

/-- Clause metadata parallel to the five families of the retained planar-SAT
formula. -/
def retainedDrawingPlanarSATClauseMetadata
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (DrawingPlanarSATClauseMetadata Variable) :=
  let graph := PeriodicCNF.incidenceGraph formula
  drawingPlanarSATCrossoverClauseMetadata graph ++
    retainedDrawingPlanarSATCarrierClauseMetadata graph ++
      drawingPlanarSATBendClauseMetadata graph ++
        drawingPlanarSATRoutedClauseMetadata formula ++
          drawingPlanarSATRoutedVariableClauseMetadata formula

/-- Forgetting retained source witnesses recovers the retained formula in
its exact global clause order. -/
@[simp]
theorem retainedDrawingPlanarSATClauseMetadata_clauses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedDrawingPlanarSATClauseMetadata formula).map
        DrawingPlanarSATClauseMetadata.clause =
      retainedDrawingPlanarSATFormula formula := by
  simp [retainedDrawingPlanarSATClauseMetadata,
    retainedDrawingPlanarSATFormula,
    retainedScopedDrawingPlanarSATCore,
    retainedDrawingRoutePlanarCoreFormula,
    retainedScopedDrawingRouteWireFormula,
    retainedDrawingRouteWireFormula,
    List.map_append, List.map_map, Function.comp_def]

/-- Every entry in the retained metadata list has a genuine component and
local clause index. -/
theorem retainedDrawingPlanarSATClauseMetadata_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈ retainedDrawingPlanarSATClauseMetadata formula) :
    metadata.RetainedValid formula := by
  let graph := PeriodicCNF.incidenceGraph formula
  by_cases crossoverMember :
      metadata ∈
        drawingPlanarSATCrossoverClauseMetadata
          (Variable := Variable) graph
  · exact drawingPlanarSATCrossoverClauseMetadata_retainedValid
      formula crossoverMember
  by_cases carrierMember :
      metadata ∈
        retainedDrawingPlanarSATCarrierClauseMetadata
          (Variable := Variable) graph
  · exact retainedDrawingPlanarSATCarrierClauseMetadata_valid
      formula carrierMember
  by_cases bendMember :
      metadata ∈
        drawingPlanarSATBendClauseMetadata
          (Variable := Variable) graph
  · exact drawingPlanarSATBendClauseMetadata_retainedValid
      formula bendMember
  by_cases routedClauseMember :
      metadata ∈ drawingPlanarSATRoutedClauseMetadata formula
  · exact drawingPlanarSATRoutedClauseMetadata_retainedValid
      formula routedClauseMember
  apply drawingPlanarSATRoutedVariableClauseMetadata_retainedValid formula
  simpa [retainedDrawingPlanarSATClauseMetadata, graph,
    crossoverMember, carrierMember, bendMember,
    routedClauseMember] using metadataMember

/-- The retained metadata enumeration is exhaustive: every component/local
clause witness satisfying `RetainedValid` occurs in the list. -/
theorem DrawingPlanarSATClauseMetadata.mem_retained_of_retainedValid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula) :
    metadata ∈ retainedDrawingPlanarSATClauseMetadata formula := by
  rcases metadata with ⟨clause, source⟩
  cases source <;>
    simp_all [DrawingPlanarSATClauseMetadata.RetainedValid,
      retainedDrawingPlanarSATClauseMetadata,
      drawingPlanarSATCrossoverClauseMetadata,
      drawingPlanarSATCrossoverClauseMetadataFor,
      retainedDrawingPlanarSATCarrierClauseMetadata,
      drawingPlanarSATCarrierClauseMetadataFor,
      drawingPlanarSATBendClauseMetadata,
      drawingPlanarSATBendClauseMetadataFor,
      drawingPlanarSATRoutedClauseMetadata,
      drawingPlanarSATRoutedVariableClauseMetadata,
      drawingPlanarSATRoutedVariableClauseMetadataFor]

/-- Membership in the retained metadata enumeration is exactly retained
component validity. -/
theorem DrawingPlanarSATClauseMetadata.mem_retained_iff_retainedValid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable) :
    metadata ∈ retainedDrawingPlanarSATClauseMetadata formula ↔
      metadata.RetainedValid formula :=
  ⟨retainedDrawingPlanarSATClauseMetadata_valid formula,
    metadata.mem_retained_of_retainedValid formula⟩

/-- Looking up a retained formula clause returns metadata carrying that exact
clause. -/
theorem retainedDrawingPlanarSATClauseMetadata_lookup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingPlanarSATFormula formula).zipIdx) :
    ∃ metadata,
      (retainedDrawingPlanarSATClauseMetadata
          formula)[clauseIndex]? = some metadata ∧
        metadata.clause = clause := by
  have clauseLookup :
      (retainedDrawingPlanarSATFormula
        formula)[clauseIndex]? = some clause :=
    (List.mk_mem_zipIdx_iff_getElem?
      (l := retainedDrawingPlanarSATFormula formula)
      (x := clause) (i := clauseIndex)).mp clauseMember
  have projectedLookup :
      ((retainedDrawingPlanarSATClauseMetadata formula).map
          DrawingPlanarSATClauseMetadata.clause)[
            clauseIndex]? = some clause := by
    simpa using clauseLookup
  rw [List.getElem?_map] at projectedLookup
  simpa only [Option.map_eq_some_iff] using projectedLookup

/-- A retained clause lookup also returns its source-membership and
local-index certificate. -/
theorem retainedDrawingPlanarSATClauseMetadata_lookup_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingPlanarSATFormula formula).zipIdx) :
    ∃ metadata,
      (retainedDrawingPlanarSATClauseMetadata
          formula)[clauseIndex]? = some metadata ∧
        metadata.clause = clause ∧
          metadata.RetainedValid formula := by
  rcases retainedDrawingPlanarSATClauseMetadata_lookup
      formula clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  have metadataIndexLt :
      clauseIndex <
        (retainedDrawingPlanarSATClauseMetadata formula).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (retainedDrawingPlanarSATClauseMetadata formula)[clauseIndex] =
        metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember :
      metadata ∈ retainedDrawingPlanarSATClauseMetadata formula := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  exact
    ⟨metadata, metadataLookup, clauseEqual,
      retainedDrawingPlanarSATClauseMetadata_valid
        formula metadataMember⟩

end PeriodicOrthocrossing
end LeanTrominoes
