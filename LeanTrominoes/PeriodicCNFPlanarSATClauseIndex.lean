/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarFormula
import LeanTrominoes.PeriodicCNFPlanarOccurrences

/-!
# Indexing the finite planar-SAT clause families

The finite planarized SAT formula concatenates five geometrically distinct
clause families.  Later incidence-route definitions must recover the exact
local drawing component and local clause index from a clause's global index.

This module stores that information in a parallel metadata list.  Bend
metadata retains the original `RouteBend`, and variable-gadget metadata
retains its lifted vertex site, so no geometric witness is lost when the
component formulas are flattened.  Projecting the clauses recovers
`drawingPlanarSATFormula` exactly.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- One crossover site's clauses after embedding into the combined planar-SAT
variable type. -/
def drawingPlanarSATCrossoverFormulaAt
    {Variable : Type*}
    (crossing : CrossingRecord) :
    List (EmbeddedClause (PlanarSATVariable Variable)) :=
  (scopedCrossoverInstance crossing
    (carrierNodeCrossingPorts crossing)
    (crossingMacroOrigin crossing) 1).map fun clause =>
      clause.rename (@planarSATCoreVariableMap Variable)

/-- One complete-carrier equality link after embedding into the combined
planar-SAT variable type. -/
def drawingPlanarSATCarrierFormulaAt
    {Variable : Type*}
    (link : EqualityLink CarrierNode) :
    List (EmbeddedClause (PlanarSATVariable Variable)) :=
  (equalityInstance link.first link.second link.positions).map
    fun clause =>
      (clause.rename fun node =>
        (Sum.inl node :
          Sum CarrierNode
            (CrossingRecord × CrossoverInternal))).rename
        (@planarSATCoreVariableMap Variable)

/-- One route bend's equality clauses after embedding into the combined
planar-SAT variable type. -/
def drawingPlanarSATBendFormulaAt
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (routeBend : RouteBend) :
    List (EmbeddedClause (PlanarSATVariable Variable)) :=
  drawingPlanarSATCarrierFormulaAt
    (routeBend.equalityLink graph)

/-- One active routed-variable equality arm after embedding into the combined
planar-SAT variable type. -/
def drawingPlanarSATRoutedVariableFormulaAt
    {Variable : Type*}
    (link : EqualityLink (PlanarSATNode Variable)) :
    List (EmbeddedClause (PlanarSATVariable Variable)) :=
  (equalityInstance link.first link.second link.positions).map
    fun clause =>
      clause.rename planarSATExternalVariableMap

/-- The five geometric sources of clauses in `drawingPlanarSATFormula`.
Constructors retain every witness needed to recover the local drawing. -/
inductive DrawingPlanarSATClauseSource
    (Variable : Type*)
  | crossover (crossing : CrossingRecord) (localClauseIndex : Nat)
  | carrier
      (link : EqualityLink CarrierNode) (localClauseIndex : Nat)
  | bend
      (routeBend : RouteBend) (localClauseIndex : Nat)
  | routedClause (site : ClauseRouteSite)
  | routedVariable
      (site : VariableRouteSite Variable)
      (armIndex : Nat)
      (arm : DuplicatorArm)
      (link : EqualityLink (PlanarSATNode Variable))
      (localClauseIndex : Nat)

/-- A global planar-SAT clause paired with its exact local geometric source. -/
structure DrawingPlanarSATClauseMetadata
    (Variable : Type*) where
  clause : EmbeddedClause (PlanarSATVariable Variable)
  source : DrawingPlanarSATClauseSource Variable

/-- The source component occurs in the finite drawing family, and the stored
clause occurs at the source's recorded local index. -/
def DrawingPlanarSATClauseMetadata.Valid
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
      link ∈ drawingCompleteCarrierLinks graph ∧
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
        (link, armIndex) ∈ (routedVariableLinksAt formula site).zipIdx ∧
          arm = link.first.duplicatorArm ∧
          (metadata.clause, localClauseIndex) ∈
            (drawingPlanarSATRoutedVariableFormulaAt link).zipIdx

def drawingPlanarSATCrossoverClauseMetadataFor
    {Variable : Type*}
    (crossing : CrossingRecord) :
    List (DrawingPlanarSATClauseMetadata Variable) :=
  (drawingPlanarSATCrossoverFormulaAt
    (Variable := Variable) crossing).zipIdx.map
    fun tagged =>
      ⟨tagged.1, .crossover crossing tagged.2⟩

def drawingPlanarSATCrossoverClauseMetadata
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (DrawingPlanarSATClauseMetadata Variable) :=
  (orientedCrossingHalo graph).flatMap
    drawingPlanarSATCrossoverClauseMetadataFor

@[simp] theorem drawingPlanarSATCrossoverClauseMetadataFor_clauses
    {Variable : Type*}
    (crossing : CrossingRecord) :
    (drawingPlanarSATCrossoverClauseMetadataFor
      (Variable := Variable) crossing).map
        DrawingPlanarSATClauseMetadata.clause =
      drawingPlanarSATCrossoverFormulaAt
        (Variable := Variable) crossing := by
  simp [drawingPlanarSATCrossoverClauseMetadataFor, List.map_map,
    Function.comp_def]

@[simp] theorem drawingPlanarSATCrossoverClauseMetadata_clauses
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (drawingPlanarSATCrossoverClauseMetadata
      (Variable := Variable) graph).map
        DrawingPlanarSATClauseMetadata.clause =
      (drawingCarrierNodeCrossoverFormula graph).map fun clause =>
        clause.rename (@planarSATCoreVariableMap Variable) := by
  simp [drawingPlanarSATCrossoverClauseMetadata,
    drawingPlanarSATCrossoverFormulaAt,
    drawingCarrierNodeCrossoverFormula, crossoverFamily,
    List.map_flatMap]

theorem drawingPlanarSATCrossoverClauseMetadataFor_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord)
    (crossingMember :
      crossing ∈
        orientedCrossingHalo
          (PeriodicCNF.incidenceGraph formula))
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        drawingPlanarSATCrossoverClauseMetadataFor
          (Variable := Variable) crossing) :
    metadata.Valid formula := by
  rw [drawingPlanarSATCrossoverClauseMetadataFor] at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember, metadataEqual⟩
  subst metadata
  change crossing ∈
      orientedCrossingHalo
        (PeriodicCNF.incidenceGraph formula) ∧
    taggedClause ∈
      (drawingPlanarSATCrossoverFormulaAt
        (Variable := Variable) crossing).zipIdx
  exact ⟨crossingMember, taggedClauseMember⟩

theorem drawingPlanarSATCrossoverClauseMetadata_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        drawingPlanarSATCrossoverClauseMetadata
          (Variable := Variable)
          (PeriodicCNF.incidenceGraph formula)) :
    metadata.Valid formula := by
  rcases List.mem_flatMap.mp metadataMember with
    ⟨crossing, crossingMember, metadataMember⟩
  exact drawingPlanarSATCrossoverClauseMetadataFor_valid
    formula crossing crossingMember metadataMember

def drawingPlanarSATCarrierClauseMetadataFor
    {Variable : Type*}
    (link : EqualityLink CarrierNode) :
    List (DrawingPlanarSATClauseMetadata Variable) :=
  (drawingPlanarSATCarrierFormulaAt
    (Variable := Variable) link).zipIdx.map
    fun tagged => ⟨tagged.1, .carrier link tagged.2⟩

def drawingPlanarSATCarrierClauseMetadata
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (DrawingPlanarSATClauseMetadata Variable) :=
  (drawingCompleteCarrierLinks graph).flatMap
    drawingPlanarSATCarrierClauseMetadataFor

@[simp] theorem drawingPlanarSATCarrierClauseMetadata_clauses
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (drawingPlanarSATCarrierClauseMetadata
      (Variable := Variable) graph).map
        DrawingPlanarSATClauseMetadata.clause =
      (drawingCompleteCarrierFormula graph).map fun clause =>
        (clause.rename fun node =>
          (Sum.inl node :
            Sum CarrierNode
              (CrossingRecord × CrossoverInternal))).rename
          (@planarSATCoreVariableMap Variable) := by
  simp [drawingPlanarSATCarrierClauseMetadata, drawingPlanarSATCarrierClauseMetadataFor,
    drawingPlanarSATCarrierFormulaAt,
    drawingCompleteCarrierFormula, equalityFamily,
    List.map_flatMap, List.map_map, Function.comp_def]

theorem drawingPlanarSATCarrierClauseMetadataFor_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (linkMember :
      link ∈
        drawingCompleteCarrierLinks
          (PeriodicCNF.incidenceGraph formula))
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        drawingPlanarSATCarrierClauseMetadataFor
          (Variable := Variable) link) :
    metadata.Valid formula := by
  rw [drawingPlanarSATCarrierClauseMetadataFor] at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember, metadataEqual⟩
  subst metadata
  simpa [DrawingPlanarSATClauseMetadata.Valid] using
    And.intro linkMember taggedClauseMember

theorem drawingPlanarSATCarrierClauseMetadata_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        drawingPlanarSATCarrierClauseMetadata
          (Variable := Variable)
          (PeriodicCNF.incidenceGraph formula)) :
    metadata.Valid formula := by
  rcases List.mem_flatMap.mp metadataMember with
    ⟨link, linkMember, metadataMember⟩
  exact drawingPlanarSATCarrierClauseMetadataFor_valid
    formula link linkMember metadataMember

def drawingPlanarSATBendClauseMetadataFor
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (routeBend : RouteBend) :
    List (DrawingPlanarSATClauseMetadata Variable) :=
  (drawingPlanarSATBendFormulaAt
    (Variable := Variable) graph routeBend).zipIdx.map
    fun tagged => ⟨tagged.1, .bend routeBend tagged.2⟩

def drawingPlanarSATBendClauseMetadata
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (DrawingPlanarSATClauseMetadata Variable) :=
  (drawingRouteBends graph).dedup.flatMap
    (drawingPlanarSATBendClauseMetadataFor graph)

@[simp] theorem drawingPlanarSATBendClauseMetadata_clauses
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (drawingPlanarSATBendClauseMetadata
      (Variable := Variable) graph).map
        DrawingPlanarSATClauseMetadata.clause =
      (drawingRouteBendFormula graph).map fun clause =>
        (clause.rename fun node =>
          (Sum.inl node :
            Sum CarrierNode
              (CrossingRecord × CrossoverInternal))).rename
          (@planarSATCoreVariableMap Variable) := by
  simp [drawingPlanarSATBendClauseMetadata, drawingPlanarSATBendClauseMetadataFor,
    drawingPlanarSATBendFormulaAt,
    drawingPlanarSATCarrierFormulaAt,
    drawingRouteBendFormula, drawingRouteBendLinks,
    equalityFamily,
    List.map_flatMap, List.map_map, Function.comp_def]
  rw [List.flatMap_map]

theorem drawingPlanarSATBendClauseMetadataFor_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeBend : RouteBend)
    (routeBendMember :
      routeBend ∈
        (drawingRouteBends
          (PeriodicCNF.incidenceGraph formula)).dedup)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        drawingPlanarSATBendClauseMetadataFor
          (Variable := Variable)
          (PeriodicCNF.incidenceGraph formula)
          routeBend) :
    metadata.Valid formula := by
  rw [drawingPlanarSATBendClauseMetadataFor] at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember, metadataEqual⟩
  subst metadata
  simpa [DrawingPlanarSATClauseMetadata.Valid] using
    And.intro routeBendMember taggedClauseMember

theorem drawingPlanarSATBendClauseMetadata_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        drawingPlanarSATBendClauseMetadata
          (Variable := Variable)
          (PeriodicCNF.incidenceGraph formula)) :
    metadata.Valid formula := by
  rcases List.mem_flatMap.mp metadataMember with
    ⟨routeBend, routeBendMember, metadataMember⟩
  exact drawingPlanarSATBendClauseMetadataFor_valid
    formula routeBend routeBendMember metadataMember

def drawingPlanarSATRoutedClauseMetadata
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (DrawingPlanarSATClauseMetadata Variable) :=
  (drawingClauseRouteSites formula).map fun site =>
    ⟨(routedClauseAt formula site).rename
      planarSATExternalVariableMap, .routedClause site⟩

@[simp] theorem drawingPlanarSATRoutedClauseMetadata_clauses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPlanarSATRoutedClauseMetadata formula).map
        DrawingPlanarSATClauseMetadata.clause =
      scopedDrawingRoutedClauseFormula formula := by
  simp [drawingPlanarSATRoutedClauseMetadata,
    scopedDrawingRoutedClauseFormula,
    drawingRoutedClauseFormula, List.map_map,
    Function.comp_def]

theorem drawingPlanarSATRoutedClauseMetadata_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈ drawingPlanarSATRoutedClauseMetadata formula) :
    metadata.Valid formula := by
  rw [drawingPlanarSATRoutedClauseMetadata] at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨site, siteMember, metadataEqual⟩
  subst metadata
  exact ⟨siteMember, rfl⟩

def drawingPlanarSATRoutedVariableClauseMetadataFor
    {Variable : Type*}
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    List (DrawingPlanarSATClauseMetadata Variable) :=
  (drawingPlanarSATRoutedVariableFormulaAt link).zipIdx.map
    fun tagged =>
      ⟨tagged.1,
        .routedVariable site armIndex arm link tagged.2⟩

def drawingPlanarSATRoutedVariableClauseMetadata
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (DrawingPlanarSATClauseMetadata Variable) :=
  (drawingVariableRouteSites formula).flatMap fun site =>
    (routedVariableLinksAt formula site).zipIdx.flatMap fun taggedLink =>
      drawingPlanarSATRoutedVariableClauseMetadataFor
        site taggedLink.2 taggedLink.1.first.duplicatorArm
          taggedLink.1

@[simp] theorem drawingPlanarSATRoutedVariableClauseMetadata_clauses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPlanarSATRoutedVariableClauseMetadata formula).map
        DrawingPlanarSATClauseMetadata.clause =
      scopedDrawingRoutedVariableFormula formula := by
  rw [scopedDrawingRoutedVariableFormula,
    drawingRoutedVariableFormula_eq_equalityFamily]
  simp [drawingPlanarSATRoutedVariableClauseMetadata,
    drawingPlanarSATRoutedVariableClauseMetadataFor,
    drawingPlanarSATRoutedVariableFormulaAt,
    drawingRoutedVariableLinks,
    equalityFamily, List.map_flatMap, List.map_map,
    Function.comp_def]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro site _siteMember
  exact PeriodicCNF.zipIdx_flatMap_fst
    (fun link : EqualityLink (PlanarSATNode Variable) =>
      (equalityInstance link.first link.second link.positions).map
        fun clause => clause.rename planarSATExternalVariableMap)
    (routedVariableLinksAt formula site) 0

theorem drawingPlanarSATRoutedVariableClauseMetadataFor_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (siteMember :
      site ∈ drawingVariableRouteSites formula)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (linkMember :
      (link, armIndex) ∈
        (routedVariableLinksAt formula site).zipIdx)
    (armEq : arm = link.first.duplicatorArm)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        drawingPlanarSATRoutedVariableClauseMetadataFor
          site armIndex arm link) :
    metadata.Valid formula := by
  rw [drawingPlanarSATRoutedVariableClauseMetadataFor] at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember, metadataEqual⟩
  subst metadata
  simpa [DrawingPlanarSATClauseMetadata.Valid] using
    And.intro siteMember
      (And.intro linkMember
        (And.intro armEq taggedClauseMember))

theorem drawingPlanarSATRoutedVariableClauseMetadata_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈ drawingPlanarSATRoutedVariableClauseMetadata formula) :
    metadata.Valid formula := by
  rcases List.mem_flatMap.mp metadataMember with
    ⟨site, siteMember, metadataMember⟩
  rcases List.mem_flatMap.mp metadataMember with
    ⟨taggedLink, linkMember, metadataMember⟩
  exact drawingPlanarSATRoutedVariableClauseMetadataFor_valid
    formula site siteMember taggedLink.2
      taggedLink.1.first.duplicatorArm taggedLink.1
      linkMember rfl metadataMember

/-- Clause metadata parallel to the five concatenated geometric families of
`drawingPlanarSATFormula`. -/
def drawingPlanarSATClauseMetadata
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (DrawingPlanarSATClauseMetadata Variable) :=
  let graph := PeriodicCNF.incidenceGraph formula
  drawingPlanarSATCrossoverClauseMetadata graph ++
    drawingPlanarSATCarrierClauseMetadata graph ++
      drawingPlanarSATBendClauseMetadata graph ++
        drawingPlanarSATRoutedClauseMetadata formula ++
          drawingPlanarSATRoutedVariableClauseMetadata formula

/-- Forgetting all source witnesses recovers `drawingPlanarSATFormula`
exactly, including its global clause order. -/
@[simp] theorem drawingPlanarSATClauseMetadata_clauses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPlanarSATClauseMetadata formula).map
        DrawingPlanarSATClauseMetadata.clause =
      drawingPlanarSATFormula formula := by
  simp [drawingPlanarSATClauseMetadata,
    drawingPlanarSATFormula, scopedDrawingPlanarSATCore,
    drawingRoutePlanarCoreFormula, scopedDrawingRouteWireFormula,
    drawingRouteWireFormula, List.map_append,
    List.map_map, Function.comp_def]

/-- Every entry of the global metadata list has a genuine finite-family source
and a genuine local clause index. -/
theorem drawingPlanarSATClauseMetadata_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {metadata : DrawingPlanarSATClauseMetadata Variable}
    (metadataMember :
      metadata ∈ drawingPlanarSATClauseMetadata formula) :
    metadata.Valid formula := by
  let graph := PeriodicCNF.incidenceGraph formula
  by_cases crossoverMember :
      metadata ∈
        drawingPlanarSATCrossoverClauseMetadata
          (Variable := Variable) graph
  · exact drawingPlanarSATCrossoverClauseMetadata_valid formula crossoverMember
  by_cases carrierMember :
      metadata ∈
        drawingPlanarSATCarrierClauseMetadata
          (Variable := Variable) graph
  · exact drawingPlanarSATCarrierClauseMetadata_valid formula carrierMember
  by_cases bendMember :
      metadata ∈
        drawingPlanarSATBendClauseMetadata
          (Variable := Variable) graph
  · exact drawingPlanarSATBendClauseMetadata_valid formula bendMember
  by_cases routedClauseMember :
      metadata ∈ drawingPlanarSATRoutedClauseMetadata formula
  · exact drawingPlanarSATRoutedClauseMetadata_valid
      formula routedClauseMember
  apply drawingPlanarSATRoutedVariableClauseMetadata_valid formula
  simpa [drawingPlanarSATClauseMetadata, graph,
    crossoverMember, carrierMember, bendMember,
    routedClauseMember] using metadataMember

/-- Looking up a genuine global clause occurrence returns metadata carrying
that exact clause. -/
theorem drawingPlanarSATClauseMetadata_lookup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATFormula formula).zipIdx) :
    ∃ metadata,
      (drawingPlanarSATClauseMetadata
          formula)[clauseIndex]? = some metadata ∧
        metadata.clause = clause := by
  have clauseLookup :
      (drawingPlanarSATFormula
        formula)[clauseIndex]? = some clause :=
    (List.mk_mem_zipIdx_iff_getElem?
      (l := drawingPlanarSATFormula formula)
      (x := clause) (i := clauseIndex)).mp clauseMember
  have projectedLookup :
      ((drawingPlanarSATClauseMetadata formula).map
          DrawingPlanarSATClauseMetadata.clause)[
            clauseIndex]? = some clause := by
    simpa using clauseLookup
  rw [List.getElem?_map] at projectedLookup
  simpa only [Option.map_eq_some_iff] using
    projectedLookup

/-- A genuine global clause lookup also returns the source-membership and
local-index certificate needed to select its local incidence drawing. -/
theorem drawingPlanarSATClauseMetadata_lookup_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATFormula formula).zipIdx) :
    ∃ metadata,
      (drawingPlanarSATClauseMetadata
          formula)[clauseIndex]? = some metadata ∧
        metadata.clause = clause ∧
          metadata.Valid formula := by
  rcases drawingPlanarSATClauseMetadata_lookup
      formula clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  have metadataIndexLt :
      clauseIndex <
        (drawingPlanarSATClauseMetadata formula).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (drawingPlanarSATClauseMetadata formula)[clauseIndex] =
        metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember :
      metadata ∈
        drawingPlanarSATClauseMetadata formula := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  exact
    ⟨metadata, metadataLookup, clauseEqual,
      drawingPlanarSATClauseMetadata_valid
        formula metadataMember⟩

end PeriodicOrthocrossing
end LeanTrominoes
