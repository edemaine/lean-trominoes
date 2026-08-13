/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedSATClauseIndex
import LeanTrominoes.PeriodicOrthocrossingPlanarSATLocalIncidenceDrawings
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierWireIncidenceDrawings

/-!
# Local incidence drawing for the retained planar SAT formula

Every retained metadata source selects the same certified local component
drawing as its canonical counterpart.  The carrier case uses the retained
lens validity theorem; all other cases are unchanged.  Looking up those
sources yields a complete finite incidence drawing with exact endpoints,
orthogonal routes, simple routes, and local component planarity.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

namespace DrawingPlanarSATClauseMetadata

/-- Retained-valid metadata places its clause at the advertised local index
of the selected component drawing. -/
theorem retainedLocalClauseMember
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula) :
    (metadata.clause, metadata.source.localClauseIndex) ∈
      (metadata.source.incidenceDrawing formula).formula.zipIdx := by
  cases metadata with
  | mk clause source =>
    cases source with
    | crossover crossing localClauseIndex =>
        simpa [DrawingPlanarSATClauseSource.localClauseIndex,
          DrawingPlanarSATClauseSource.incidenceDrawing] using valid.2
    | carrier link localClauseIndex =>
        rw [DrawingPlanarSATClauseSource.incidenceDrawing,
          retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
            wellFormed degree isLocal valid.1]
        exact valid.2
    | bend routeBend localClauseIndex =>
        rw [DrawingPlanarSATClauseSource.incidenceDrawing,
          drawingPlanarSATBendCornerIncidenceDrawing_formula]
        exact valid.2
    | routedClause site =>
        rw [DrawingPlanarSATClauseSource.incidenceDrawing,
          drawingPlanarSATRoutedClauseIncidenceDrawing_formula]
        rw [valid.2]
        simp [DrawingPlanarSATClauseSource.localClauseIndex]
    | routedVariable site armIndex arm link localClauseIndex =>
        have linkMember :
            link ∈ routedVariableLinksAt formula site :=
          List.fst_mem_of_mem_zipIdx valid.2.1
        rw [DrawingPlanarSATClauseSource.incidenceDrawing,
          drawingPlanarSATRoutedVariableIncidenceDrawing_formula
            formula site arm link linkMember valid.2.2.1]
        exact valid.2.2.2

/-- Every retained-valid selected component drawing has exact incidence
endpoints. -/
theorem retainedLocalDrawingRoutesMatch
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula) :
    (metadata.source.incidenceDrawing formula).RoutesMatch := by
  cases metadata with
  | mk clause source =>
    cases source with
    | crossover crossing localClauseIndex =>
        exact drawingPlanarSATCrossoverIncidenceDrawing_routesMatch
          formula crossing
    | carrier link localClauseIndex =>
        exact
          (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_isValid
            wellFormed degree isLocal valid.1).1
    | bend routeBend localClauseIndex =>
        exact (drawingPlanarSATBendCornerIncidenceDrawing_isValid
          wellFormed degree isLocal valid.1).1
    | routedClause site =>
        exact
          drawingPlanarSATRoutedClauseIncidenceDrawing_routesMatch
            formula wellFormed site
    | routedVariable site armIndex arm link localClauseIndex =>
        exact
          drawingPlanarSATRoutedVariableIncidenceDrawing_routesMatch
            formula wellFormed site arm
            (List.fst_mem_of_mem_zipIdx valid.2.1)
            valid.2.2.1

/-- Every retained-valid selected local component is continuously planar. -/
theorem retainedLocalDrawingIsPlanar
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula) :
    (metadata.source.incidenceDrawing formula).IsPlanar := by
  cases metadata with
  | mk clause source =>
    cases source with
    | crossover crossing localClauseIndex =>
        exact drawingPlanarSATCrossoverIncidenceDrawing_isPlanar
          formula crossing
    | carrier link localClauseIndex =>
        exact
          (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_isValid
            wellFormed degree isLocal valid.1).2.2
    | bend routeBend localClauseIndex =>
        exact (drawingPlanarSATBendCornerIncidenceDrawing_isValid
          wellFormed degree isLocal valid.1).2.2
    | routedClause site =>
        exact
          drawingPlanarSATRoutedClauseIncidenceDrawing_isPlanar
            formula wellFormed degree site
    | routedVariable site armIndex arm link localClauseIndex =>
        exact
          drawingPlanarSATRoutedVariableIncidenceDrawing_isPlanar
            formula wellFormed site arm
            (List.fst_mem_of_mem_zipIdx valid.2.1)
            valid.2.2.1

/-- Any genuine route of a retained-valid local component is simple. -/
theorem retainedLocalRouteIsSimple
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      ((metadata.source.incidenceDrawing formula).routes
        metadata.source.localClauseIndex literalIndex) := by
  apply
    (metadata.source.incidenceDrawing formula)
      |>.embeddedRoute_isSimple_of_members
        (metadata.retainedLocalDrawingIsPlanar
          wellFormed degree isLocal valid)
        (metadata.retainedLocalClauseMember
          wellFormed degree isLocal valid)
        literalMember

/-- Distinct incidences from one retained-valid component inherit that local
drawing's continuous separation. -/
theorem retainedLocalRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (sameComponent :
      first.source.component = second.source.component)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        first.clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        second.clause.literals.zipIdx)
    (different :
      first.source.localClauseIndex ≠
          second.source.localClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((first.source.incidenceDrawing formula).routes
        first.source.localClauseIndex firstLiteralIndex)
      ((second.source.incidenceDrawing formula).routes
        second.source.localClauseIndex secondLiteralIndex) := by
  have sameDrawing :
      first.source.incidenceDrawing formula =
        second.source.incidenceDrawing formula :=
    first.source.incidenceDrawing_eq_of_component_eq
      formula second.source sameComponent
  have secondClauseMember :=
    second.retainedLocalClauseMember
      wellFormed degree isLocal secondValid
  rw [← sameDrawing] at secondClauseMember ⊢
  apply
    (first.source.incidenceDrawing formula)
      |>.embeddedRoutes_avoidEachOther_of_members
        (first.retainedLocalDrawingIsPlanar
          wellFormed degree isLocal firstValid)
        (first.retainedLocalClauseMember
          wellFormed degree isLocal firstValid)
        secondClauseMember
        firstLiteralMember secondLiteralMember different

end DrawingPlanarSATClauseMetadata

/-- Total route family selected from retained clause metadata. -/
def retainedDrawingPlanarSATLocalIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match
        (retainedDrawingPlanarSATClauseMetadata
          formula)[clauseIndex]? with
    | none => []
    | some metadata =>
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex literalIndex

/-- Physical endpoint predicate for the retained finite formula. -/
def RetainedDrawingPlanarSATPhysicalIncidenceRoutesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : Prop :=
  EmbeddedPhysicalIncidenceRoutesMatch
    (retainedDrawingPlanarSATFormula formula)
    (drawingPlanarSATVariablePosition formula) routes

/-- Every retained metadata-selected route has its advertised physical
clause and variable endpoints. -/
theorem retainedDrawingPlanarSATLocalIncidenceRoutes_physicalRoutesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    RetainedDrawingPlanarSATPhysicalIncidenceRoutesMatch
      formula
      (retainedDrawingPlanarSATLocalIncidenceRoutes formula) := by
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  rcases retainedDrawingPlanarSATClauseMetadata_lookup_valid
      formula clauseMember with
    ⟨metadata, metadataLookup, clauseEqual, valid⟩
  subst clause
  have localClauseMember :=
    metadata.retainedLocalClauseMember
      wellFormed degree isLocal valid
  have localRoutesMatch :=
    metadata.retainedLocalDrawingRoutesMatch
      wellFormed degree isLocal valid
  have endpoints :=
    (metadata.source.incidenceDrawing formula).physicalRoutesMatch
      localRoutesMatch metadata.clause
      metadata.source.localClauseIndex localClauseMember
      literal literalIndex literalMember
  simpa [retainedDrawingPlanarSATLocalIncidenceRoutes,
    metadataLookup] using endpoints

/-- The complete retained finite formula equipped with its metadata-selected
local incidence routes. -/
irreducible_def retainedDrawingPlanarSATLocalIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    EmbeddedCNFIncidenceDrawing (PlanarSATVariable Variable) where
  formula := retainedDrawingPlanarSATFormula formula
  variablePosition := drawingPlanarSATVariablePosition formula
  routes := retainedDrawingPlanarSATLocalIncidenceRoutes formula

@[simp]
theorem retainedDrawingPlanarSATLocalIncidenceDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedDrawingPlanarSATLocalIncidenceDrawing formula).formula =
      retainedDrawingPlanarSATFormula formula := by
  rw [retainedDrawingPlanarSATLocalIncidenceDrawing]

@[simp]
theorem retainedDrawingPlanarSATLocalIncidenceDrawing_variablePosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedDrawingPlanarSATLocalIncidenceDrawing
      formula).variablePosition =
        drawingPlanarSATVariablePosition formula := by
  rw [retainedDrawingPlanarSATLocalIncidenceDrawing]

@[simp]
theorem retainedDrawingPlanarSATLocalIncidenceDrawing_routes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedDrawingPlanarSATLocalIncidenceDrawing formula).routes =
      retainedDrawingPlanarSATLocalIncidenceRoutes formula := by
  rw [retainedDrawingPlanarSATLocalIncidenceDrawing]

/-- The assembled retained finite drawing has exact incidence endpoints. -/
theorem retainedDrawingPlanarSATLocalIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (retainedDrawingPlanarSATLocalIncidenceDrawing formula).RoutesMatch := by
  apply EmbeddedCNFIncidenceDrawing.routesMatch_of_physical
  rw [retainedDrawingPlanarSATLocalIncidenceDrawing_formula,
    retainedDrawingPlanarSATLocalIncidenceDrawing_variablePosition,
    retainedDrawingPlanarSATLocalIncidenceDrawing_routes]
  exact retainedDrawingPlanarSATLocalIncidenceRoutes_physicalRoutesMatch
    formula wellFormed degree isLocal

end PeriodicOrthocrossing
end LeanTrominoes
