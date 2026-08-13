/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossoverIncidenceDrawing
import LeanTrominoes.PeriodicOrthocrossingWireIncidenceDrawings
import LeanTrominoes.PeriodicOrthocrossingRoutedClauseIncidenceDrawing
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableIncidenceDrawing
import LeanTrominoes.PeriodicCNFPlanarSATIncidenceRoutes

/-!
# Metadata-selected planar-SAT incidence drawings

Every clause of the finite planar-SAT block carries metadata identifying the
local geometric component that produced it.  This file turns that metadata
into a total incidence-route selector.  Crossovers, straight carrier lenses,
route-bend corners, and active variable arms use their certified local
drawings.  A routed source clause uses its direct terminal rays, which retain
the cyclic order needed by the later occurrence split.  Every one of these
selected drawings is continuously planar.

The main result proves that every selected local route has the endpoints of
the corresponding global incidence.  Consequently the existing
periodicization, wrapping, deduplication, and anchor-normalization transport
applies to this component-aware route family without any new index proof.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- The geometric component underlying a clause source, forgetting only the
component's local clause index and enumeration bookkeeping. -/
inductive DrawingPlanarSATComponent
    (Variable : Type*)
  | crossover (crossing : CrossingRecord)
  | carrier (link : EqualityLink CarrierNode)
  | bend (routeBend : RouteBend)
  | routedClause (site : ClauseRouteSite)
  | routedVariable
      (site : VariableRouteSite Variable)
      (arm : DuplicatorArm)
      (link : EqualityLink (PlanarSATNode Variable))
  deriving DecidableEq

namespace DrawingPlanarSATClauseSource

/-- Forget a clause source's local index while retaining its complete local
geometric drawing. -/
def component {Variable : Type*} :
    DrawingPlanarSATClauseSource Variable →
      DrawingPlanarSATComponent Variable
  | .crossover crossing _ => .crossover crossing
  | .carrier link _ => .carrier link
  | .bend routeBend _ => .bend routeBend
  | .routedClause site => .routedClause site
  | .routedVariable site _ arm link _ =>
      .routedVariable site arm link

/-- The clause index inside the local drawing selected by one source. -/
def localClauseIndex {Variable : Type*} :
    DrawingPlanarSATClauseSource Variable → Nat
  | .crossover _ localClauseIndex => localClauseIndex
  | .carrier _ localClauseIndex => localClauseIndex
  | .bend _ localClauseIndex => localClauseIndex
  | .routedClause _ => 0
  | .routedVariable _ _ _ _ localClauseIndex => localClauseIndex

/-- Select the positioned local incidence drawing that produced a global
planar-SAT clause. -/
def incidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    DrawingPlanarSATClauseSource Variable →
      EmbeddedCNFIncidenceDrawing (PlanarSATVariable Variable)
  | .crossover crossing _ =>
      drawingPlanarSATCrossoverIncidenceDrawing formula crossing
  | .carrier link _ =>
      drawingPlanarSATCarrierLensIncidenceDrawing formula link
  | .bend routeBend _ =>
      drawingPlanarSATBendCornerIncidenceDrawing formula routeBend
  | .routedClause site =>
      drawingPlanarSATRoutedClauseIncidenceDrawing formula site
  | .routedVariable site _ arm link _ =>
      drawingPlanarSATRoutedVariableIncidenceDrawing
        formula site arm link

/-- Sources naming the same geometric component select the same complete
local drawing, even when their local clause indices differ. -/
theorem incidenceDrawing_eq_of_component_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (first second : DrawingPlanarSATClauseSource Variable)
    (sameComponent : first.component = second.component) :
    first.incidenceDrawing formula =
      second.incidenceDrawing formula := by
  cases first <;> cases second <;>
    simp_all [component, incidenceDrawing]

/-- Every selected local drawing uses the common final planar-SAT variable
placement. -/
@[simp] theorem incidenceDrawing_variablePosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable) :
    (source.incidenceDrawing formula).variablePosition =
      drawingPlanarSATVariablePosition formula := by
  cases source <;> rfl

end DrawingPlanarSATClauseSource

namespace DrawingPlanarSATClauseMetadata

/-- Valid source metadata places the advertised global clause at the
advertised local index of its selected drawing. -/
theorem localClauseMember
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.Valid formula) :
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
          drawingPlanarSATCarrierLensIncidenceDrawing_formula
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

/-- Every valid metadata-selected drawing has exact incidence endpoints. -/
theorem localDrawingRoutesMatch
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.Valid formula) :
    (metadata.source.incidenceDrawing formula).RoutesMatch := by
  cases metadata with
  | mk clause source =>
    cases source with
    | crossover crossing localClauseIndex =>
        exact drawingPlanarSATCrossoverIncidenceDrawing_routesMatch
          formula crossing
    | carrier link localClauseIndex =>
        exact (drawingPlanarSATCarrierLensIncidenceDrawing_isValid
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

/-- Every valid metadata-selected local component is continuously planar. -/
theorem localDrawingIsPlanar
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.Valid formula) :
    (metadata.source.incidenceDrawing formula).IsPlanar := by
  cases metadata with
  | mk clause source =>
    cases source with
    | crossover crossing localClauseIndex =>
        exact drawingPlanarSATCrossoverIncidenceDrawing_isPlanar
          formula crossing
    | carrier link localClauseIndex =>
        exact (drawingPlanarSATCarrierLensIncidenceDrawing_isValid
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

end DrawingPlanarSATClauseMetadata

/-- Total finite route family obtained by looking up each global clause's
source metadata and then using its certified local drawing. -/
def drawingPlanarSATLocalIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match (drawingPlanarSATClauseMetadata formula)[clauseIndex]? with
    | none => []
    | some metadata =>
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex literalIndex

/-- Every genuine route selected from local component metadata has the
advertised global clause and variable endpoints. -/
theorem drawingPlanarSATLocalIncidenceRoutes_physicalRoutesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    DrawingPlanarSATPhysicalIncidenceRoutesMatch
      formula (drawingPlanarSATLocalIncidenceRoutes formula) := by
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  rcases drawingPlanarSATClauseMetadata_lookup_valid
      formula clauseMember with
    ⟨metadata, metadataLookup, clauseEqual, valid⟩
  subst clause
  have localClauseMember :=
    metadata.localClauseMember
      wellFormed degree isLocal valid
  have localRoutesMatch :=
    metadata.localDrawingRoutesMatch
      wellFormed degree isLocal valid
  have endpoints :=
    (metadata.source.incidenceDrawing formula).physicalRoutesMatch
      localRoutesMatch metadata.clause
      metadata.source.localClauseIndex localClauseMember
      literal literalIndex literalMember
  simpa [drawingPlanarSATLocalIncidenceRoutes,
    metadataLookup] using endpoints

/-- The metadata-selected family transported through periodicization,
wrapping, deduplication, and anchor normalization. -/
def deduplicatedWrappedDrawingPeriodicPlanarSATLocalIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  deduplicatedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
    formula (drawingPlanarSATLocalIncidenceRoutes formula)

/-- The transported metadata-selected routes satisfy the complete periodic
incidence endpoint condition. -/
theorem
    deduplicatedWrappedDrawingPeriodicPlanarSATLocalIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (PositionedPeriodicCNF.incidenceDrawing
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula formula)
      (wrappedDrawingPeriodicPlanarSATPlacement formula)
      (deduplicatedWrappedDrawingPeriodicPlanarSATLocalIncidenceRoutes
        formula)).RoutesMatch
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase.incidenceGraph := by
  exact
    deduplicatedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesMatch
      formula (drawingPlanarSATLocalIncidenceRoutes formula)
      (drawingPlanarSATLocalIncidenceRoutes_physicalRoutesMatch
        formula wellFormed degree isLocal)

end PeriodicOrthocrossing
end LeanTrominoes
