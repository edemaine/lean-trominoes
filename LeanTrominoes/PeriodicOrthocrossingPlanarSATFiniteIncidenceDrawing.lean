/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarSATLocalIncidenceDrawings
import LeanTrominoes.PeriodicOrthocrossingPlanarSATClauseKeyLookup
import LeanTrominoes.EmbeddedCNFIncidenceDrawingPlanarity

/-!
# The finite routed planar-SAT incidence drawing

The clause-source selector supplies one route for every literal occurrence
of the complete finite routed planar-SAT formula.  This file packages those
routes as a single `EmbeddedCNFIncidenceDrawing` and transfers the local
planarity certificates to every selected global route.

What remains for complete global planarity is isolated explicitly:
separation between routes selected from different local components, avoidance
of all global vertices, and distinctness of the assembled vertex positions.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- The complete finite routed planar-SAT formula equipped with the
metadata-selected local route family. -/
irreducible_def drawingPlanarSATLocalIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    EmbeddedCNFIncidenceDrawing (PlanarSATVariable Variable) where
  formula := drawingPlanarSATFormula formula
  variablePosition := drawingPlanarSATVariablePosition formula
  routes := drawingPlanarSATLocalIncidenceRoutes formula

@[simp] theorem drawingPlanarSATLocalIncidenceDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPlanarSATLocalIncidenceDrawing formula).formula =
      drawingPlanarSATFormula formula := by
  rw [drawingPlanarSATLocalIncidenceDrawing]

@[simp] theorem drawingPlanarSATLocalIncidenceDrawing_variablePosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPlanarSATLocalIncidenceDrawing formula).variablePosition =
      drawingPlanarSATVariablePosition formula := by
  rw [drawingPlanarSATLocalIncidenceDrawing]

@[simp] theorem drawingPlanarSATLocalIncidenceDrawing_routes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPlanarSATLocalIncidenceDrawing formula).routes =
      drawingPlanarSATLocalIncidenceRoutes formula := by
  rw [drawingPlanarSATLocalIncidenceDrawing]

/-- The geometric form of cross-component route separation.  Unlike the
global predicate below, this certificate speaks directly about two valid
metadata-selected local drawings, so its proof does not need to manipulate
global clause indices or metadata lookups. -/
def DrawingPlanarSATComponentRoutesSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Prop :=
  ∀ (firstMetadata secondMetadata :
      DrawingPlanarSATClauseMetadata Variable),
    firstMetadata.Valid formula →
      secondMetadata.Valid formula →
        ∀ {firstLiteral secondLiteral :
            PlanarSATVariable Variable × Bool}
          {firstLiteralIndex secondLiteralIndex : Nat},
          (firstLiteral, firstLiteralIndex) ∈
              firstMetadata.clause.literals.zipIdx →
            (secondLiteral, secondLiteralIndex) ∈
                secondMetadata.clause.literals.zipIdx →
              firstMetadata.source.component ≠
                  secondMetadata.source.component →
                EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
                  ((firstMetadata.source.incidenceDrawing formula).routes
                    firstMetadata.source.localClauseIndex
                    firstLiteralIndex)
                  ((secondMetadata.source.incidenceDrawing formula).routes
                    secondMetadata.source.localClauseIndex
                    secondLiteralIndex)

/-- The residual pairwise route obligation after local component planarity:
routes selected from genuinely different geometric components avoid one
another. -/
def DrawingPlanarSATCrossComponentRoutesSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Prop :=
  ∀ {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat},
    (firstClause, firstClauseIndex) ∈
        (drawingPlanarSATFormula formula).zipIdx →
      (secondClause, secondClauseIndex) ∈
        (drawingPlanarSATFormula formula).zipIdx →
      ∀ {firstLiteral secondLiteral :
          PlanarSATVariable Variable × Bool}
        {firstLiteralIndex secondLiteralIndex : Nat},
        (firstLiteral, firstLiteralIndex) ∈
            firstClause.literals.zipIdx →
          (secondLiteral, secondLiteralIndex) ∈
            secondClause.literals.zipIdx →
          ∀ {firstMetadata secondMetadata :
              DrawingPlanarSATClauseMetadata Variable},
            (drawingPlanarSATClauseMetadata
                formula)[firstClauseIndex]? =
              some firstMetadata →
            (drawingPlanarSATClauseMetadata
                formula)[secondClauseIndex]? =
              some secondMetadata →
            firstMetadata.source.component ≠
                secondMetadata.source.component →
            EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
              (drawingPlanarSATLocalIncidenceRoutes
                formula firstClauseIndex firstLiteralIndex)
              (drawingPlanarSATLocalIncidenceRoutes
                formula secondClauseIndex secondLiteralIndex)

/-- A geometric separation certificate for valid local components lifts to
the globally indexed route family selected by clause metadata. -/
theorem drawingPlanarSAT_crossComponentRoutesSeparated_of_components
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (componentsSeparated :
      DrawingPlanarSATComponentRoutesSeparated formula) :
    DrawingPlanarSATCrossComponentRoutesSeparated formula := by
  intro firstClause secondClause
    firstClauseIndex secondClauseIndex
    firstClauseMember secondClauseMember
    firstLiteral secondLiteral
    firstLiteralIndex secondLiteralIndex
    firstLiteralMember secondLiteralMember
    firstMetadata secondMetadata
    firstLookup secondLookup differentComponents
  rcases drawingPlanarSATClauseMetadata_lookup_valid
      formula firstClauseMember with
    ⟨firstMetadata', firstLookup', firstClauseEqual, firstValid⟩
  rcases drawingPlanarSATClauseMetadata_lookup_valid
      formula secondClauseMember with
    ⟨secondMetadata', secondLookup', secondClauseEqual, secondValid⟩
  have firstMetadataEqual :
      firstMetadata' = firstMetadata := by
    rw [firstLookup] at firstLookup'
    exact Option.some.inj firstLookup'.symm
  have secondMetadataEqual :
      secondMetadata' = secondMetadata := by
    rw [secondLookup] at secondLookup'
    exact Option.some.inj secondLookup'.symm
  subst firstMetadata'
  subst secondMetadata'
  have firstLocalLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstMetadata.clause.literals.zipIdx := by
    simpa [firstClauseEqual] using firstLiteralMember
  have secondLocalLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondMetadata.clause.literals.zipIdx := by
    simpa [secondClauseEqual] using secondLiteralMember
  have separated := componentsSeparated
    firstMetadata secondMetadata firstValid secondValid
    firstLocalLiteralMember secondLocalLiteralMember
    differentComponents
  simpa [drawingPlanarSATLocalIncidenceRoutes,
    firstLookup, secondLookup] using separated

/-- The assembled finite drawing has exact clause and variable endpoints. -/
theorem drawingPlanarSATLocalIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (drawingPlanarSATLocalIncidenceDrawing formula).RoutesMatch := by
  apply EmbeddedCNFIncidenceDrawing.routesMatch_of_physical
  rw [drawingPlanarSATLocalIncidenceDrawing_formula,
    drawingPlanarSATLocalIncidenceDrawing_variablePosition,
    drawingPlanarSATLocalIncidenceDrawing_routes]
  exact drawingPlanarSATLocalIncidenceRoutes_physicalRoutesMatch
    formula wellFormed degree isLocal

/-- A valid metadata entry transfers its selected local drawing's route
simplicity to any genuine literal of the advertised clause. -/
theorem DrawingPlanarSATClauseMetadata.localRouteIsSimple
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.Valid formula)
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
        (metadata.localDrawingIsPlanar
          wellFormed degree isLocal valid)
        (metadata.localClauseMember
          wellFormed degree isLocal valid)
        literalMember

/-- Two distinct local incidences selected from the same geometric component
inherit that component's continuous route separation, even when they belong
to different local clauses. -/
theorem DrawingPlanarSATClauseMetadata.localRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.Valid formula)
    (secondValid : second.Valid formula)
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
    second.localClauseMember
      wellFormed degree isLocal secondValid
  rw [← sameDrawing] at secondClauseMember ⊢
  apply
    (first.source.incidenceDrawing formula)
      |>.embeddedRoutes_avoidEachOther_of_members
        (first.localDrawingIsPlanar
          wellFormed degree isLocal firstValid)
        (first.localClauseMember
          wellFormed degree isLocal firstValid)
        secondClauseMember
        firstLiteralMember secondLiteralMember different

/-- Every genuine global incidence exposes the exact valid local drawing,
local clause, local route, and local planarity certificate selected by its
source metadata. -/
theorem drawingPlanarSATLocalIncidence_localWitness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATFormula formula).zipIdx)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ metadata,
      (drawingPlanarSATClauseMetadata
          formula)[clauseIndex]? = some metadata ∧
        metadata.clause = clause ∧
          metadata.Valid formula ∧
            (metadata.clause,
                metadata.source.localClauseIndex) ∈
              (metadata.source.incidenceDrawing formula).formula.zipIdx ∧
              (literal, literalIndex) ∈
                metadata.clause.literals.zipIdx ∧
                drawingPlanarSATLocalIncidenceRoutes
                    formula clauseIndex literalIndex =
                  (metadata.source.incidenceDrawing formula).routes
                    metadata.source.localClauseIndex literalIndex ∧
                  (metadata.source.incidenceDrawing formula).IsPlanar := by
  rcases drawingPlanarSATClauseMetadata_lookup_valid
      formula clauseMember with
    ⟨metadata, metadataLookup, clauseEqual, valid⟩
  refine
    ⟨metadata, metadataLookup, clauseEqual, valid,
      metadata.localClauseMember
        wellFormed degree isLocal valid, ?_, ?_, ?_⟩
  · simpa [clauseEqual] using literalMember
  · simp [drawingPlanarSATLocalIncidenceRoutes, metadataLookup]
  · exact metadata.localDrawingIsPlanar
      wellFormed degree isLocal valid

/-- Every route in the assembled finite drawing is simple, because its
metadata-selected local component is continuously planar. -/
theorem drawingPlanarSATLocalIncidenceRoute_isSimple
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATFormula formula).zipIdx)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (drawingPlanarSATLocalIncidenceRoutes
        formula clauseIndex literalIndex) := by
  rcases drawingPlanarSATClauseMetadata_lookup_valid
      formula clauseMember with
    ⟨metadata, metadataLookup, clauseEqual, valid⟩
  have localLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have simple := metadata.localRouteIsSimple
    wellFormed degree isLocal valid localLiteralMember
  simpa [drawingPlanarSATLocalIncidenceRoutes,
    metadataLookup] using simple

/-- Indexed route simplicity for the complete assembled drawing. -/
theorem drawingPlanarSATLocalIncidenceDrawing_routesAreSimple
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (drawingPlanarSATLocalIncidenceDrawing formula).RoutesAreSimple := by
  apply
    (drawingPlanarSATLocalIncidenceDrawing formula)
      |>.routesAreSimple_of_members
  rw [drawingPlanarSATLocalIncidenceDrawing_formula,
    drawingPlanarSATLocalIncidenceDrawing_routes]
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  exact drawingPlanarSATLocalIncidenceRoute_isSimple
    formula wellFormed degree isLocal clauseMember literalMember

/-- Component/local-clause key injectivity and cross-component separation
discharge the complete pairwise-route field of global separation. -/
theorem
    drawingPlanarSATLocalIncidenceDrawing_routesAvoidEachOther_of_keyInjective
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (keyInjective :
      DrawingPlanarSATComponentClauseKeysInjective formula)
    (crossComponent :
      DrawingPlanarSATCrossComponentRoutesSeparated formula) :
    ∀ firstIndex secondIndex :
        Fin
          (drawingPlanarSATLocalIncidenceDrawing
            formula).incidences.length,
      firstIndex ≠ secondIndex →
        EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
          ((drawingPlanarSATLocalIncidenceDrawing formula).routeAt
            ((drawingPlanarSATLocalIncidenceDrawing
              formula).incidenceAt firstIndex))
          ((drawingPlanarSATLocalIncidenceDrawing formula).routeAt
            ((drawingPlanarSATLocalIncidenceDrawing
              formula).incidenceAt secondIndex)) := by
  intro firstIndex secondIndex different
  let drawing :=
    drawingPlanarSATLocalIncidenceDrawing formula
  let firstIncidence := drawing.incidenceAt firstIndex
  let secondIncidence := drawing.incidenceAt secondIndex
  have firstIncidenceMember :
      firstIncidence ∈ drawing.incidences :=
    List.get_mem drawing.incidences firstIndex
  have secondIncidenceMember :
      secondIncidence ∈ drawing.incidences :=
    List.get_mem drawing.incidences secondIndex
  have firstMembers :=
    (mem_embeddedCNFIncidences_iff
      drawing.formula firstIncidence).mp firstIncidenceMember
  have secondMembers :=
    (mem_embeddedCNFIncidences_iff
      drawing.formula secondIncidence).mp secondIncidenceMember
  have firstClauseMember :
      (firstIncidence.clause, firstIncidence.clauseIndex) ∈
        (drawingPlanarSATFormula formula).zipIdx := by
    simpa [drawing,
      drawingPlanarSATLocalIncidenceDrawing_formula] using
        firstMembers.1
  have secondClauseMember :
      (secondIncidence.clause, secondIncidence.clauseIndex) ∈
        (drawingPlanarSATFormula formula).zipIdx := by
    simpa [drawing,
      drawingPlanarSATLocalIncidenceDrawing_formula] using
        secondMembers.1
  rcases drawingPlanarSATClauseMetadata_lookup_valid
      formula firstClauseMember with
    ⟨firstMetadata, firstLookup,
      firstClauseEqual, firstValid⟩
  rcases drawingPlanarSATClauseMetadata_lookup_valid
      formula secondClauseMember with
    ⟨secondMetadata, secondLookup,
      secondClauseEqual, secondValid⟩
  change EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
    (drawing.routes
      firstIncidence.clauseIndex firstIncidence.literalIndex)
    (drawing.routes
      secondIncidence.clauseIndex secondIncidence.literalIndex)
  rw [show drawing.routes =
      drawingPlanarSATLocalIncidenceRoutes formula by
    simp [drawing]]
  by_cases sameComponent :
      firstMetadata.source.component =
        secondMetadata.source.component
  · have localCoordinatesDifferent :
        firstMetadata.source.localClauseIndex ≠
              secondMetadata.source.localClauseIndex ∨
          firstIncidence.literalIndex ≠
              secondIncidence.literalIndex := by
      rcases drawing.incidenceCoordinates_ne_of_ne different with
        globalClauseDifferent | literalDifferent
      · left
        intro localClauseEqual
        exact globalClauseDifferent
          (keyInjective firstLookup secondLookup
            sameComponent localClauseEqual)
      · exact Or.inr literalDifferent
    have firstLiteralMember :
        (firstIncidence.literal, firstIncidence.literalIndex) ∈
          firstMetadata.clause.literals.zipIdx := by
      simpa [firstClauseEqual] using firstMembers.2
    have secondLiteralMember :
        (secondIncidence.literal, secondIncidence.literalIndex) ∈
          secondMetadata.clause.literals.zipIdx := by
      simpa [secondClauseEqual] using secondMembers.2
    have localAvoids :=
      firstMetadata.localRoutesAvoidEachOther
        wellFormed degree isLocal secondMetadata
        firstValid secondValid sameComponent
        firstLiteralMember secondLiteralMember
        localCoordinatesDifferent
    simpa [drawingPlanarSATLocalIncidenceRoutes,
      firstLookup, secondLookup] using localAvoids
  · exact crossComponent
      firstClauseMember secondClauseMember
      firstMembers.2 secondMembers.2
      firstLookup secondLookup sameComponent

/-- Cross-component separation alone now discharges global pairwise route
separation: component/local-clause key injectivity is certified by the
five-family metadata enumeration. -/
theorem drawingPlanarSATLocalIncidenceDrawing_routesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (crossComponent :
      DrawingPlanarSATCrossComponentRoutesSeparated formula) :
    ∀ firstIndex secondIndex :
        Fin
          (drawingPlanarSATLocalIncidenceDrawing
            formula).incidences.length,
      firstIndex ≠ secondIndex →
        EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
          ((drawingPlanarSATLocalIncidenceDrawing formula).routeAt
            ((drawingPlanarSATLocalIncidenceDrawing
              formula).incidenceAt firstIndex))
          ((drawingPlanarSATLocalIncidenceDrawing formula).routeAt
            ((drawingPlanarSATLocalIncidenceDrawing
              formula).incidenceAt secondIndex)) := by
  exact
    drawingPlanarSATLocalIncidenceDrawing_routesAvoidEachOther_of_keyInjective
      formula wellFormed degree isLocal
      (drawingPlanarSAT_componentClauseKeysInjective formula)
      crossComponent

/-- Once component keys are injective and different components are
geometrically separated, only vertex/route avoidance and vertex-position
distinctness remain for complete finite planarity. -/
theorem
    drawingPlanarSATLocalIncidenceDrawing_isPlanar_iff_vertexSeparation
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (crossComponent :
      DrawingPlanarSATCrossComponentRoutesSeparated formula) :
    (drawingPlanarSATLocalIncidenceDrawing formula).IsPlanar ↔
      (drawingPlanarSATLocalIncidenceDrawing
          formula).VerticesAvoidRouteInteriors ∧
        (drawingPlanarSATLocalIncidenceDrawing
          formula).vertexPositions.Nodup := by
  constructor
  · intro planar
    exact planar.2.2
  · rintro ⟨verticesAvoid, verticesNodup⟩
    exact
      ⟨drawingPlanarSATLocalIncidenceDrawing_routesAreSimple
          formula wellFormed degree isLocal,
        drawingPlanarSATLocalIncidenceDrawing_routesAvoidEachOther
          formula wellFormed degree isLocal
          crossComponent,
        verticesAvoid, verticesNodup⟩

/-- Complete finite planarity now reduces exactly to global separation;
route simplicity is already discharged component by component. -/
theorem drawingPlanarSATLocalIncidenceDrawing_isPlanar_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (drawingPlanarSATLocalIncidenceDrawing formula).IsPlanar ↔
      (drawingPlanarSATLocalIncidenceDrawing
        formula).GlobalSeparation := by
  exact
    (drawingPlanarSATLocalIncidenceDrawing formula)
      |>.isPlanar_iff_globalSeparation
        (drawingPlanarSATLocalIncidenceDrawing_routesAreSimple
          formula wellFormed degree isLocal)

end PeriodicOrthocrossing
end LeanTrominoes
