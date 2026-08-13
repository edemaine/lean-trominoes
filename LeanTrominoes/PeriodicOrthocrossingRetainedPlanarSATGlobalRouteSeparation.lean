/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATClauseKeys

/-!
# Global route separation for the retained planar SAT drawing

Component separation and component/local-clause key injectivity lift through
the retained metadata lookup to the actual globally indexed route family.
Thus every assembled route is simple and every two distinct incidences have
complete continuous route separation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Cross-component route separation stated in the global clause indices of
the retained formula. -/
def RetainedDrawingPlanarSATCrossComponentRoutesSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Prop :=
  ∀ {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat},
    (firstClause, firstClauseIndex) ∈
        (retainedDrawingPlanarSATFormula formula).zipIdx →
      (secondClause, secondClauseIndex) ∈
        (retainedDrawingPlanarSATFormula formula).zipIdx →
      ∀ {firstLiteral secondLiteral :
          PlanarSATVariable Variable × Bool}
        {firstLiteralIndex secondLiteralIndex : Nat},
        (firstLiteral, firstLiteralIndex) ∈
            firstClause.literals.zipIdx →
          (secondLiteral, secondLiteralIndex) ∈
            secondClause.literals.zipIdx →
          ∀ {firstMetadata secondMetadata :
              DrawingPlanarSATClauseMetadata Variable},
            (retainedDrawingPlanarSATClauseMetadata
                formula)[firstClauseIndex]? =
              some firstMetadata →
            (retainedDrawingPlanarSATClauseMetadata
                formula)[secondClauseIndex]? =
              some secondMetadata →
            firstMetadata.source.component ≠
                secondMetadata.source.component →
            EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
              (retainedDrawingPlanarSATLocalIncidenceRoutes
                formula firstClauseIndex firstLiteralIndex)
              (retainedDrawingPlanarSATLocalIncidenceRoutes
                formula secondClauseIndex secondLiteralIndex)

/-- Component-level separation lifts to globally indexed retained routes. -/
theorem
    retainedDrawingPlanarSAT_crossComponentRoutesSeparated_of_components
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (componentsSeparated :
      RetainedDrawingPlanarSATComponentRoutesSeparated formula) :
    RetainedDrawingPlanarSATCrossComponentRoutesSeparated formula := by
  intro firstClause secondClause
    firstClauseIndex secondClauseIndex
    firstClauseMember secondClauseMember
    firstLiteral secondLiteral
    firstLiteralIndex secondLiteralIndex
    firstLiteralMember secondLiteralMember
    firstMetadata secondMetadata
    firstLookup secondLookup differentComponents
  rcases retainedDrawingPlanarSATClauseMetadata_lookup_valid
      formula firstClauseMember with
    ⟨firstMetadata', firstLookup',
      firstClauseEqual, firstValid⟩
  rcases retainedDrawingPlanarSATClauseMetadata_lookup_valid
      formula secondClauseMember with
    ⟨secondMetadata', secondLookup',
      secondClauseEqual, secondValid⟩
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
  simpa [retainedDrawingPlanarSATLocalIncidenceRoutes,
    firstLookup, secondLookup] using separated

/-- The retained construction satisfies global cross-component route
separation. -/
theorem retainedDrawingPlanarSAT_crossComponentRoutesSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    RetainedDrawingPlanarSATCrossComponentRoutesSeparated formula :=
  retainedDrawingPlanarSAT_crossComponentRoutesSeparated_of_components
    formula
    (retainedDrawingPlanarSAT_componentRoutesSeparated
      formula wellFormed degree isLocal)

/-- Every globally selected retained route is simple. -/
theorem retainedDrawingPlanarSATLocalIncidenceRoute_isSimple
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
        (retainedDrawingPlanarSATFormula formula).zipIdx)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (retainedDrawingPlanarSATLocalIncidenceRoutes
        formula clauseIndex literalIndex) := by
  rcases retainedDrawingPlanarSATClauseMetadata_lookup_valid
      formula clauseMember with
    ⟨metadata, metadataLookup, clauseEqual, valid⟩
  have localLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have simple := metadata.retainedLocalRouteIsSimple
    wellFormed degree isLocal valid localLiteralMember
  simpa [retainedDrawingPlanarSATLocalIncidenceRoutes,
    metadataLookup] using simple

/-- Indexed route simplicity for the complete retained drawing. -/
theorem retainedDrawingPlanarSATLocalIncidenceDrawing_routesAreSimple
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (retainedDrawingPlanarSATLocalIncidenceDrawing
      formula).RoutesAreSimple := by
  apply
    (retainedDrawingPlanarSATLocalIncidenceDrawing formula)
      |>.routesAreSimple_of_members
  rw [retainedDrawingPlanarSATLocalIncidenceDrawing_formula,
    retainedDrawingPlanarSATLocalIncidenceDrawing_routes]
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  exact retainedDrawingPlanarSATLocalIncidenceRoute_isSimple
    formula wellFormed degree isLocal clauseMember literalMember

/-- Key injectivity and cross-component separation discharge pairwise route
separation for the globally indexed retained drawing. -/
theorem
    retainedDrawingPlanarSATLocalIncidenceDrawing_routesAvoidEachOther_of_keyInjective
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (keyInjective :
      RetainedDrawingPlanarSATComponentClauseKeysInjective formula)
    (crossComponent :
      RetainedDrawingPlanarSATCrossComponentRoutesSeparated formula) :
    ∀ firstIndex secondIndex :
        Fin
          (retainedDrawingPlanarSATLocalIncidenceDrawing
            formula).incidences.length,
      firstIndex ≠ secondIndex →
        EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
          ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
            ((retainedDrawingPlanarSATLocalIncidenceDrawing
              formula).incidenceAt firstIndex))
          ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
            ((retainedDrawingPlanarSATLocalIncidenceDrawing
              formula).incidenceAt secondIndex)) := by
  intro firstIndex secondIndex different
  let drawing :=
    retainedDrawingPlanarSATLocalIncidenceDrawing formula
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
        (retainedDrawingPlanarSATFormula formula).zipIdx := by
    simpa [drawing,
      retainedDrawingPlanarSATLocalIncidenceDrawing_formula] using
        firstMembers.1
  have secondClauseMember :
      (secondIncidence.clause, secondIncidence.clauseIndex) ∈
        (retainedDrawingPlanarSATFormula formula).zipIdx := by
    simpa [drawing,
      retainedDrawingPlanarSATLocalIncidenceDrawing_formula] using
        secondMembers.1
  rcases retainedDrawingPlanarSATClauseMetadata_lookup_valid
      formula firstClauseMember with
    ⟨firstMetadata, firstLookup,
      firstClauseEqual, firstValid⟩
  rcases retainedDrawingPlanarSATClauseMetadata_lookup_valid
      formula secondClauseMember with
    ⟨secondMetadata, secondLookup,
      secondClauseEqual, secondValid⟩
  change EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
    (drawing.routes
      firstIncidence.clauseIndex firstIncidence.literalIndex)
    (drawing.routes
      secondIncidence.clauseIndex secondIncidence.literalIndex)
  rw [show drawing.routes =
      retainedDrawingPlanarSATLocalIncidenceRoutes formula by
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
      firstMetadata.retainedLocalRoutesAvoidEachOther
        wellFormed degree isLocal secondMetadata
        firstValid secondValid sameComponent
        firstLiteralMember secondLiteralMember
        localCoordinatesDifferent
    simpa [retainedDrawingPlanarSATLocalIncidenceRoutes,
      firstLookup, secondLookup] using localAvoids
  · exact crossComponent
      firstClauseMember secondClauseMember
      firstMembers.2 secondMembers.2
      firstLookup secondLookup sameComponent

/-- Every two distinct incidences of the retained finite drawing have
complete continuous route separation. -/
theorem
    retainedDrawingPlanarSATLocalIncidenceDrawing_routesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    ∀ firstIndex secondIndex :
        Fin
          (retainedDrawingPlanarSATLocalIncidenceDrawing
            formula).incidences.length,
      firstIndex ≠ secondIndex →
        EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
          ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
            ((retainedDrawingPlanarSATLocalIncidenceDrawing
              formula).incidenceAt firstIndex))
          ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
            ((retainedDrawingPlanarSATLocalIncidenceDrawing
              formula).incidenceAt secondIndex)) := by
  exact
    retainedDrawingPlanarSATLocalIncidenceDrawing_routesAvoidEachOther_of_keyInjective
      formula wellFormed degree isLocal
      (retainedDrawingPlanarSAT_componentClauseKeysInjective formula)
      (retainedDrawingPlanarSAT_crossComponentRoutesSeparated
        formula wellFormed degree isLocal)

end PeriodicOrthocrossing
end LeanTrominoes
