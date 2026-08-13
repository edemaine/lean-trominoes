/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarOneInThreeFigureNineMiddleRouteDirections
import LeanTrominoes.PeriodicOneInThreePositionedAuxiliaryEndpoints

/-!
# Middle-route exits after Figure 9 splicing

The finite Figure 9 weak-left invariant survives anchor normalization.  A
complete spliced route has the same first exit as its local prefix, so every
literal-index-one source route used by unit elimination still exits weakly
left of its canonical clause point.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePositioned

open PlanarThreeSAT

/-- The first exit of a normalized literal-index-one Figure 9 route lies
weakly left of its canonical clause endpoint. -/
theorem normalizedLocalRoutes_middle_doesNotExitRight
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause : PositionedPeriodicClause (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeVariable Variable)}
    (literalMember : (literal, 1) ∈ clause.literals.zipIdx)
    (exit : Cell)
    (routeExit :
      (normalizedLocalRoutes source sourcePlacement
        clauseIndex 1).tail.head? = some exit) :
    exit.1 ≤
      (PositionedPeriodicCNF.canonicalClausePosition
        (placement source sourcePlacement) clause).1 := by
  rcases formulaClauseMetadata_lookup_valid source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  subst clause
  have metadataLiteralMember :
      (literal, 1) ∈ metadata.clause.literals.zipIdx := by
    simpa using literalMember
  have metadataSourceMember : metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth : metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, metadataSourceMember, rfl⟩
  let drawing :=
    PlanarOneInThreePositioned.instantiatedDrawing
      metadata.sourceClauseIndex metadata.sourceClause
  have drawingFormula :
      drawing.formula =
        (clauseGadget metadata.sourceClauseIndex
          metadata.sourceClause).map
            PlanarOneInThreeNoUnits.embedPositionedClause :=
    PlanarOneInThreePositioned.instantiatedDrawing_formula
      metadata.sourceClauseIndex metadata.sourceClause metadataWidth
  have embeddedClauseMember :
      (PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
          metadata.localClauseIndex) ∈ drawing.formula.zipIdx := by
    rw [drawingFormula, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(metadata.clause, metadata.localClauseIndex),
        localClauseMember, rfl⟩
  have embeddedLiteralMember :
      ((literal.atom, literal.value), 1) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause).literals.zipIdx := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(literal, 1), metadataLiteralMember, rfl⟩
  let anchor :=
    (placement source sourcePlacement).translation
      (PeriodicCNF.clauseAnchor metadata.clause.literals)
  let route := localRoutes source clauseIndex 1
  have normalizedRouteEqual :
      normalizedLocalRoutes source sourcePlacement clauseIndex 1 =
        route.map (fun point => Cell.sub point anchor) := by
    simp [normalizedLocalRoutes, metadataLookup,
      PositionedPeriodicCNF.normalizeIncidenceRoute, route, anchor]
  have endpoints :=
    normalizedLocalRoutes_endpoints_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember metadataLiteralMember
  cases routeEquation : route with
  | nil =>
      rw [normalizedRouteEqual, routeEquation] at routeExit
      simp at routeExit
  | cons first rest =>
      cases rest with
      | nil =>
          rw [normalizedRouteEqual, routeEquation] at routeExit
          simp at routeExit
      | cons second tail =>
          have drawingRoute :
              drawing.routes metadata.localClauseIndex 1 = route := by
            simp [drawing, route, localRoutes, metadataLookup]
          have physicalDirection : second.1 ≤ first.1 := by
            apply
              EmbeddedCNFIncidenceDrawing.middleRoute_doesNotExitRight_of_members
                drawing
                (PlanarOneInThreePositioned.instantiatedDrawing_middleRoutesDoNotExitRight
                  metadata.sourceClauseIndex metadata.sourceClause
                  metadataWidth)
                embeddedClauseMember embeddedLiteralMember
            · rw [drawingRoute, routeEquation]
              simp
            · rw [drawingRoute, routeEquation]
              simp
          have normalizedHead :
              Cell.sub first anchor =
                PositionedPeriodicCNF.canonicalClausePosition
                  (placement source sourcePlacement) metadata.clause := by
            have headEquation := endpoints.1
            rw [normalizedRouteEqual, routeEquation] at headEquation
            simpa using Option.some.inj headEquation
          have normalizedExit : Cell.sub second anchor = exit := by
            rw [normalizedRouteEqual, routeEquation] at routeExit
            simpa using Option.some.inj routeExit
          rw [← normalizedHead, ← normalizedExit]
          rcases first with ⟨firstX, firstY⟩
          rcases second with ⟨secondX, secondY⟩
          rcases anchor with ⟨anchorX, anchorY⟩
          simpa [Cell.sub] using sub_le_sub_right physicalDirection anchorX

/-- Complete Figure 9 splicing preserves the middle route's weak-left first
exit, independently of the inherited suffix family. -/
theorem splicedRoutes_middle_doesNotExitRight
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (inherited :
      PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
        (formula source)
        (placement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement))
    {clause : PositionedPeriodicClause (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeVariable Variable)}
    (literalMember : (literal, 1) ∈ clause.literals.zipIdx)
    (exit : Cell)
    (routeExit :
      (splicedRoutes source sourcePlacement inherited
        clauseIndex 1).tail.head? = some exit) :
    exit.1 ≤
      (PositionedPeriodicCNF.canonicalClausePosition
        (placement source sourcePlacement) clause).1 := by
  rcases normalizedLocalRoutes_exists_tail_head?_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember with
    ⟨localExit, localRouteExit⟩
  have splicedRouteExit :
      (splicedRoutes source sourcePlacement inherited
        clauseIndex 1).tail.head? = some localExit := by
    unfold splicedRoutes
      PositionedPeriodicCNF.spliceLocalIncidenceRoutes
    exact joinAtEndpoint_tail_head? localRouteExit
  have exitEqual : exit = localExit :=
    Option.some.inj (routeExit.symm.trans splicedRouteExit)
  subst exit
  exact normalizedLocalRoutes_middle_doesNotExitRight
    source sourcePlacement sourceWidth sourceDistinct
    clauseMember literalMember localExit localRouteExit

end PeriodicOneInThreePositioned
end LeanTrominoes
