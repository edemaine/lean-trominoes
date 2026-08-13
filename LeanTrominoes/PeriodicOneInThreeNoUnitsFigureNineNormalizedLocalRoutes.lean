/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalRoutes
import LeanTrominoes.PositionedPeriodicCNFDeduplicationRoutes
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Anchor-normalized composed Figure 9 routes

The certified composed drawings use displayed physical coordinates in each
original source clause's `72 × 72` refinement box.  A periodic incidence
drawing instead stores every route in the canonical anchor gauge of its
final clause.  This file performs that normalization and records the exact
endpoints, orthogonality, and continuous simplicity of the selected routes.

For incidences inherited from the original source, the normalized local
endpoint is the splice point at which the external source-route tail will
be attached.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT

/-- Variable placement obtained by applying Figure 9 and then unit
elimination to a positioned source placement. -/
def composedPlacement
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    PeriodicVariablePlacement
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable)) :=
  PeriodicOneInThreeNoUnitsPositioned.placement
    (PeriodicOneInThreePositioned.formula source)
    (PeriodicOneInThreePositioned.placement
      source sourcePlacement)

/-- The endpoint advertised by the selected composed finite drawing,
expressed in the canonical anchor gauge of its final periodic clause. -/
def normalizedLocalEndpoint
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex literalIndex : Nat) : Cell :=
  match (formulaClauseMetadata source)[clauseIndex]? with
  | none => (0, 0)
  | some metadata =>
      match metadata.clause.literals[literalIndex]? with
      | none => (0, 0)
      | some literal =>
          Cell.sub
            ((instantiatedDrawing
              metadata.sourceClauseIndex
              metadata.figureNineClauseStart
              metadata.sourceClause).variablePosition literal.atom)
            ((composedPlacement source sourcePlacement).translation
              (PeriodicCNF.clauseAnchor
                metadata.clause.literals))

/-- Normalize every metadata-selected composed local route by the anchor of
its final clause. -/
def normalizedLocalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match (formulaClauseMetadata source)[clauseIndex]? with
    | none => []
    | some metadata =>
        PositionedPeriodicCNF.normalizeIncidenceRoute
          (composedPlacement source sourcePlacement)
          metadata.clause
          (localRoutes source clauseIndex literalIndex)

/-- Every genuine normalized local route is exactly its finite-template
route translated to the source-clause position in the generated clause's
anchor gauge. -/
theorem normalizedLocalRoutes_eq_translated_templateRoute_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ (metadata : ClauseMetadata Variable)
      (templateIndex : Fin
        (templateDrawing metadata.sourceClause).incidences.length),
      (formulaClauseMetadata source)[clauseIndex]? = some metadata ∧
        metadata.clause = clause ∧
        normalizedLocalRoutes source sourcePlacement
            clauseIndex literalIndex =
          PeriodicOrthocrossing.translatePolyline
            (Cell.sub
              (Cell.scale composedGadgetScale
                metadata.sourceClause.position)
              ((composedPlacement source sourcePlacement).translation
                (PeriodicCNF.clauseAnchor metadata.clause.literals)))
            ((templateDrawing metadata.sourceClause).routeAt
              ((templateDrawing metadata.sourceClause).incidenceAt
                templateIndex)) := by
  rcases localRoutes_eq_translated_templateRoute_of_members
      source sourceWidth clauseMember literalMember with
    ⟨metadata, templateIndex, metadataLookup, clauseEqual,
      localRouteEqual⟩
  refine ⟨metadata, templateIndex, metadataLookup, clauseEqual, ?_⟩
  let anchor :=
    (composedPlacement source sourcePlacement).translation
      (PeriodicCNF.clauseAnchor metadata.clause.literals)
  let macroOrigin :=
    Cell.scale composedGadgetScale metadata.sourceClause.position
  let templateRoute :=
    (templateDrawing metadata.sourceClause).routeAt
      ((templateDrawing metadata.sourceClause).incidenceAt templateIndex)
  have composedTranslations :
      (PeriodicOrthocrossing.translatePolyline
          macroOrigin templateRoute).map
          (fun point => Cell.sub point anchor) =
        PeriodicOrthocrossing.translatePolyline
          (Cell.sub macroOrigin anchor) templateRoute := by
    unfold PeriodicOrthocrossing.translatePolyline
    rw [List.map_map]
    apply List.map_congr_left
    intro point pointMember
    apply Prod.ext <;>
      simp [Cell.add, Cell.sub, sub_eq_add_neg, add_comm, add_assoc]
  simpa [normalizedLocalRoutes, metadataLookup,
    PositionedPeriodicCNF.normalizeIncidenceRoute,
    clauseEqual, localRouteEqual, anchor, macroOrigin, templateRoute]
    using composedTranslations

/-- Every genuine normalized composed route has the exact canonical
final-clause endpoint and selected normalized local endpoint. -/
theorem normalizedLocalRoutes_endpoints_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (composedPlacement source sourcePlacement) clause) ∧
      (normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex).getLast? =
        some
          (normalizedLocalEndpoint source sourcePlacement
            clauseIndex literalIndex) := by
  rcases localRoutes_endpoints_of_members
      source sourceWidth sourceDistinct
      clauseMember literalMember with
    ⟨metadata, metadataLookup, clauseEqual,
      localHead, localLast⟩
  subst clause
  constructor
  · simpa [normalizedLocalRoutes, metadataLookup] using
      PositionedPeriodicCNF.normalizeIncidenceRoute_head?
        (composedPlacement source sourcePlacement)
        metadata.clause
        (localRoutes source clauseIndex literalIndex)
        localHead
  · have literalLookup :
        metadata.clause.literals[literalIndex]? =
          some literal :=
      (List.mem_zipIdx_iff_getElem?).mp literalMember
    simp [normalizedLocalRoutes, normalizedLocalEndpoint,
      metadataLookup,
      PositionedPeriodicCNF.normalizeIncidenceRoute,
      localLast, literalLookup]

/-- Anchor normalization preserves orthogonality of every genuine selected
composed route. -/
theorem normalizedLocalRoutes_orthogonal_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex) := by
  rcases formulaClauseMetadata_lookup
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  subst clause
  simpa [normalizedLocalRoutes, metadataLookup] using
    PositionedPeriodicCNF.normalizeIncidenceRoute_orthogonal
      (composedPlacement source sourcePlacement)
      metadata.clause
      (localRoutes source clauseIndex literalIndex)
      (localRoutes_orthogonal_of_members
        source sourceWidth sourceDistinct
        clauseMember literalMember)

/-- Anchor normalization is a common translation and therefore preserves
continuous route simplicity. -/
theorem normalizedLocalRoutes_isSimple_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex) := by
  rcases formulaClauseMetadata_lookup
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  subst clause
  let anchor :=
    (composedPlacement source sourcePlacement).translation
      (PeriodicCNF.clauseAnchor metadata.clause.literals)
  have translatedSimple :=
    EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
      (localRoutes_isSimple_of_members
        source sourceWidth sourceDistinct
        clauseMember literalMember)
      (Cell.scale (-1) anchor)
  have normalizedRouteEqual :
      PositionedPeriodicCNF.normalizeIncidenceRoute
          (composedPlacement source sourcePlacement)
          metadata.clause
          (localRoutes source clauseIndex literalIndex) =
        (localRoutes source clauseIndex literalIndex).map
          (Cell.add (Cell.scale (-1) anchor)) := by
    unfold PositionedPeriodicCNF.normalizeIncidenceRoute
    apply List.map_congr_left
    intro point pointMember
    apply Prod.ext <;>
      simp [Cell.sub, Cell.add, Cell.scale, anchor,
        sub_eq_add_neg, add_comm]
  simpa [normalizedLocalRoutes, metadataLookup,
    normalizedRouteEqual] using translatedSimple

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
