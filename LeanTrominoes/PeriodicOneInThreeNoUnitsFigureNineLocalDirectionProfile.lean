/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineClauseProfileTemplate
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRoutes

/-!
# Clause-profile selection for Figure 9 local routes

Every genuine normalized local route is a translation of the finite template
route selected by its source clause profile and one dependent incidence index.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicOrthocrossing

private theorem selectedRoute_eq_of_drawing_eq
    (first second :
      EmbeddedCNFIncidenceDrawing FigureNineNoUnitsVariable)
    (drawingEq : first = second)
    (index : Fin second.incidences.length) :
    let castIndex : Fin first.incidences.length :=
      Fin.cast
        (congrArg
          (fun drawing :
            EmbeddedCNFIncidenceDrawing FigureNineNoUnitsVariable =>
            drawing.incidences.length)
          drawingEq.symm)
        index
    first.routeAt (first.incidenceAt castIndex) =
      second.routeAt (second.incidenceAt index) := by
  subst second
  rfl

/-- A genuine normalized local route is one translated finite profile route.
The translation is retained only to state the exact point-list equality; it
will disappear at the direction boundary. -/
theorem normalizedLocalRoutes_eq_translated_profileRoute_of_members
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause.literals ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ (profile : ClauseProfile)
        (templateIndex :
          Fin (templateDrawingOfClauseProfile profile).incidences.length)
        (origin : Cell),
      normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex =
        translatePolyline origin
          ((templateDrawingOfClauseProfile profile).routeAt
            ((templateDrawingOfClauseProfile profile).incidenceAt
              templateIndex)) := by
  rcases normalizedLocalRoutes_eq_translated_templateRoute_of_members
      source sourcePlacement sourceWidth clauseMember literalMember with
    ⟨metadata, concreteIndex, metadataLookup, _metadataClause, localEq⟩
  have metadataSourceMember : metadata.sourceClause ∈ source.clauses := by
    rcases formulaClauseMetadata_lookup_valid_embedded
        source clauseMember with
      ⟨witnessMetadata, witnessLookup, _witnessClause,
        sourceClauseMember, _localClauseMember⟩
    have witnessEq : witnessMetadata = metadata := by
      apply Option.some.inj
      exact witnessLookup.symm.trans metadataLookup
    subst witnessMetadata
    exact List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataNonempty : metadata.sourceClause.literals ≠ [] :=
    sourceClausesNonempty metadata.sourceClause metadataSourceMember
  have metadataWidth : metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, metadataSourceMember, rfl⟩
  let profile :=
    FormulaShapeOfFormula.clauseProfile
      (ClauseProfileOccurrenceSplit.literalProfiles
        metadata.sourceClause.literals)
  have drawingEq :
      templateDrawingOfClauseProfile profile =
        templateDrawing metadata.sourceClause := by
    simpa only [profile] using
      templateDrawingOfClauseProfile_clauseProfile_literalProfiles
        metadata.sourceClause metadataNonempty metadataWidth
  let templateIndex :
      Fin (templateDrawingOfClauseProfile profile).incidences.length :=
    Fin.cast
      (congrArg
        (fun drawing :
          EmbeddedCNFIncidenceDrawing FigureNineNoUnitsVariable =>
          drawing.incidences.length)
        drawingEq.symm)
      concreteIndex
  have selectedRouteEq :
      (templateDrawingOfClauseProfile profile).routeAt
          ((templateDrawingOfClauseProfile profile).incidenceAt
            templateIndex) =
        (templateDrawing metadata.sourceClause).routeAt
          ((templateDrawing metadata.sourceClause).incidenceAt
            concreteIndex) := by
    simpa only [templateIndex] using
      selectedRoute_eq_of_drawing_eq
        (templateDrawingOfClauseProfile profile)
        (templateDrawing metadata.sourceClause)
        drawingEq concreteIndex
  let origin :=
    Cell.sub
      (Cell.scale composedGadgetScale metadata.sourceClause.position)
      ((composedPlacement source sourcePlacement).translation
        (PeriodicCNF.clauseAnchor metadata.clause.literals))
  refine ⟨profile, templateIndex, origin, ?_⟩
  calc
    normalizedLocalRoutes source sourcePlacement clauseIndex literalIndex =
        translatePolyline origin
          ((templateDrawing metadata.sourceClause).routeAt
            ((templateDrawing metadata.sourceClause).incidenceAt
              concreteIndex)) := by
      simpa only [origin] using localEq
    _ = _ := by rw [← selectedRouteEq]

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
