/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalRoutes

/-! # Presentation indices of selected Figure 9 local routes -/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT

private theorem incidenceAt_eq_of_drawing_eq
    {Variable : Type*}
    (first second : EmbeddedCNFIncidenceDrawing Variable)
    (equal : first = second)
    (index : Fin first.incidences.length) :
    first.incidenceAt index =
      second.incidenceAt
        (Fin.cast
          (congrArg
            (fun drawing : EmbeddedCNFIncidenceDrawing Variable =>
              drawing.incidences.length)
            equal)
          index) := by
  subst second
  rfl

/-- Equal-valued indices preserve both presentation coordinates and the
literal's actual variable under template instantiation. -/
theorem templateIncidence_data_eq_instantiated
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (incidenceIndex : Fin
      ((instantiatedDrawing sourceClauseIndex figureNineClauseStart source).incidences.length))
    (templateIndex : Fin (templateDrawing source).incidences.length)
    (indexValue : templateIndex.val = incidenceIndex.val) :
    ((templateDrawing source).incidenceAt templateIndex).clauseIndex =
        ((instantiatedDrawing sourceClauseIndex figureNineClauseStart source).incidenceAt
          incidenceIndex).clauseIndex ∧
      ((templateDrawing source).incidenceAt templateIndex).literalIndex =
        ((instantiatedDrawing sourceClauseIndex figureNineClauseStart source).incidenceAt
          incidenceIndex).literalIndex ∧
      instantiatedVariableMap sourceClauseIndex figureNineClauseStart source
          ((templateDrawing source).incidenceAt templateIndex).literal.1 =
        ((instantiatedDrawing sourceClauseIndex figureNineClauseStart source).incidenceAt
          incidenceIndex).literal.1 := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  let template := templateDrawing source
  let variableMap :=
    instantiatedVariableMap sourceClauseIndex figureNineClauseStart source
  let renamed := EmbeddedCNFIncidenceDrawing.renameToImage template variableMap
  let offset := Cell.scale composedGadgetScale source.position
  let target := renamed.translate offset
  have drawingEqual :
      instantiatedDrawing sourceClauseIndex figureNineClauseStart source =
        target := by
    simpa [target, renamed, template, variableMap, offset] using
      instantiatedDrawing_eq sourceClauseIndex figureNineClauseStart source
  let targetIndex : Fin target.incidences.length :=
    Fin.cast
      (congrArg
        (fun drawing : EmbeddedCNFIncidenceDrawing
          (OneInThreeNoUnitVariable (OneInThreeVariable Variable)) =>
            drawing.incidences.length)
        drawingEqual)
      incidenceIndex
  let renamedIndex : Fin renamed.incidences.length :=
    ⟨targetIndex.val, targetIndex.isLt.trans_eq
      (EmbeddedCNFIncidenceDrawing.translate_incidences_length
        renamed offset)⟩
  let sourceIndex : Fin template.incidences.length :=
    ⟨renamedIndex.val, renamedIndex.isLt.trans_eq
      (EmbeddedCNFIncidenceDrawing.rename_incidences_length
        template variableMap
        (EmbeddedCNFIncidenceDrawing.imageVariablePosition
          template variableMap))⟩
  have sourceIndexEq : sourceIndex = templateIndex := by
    apply Fin.ext
    simpa [sourceIndex, renamedIndex, targetIndex] using indexValue.symm
  have selectedIncidenceEqual :
      (instantiatedDrawing sourceClauseIndex figureNineClauseStart source).incidenceAt
          incidenceIndex =
        target.incidenceAt targetIndex := by
    simpa only [targetIndex] using
      incidenceAt_eq_of_drawing_eq
        (instantiatedDrawing sourceClauseIndex figureNineClauseStart source)
        target drawingEqual incidenceIndex
  have translatedIncidence :=
    EmbeddedCNFIncidenceDrawing.incidenceAt_translate
      renamed offset targetIndex
  have renamedIndexEqual :
      (⟨targetIndex.val, by
        exact targetIndex.isLt.trans_eq
          (EmbeddedCNFIncidenceDrawing.translate_incidences_length
            renamed offset)⟩ : Fin renamed.incidences.length) =
        renamedIndex := by
    apply Fin.ext
    rfl
  rw [renamedIndexEqual] at translatedIncidence
  have renamedIncidence :=
    EmbeddedCNFIncidenceDrawing.incidenceAt_rename
      template variableMap
      (EmbeddedCNFIncidenceDrawing.imageVariablePosition
        template variableMap)
      renamedIndex
  have sourceIndexEqual :
      (⟨renamedIndex.val, by
        exact renamedIndex.isLt.trans_eq
          (EmbeddedCNFIncidenceDrawing.rename_incidences_length
            template variableMap
            (EmbeddedCNFIncidenceDrawing.imageVariablePosition
              template variableMap))⟩ : Fin template.incidences.length) =
        sourceIndex := by
    apply Fin.ext
    rfl
  rw [sourceIndexEqual, sourceIndexEq] at renamedIncidence
  change renamed.incidenceAt renamedIndex =
    EmbeddedCNFIncidence.rename variableMap
      (template.incidenceAt templateIndex) at renamedIncidence
  rw [selectedIncidenceEqual, translatedIncidence, renamedIncidence]
  exact ⟨rfl, rfl, rfl⟩

/-- Equal-valued indices in the instantiated drawing and its finite template
select incidences with the same clause and literal presentation indices. -/
theorem templateIncidence_coordinates_eq_instantiated
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (incidenceIndex : Fin
      ((instantiatedDrawing sourceClauseIndex figureNineClauseStart source).incidences.length))
    (templateIndex : Fin (templateDrawing source).incidences.length)
    (indexValue : templateIndex.val = incidenceIndex.val) :
    ((templateDrawing source).incidenceAt templateIndex).clauseIndex =
        ((instantiatedDrawing sourceClauseIndex figureNineClauseStart source).incidenceAt
          incidenceIndex).clauseIndex ∧
      ((templateDrawing source).incidenceAt templateIndex).literalIndex =
        ((instantiatedDrawing sourceClauseIndex figureNineClauseStart source).incidenceAt
          incidenceIndex).literalIndex := by
  have data := templateIncidence_data_eq_instantiated
    sourceClauseIndex figureNineClauseStart source incidenceIndex templateIndex indexValue
  exact ⟨data.1, data.2.1⟩

/-- A genuine generated incidence retains its clause-major presentation
index when the instantiated Figure 9 drawing is related back to its finite
template.  This is the index needed by the finite route-prefix descriptor. -/
theorem localRoutes_eq_translated_templateRoute_with_index_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
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
      (incidenceIndex : Fin
        (instantiatedDrawing
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause).incidences.length)
      (templateIndex : Fin
        (templateDrawing metadata.sourceClause).incidences.length),
      (formulaClauseMetadata source)[clauseIndex]? = some metadata ∧
        metadata.clause = clause ∧
        (instantiatedDrawing
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause).incidenceAt incidenceIndex =
            ⟨PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
              metadata.localClauseIndex,
              (literal.atom, literal.value), literalIndex⟩ ∧
        templateIndex.val = incidenceIndex.val ∧
        ((templateDrawing metadata.sourceClause).incidenceAt
          templateIndex).clauseIndex = metadata.localClauseIndex ∧
        ((templateDrawing metadata.sourceClause).incidenceAt
          templateIndex).literalIndex = literalIndex ∧
        localRoutes source clauseIndex literalIndex =
          PeriodicOrthocrossing.translatePolyline
            (Cell.scale composedGadgetScale
              metadata.sourceClause.position)
            ((templateDrawing metadata.sourceClause).routeAt
              ((templateDrawing metadata.sourceClause).incidenceAt
                templateIndex)) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  rcases formulaClauseMetadata_lookup_valid_embedded
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have metadataSourceMember :
      metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth :
      metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, metadataSourceMember, rfl⟩
  let drawing :=
    instantiatedDrawing
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause
  have drawingFormula :
      drawing.formula =
        composedClauseGadget
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause :=
    instantiatedDrawing_formula
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth
  have embeddedClauseMember :
      (PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
          metadata.localClauseIndex) ∈ drawing.formula.zipIdx := by
    rw [drawingFormula]
    exact localClauseMember
  have embeddedLiteralMember :
      ((literal.atom, literal.value), literalIndex) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause).literals.zipIdx := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(literal, literalIndex), metadataLiteralMember, rfl⟩
  let incidence :
      EmbeddedCNFIncidence
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)) :=
    ⟨PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
      metadata.localClauseIndex,
      (literal.atom, literal.value), literalIndex⟩
  have incidenceMember : incidence ∈ drawing.incidences :=
    (mem_embeddedCNFIncidences_iff drawing.formula incidence).mpr
      ⟨embeddedClauseMember, embeddedLiteralMember⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  rcases instantiatedDrawing_routeAt_incidenceAt_eq
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause incidenceIndex with
    ⟨templateIndex, templateIndexValue, selectedRoute⟩
  have templateCoordinates :=
    templateIncidence_coordinates_eq_instantiated
      metadata.sourceClauseIndex metadata.figureNineClauseStart
      metadata.sourceClause incidenceIndex templateIndex templateIndexValue
  have instantiatedIncidenceEqual :
      (instantiatedDrawing metadata.sourceClauseIndex
        metadata.figureNineClauseStart metadata.sourceClause).incidenceAt
          incidenceIndex = incidence := by
    simpa [drawing, EmbeddedCNFIncidenceDrawing.incidenceAt] using
      incidenceEqual
  refine ⟨metadata, incidenceIndex, templateIndex,
    metadataLookup, clauseEqual, ?_, templateIndexValue,
    ?_, ?_, ?_⟩
  · exact incidenceEqual
  · rw [instantiatedIncidenceEqual] at templateCoordinates
    exact templateCoordinates.1
  · rw [instantiatedIncidenceEqual] at templateCoordinates
    exact templateCoordinates.2
  · calc
      localRoutes source clauseIndex literalIndex =
          drawing.routes metadata.localClauseIndex literalIndex := by
        simp [localRoutes, metadataLookup, drawing]
      _ = drawing.routeAt (drawing.incidenceAt incidenceIndex) := by
        unfold EmbeddedCNFIncidenceDrawing.routeAt
          EmbeddedCNFIncidenceDrawing.incidenceAt
        rw [incidenceEqual]
      _ = _ := selectedRoute

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
