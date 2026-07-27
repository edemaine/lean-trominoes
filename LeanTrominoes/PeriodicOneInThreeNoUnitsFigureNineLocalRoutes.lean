import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineIndex
import LeanTrominoes.PlanarOneInThreeNoUnitsFigureNineSelector
import LeanTrominoes.PeriodicOneInThreePositionedLocalRoutes
import LeanTrominoes.EmbeddedCNFIncidenceDrawingPlanarity

/-!
# Metadata-selected local composed routes

The composed metadata index selects one certified Figure 9-plus-unit-
elimination drawing and its exact local clause number for every clause of
the actual two-stage positioned formula.

This file packages those selected physical routes and proves exact endpoints
and orthogonality for every genuine incidence.  Incidences inherited from
the original source still end at the composed neighborhood's boundary port;
the later splicing layer will attach the external source-route tail there.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT

/-- Route family obtained by selecting the certified composed drawing
recorded at each final flattened clause index. -/
def localRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match (formulaClauseMetadata source)[clauseIndex]? with
    | none => []
    | some metadata =>
        (instantiatedDrawing
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause).routes
            metadata.localClauseIndex literalIndex

/-- A genuine final clause selects exactly the composed drawing and local
clause index retained by its metadata. -/
theorem localRoutes_of_clause_member
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (literalIndex : Nat) :
    ∃ metadata : ClauseMetadata Variable,
      metadata.clause = clause ∧
      localRoutes source clauseIndex literalIndex =
        (instantiatedDrawing
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause).routes
            metadata.localClauseIndex literalIndex := by
  rcases formulaClauseMetadata_lookup
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  refine ⟨metadata, clauseEqual, ?_⟩
  simp [localRoutes, metadataLookup]

/-- Every genuine selected route meets its displayed final clause and the
exact variable endpoint advertised by its composed finite drawing. -/
theorem localRoutes_endpoints_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
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
    ∃ metadata : ClauseMetadata Variable,
      (formulaClauseMetadata source)[clauseIndex]? =
          some metadata ∧
        metadata.clause = clause ∧
        (localRoutes source clauseIndex literalIndex).head? =
          some clause.position ∧
        (localRoutes source clauseIndex literalIndex).getLast? =
          some
            ((instantiatedDrawing
              metadata.sourceClauseIndex
              metadata.figureNineClauseStart
              metadata.sourceClause).variablePosition literal.atom) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  rcases formulaClauseMetadata_lookup_valid_embedded
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have metadataSourceMember :
      metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth :
      metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, metadataSourceMember, rfl⟩
  have metadataDistinct :
      metadata.sourceClause.AtomsNodup :=
    sourceDistinct metadata.sourceClause metadataSourceMember
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
      (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause,
        metadata.localClauseIndex) ∈
        drawing.formula.zipIdx := by
    rw [drawingFormula]
    exact localClauseMember
  have embeddedLiteralMember :
      ((literal.atom, literal.value), literalIndex) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause).literals.zipIdx := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(literal, literalIndex),
        metadataLiteralMember, rfl⟩
  have drawingValid :
      drawing.IsValid :=
    instantiatedDrawing_isValid
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth metadataDistinct
  have localEndpoints :=
    EmbeddedCNFIncidenceDrawing.physicalRoutesMatch
      drawing drawingValid.1
      (PlanarOneInThreeNoUnits.embedPositionedClause
        metadata.clause)
      metadata.localClauseIndex embeddedClauseMember
      (literal.atom, literal.value)
      literalIndex embeddedLiteralMember
  refine
    ⟨metadata, metadataLookup, clauseEqual, ?_, ?_⟩
  · simpa [localRoutes, metadataLookup, drawing,
      PlanarOneInThreeNoUnits.embedPositionedClause,
      clauseEqual]
      using localEndpoints.1
  · simpa [localRoutes, metadataLookup, drawing]
      using localEndpoints.2

/-- Every genuine selected composed route is orthogonal. -/
theorem localRoutes_orthogonal_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
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
      (localRoutes source clauseIndex literalIndex) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  rcases formulaClauseMetadata_lookup_valid_embedded
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have metadataSourceMember :
      metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth :
      metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, metadataSourceMember, rfl⟩
  have metadataDistinct :
      metadata.sourceClause.AtomsNodup :=
    sourceDistinct metadata.sourceClause metadataSourceMember
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
      (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause,
        metadata.localClauseIndex) ∈
        drawing.formula.zipIdx := by
    rw [drawingFormula]
    exact localClauseMember
  have embeddedLiteralMember :
      ((literal.atom, literal.value), literalIndex) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause).literals.zipIdx := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(literal, literalIndex),
        metadataLiteralMember, rfl⟩
  have drawingValid :
      drawing.IsValid :=
    instantiatedDrawing_isValid
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth metadataDistinct
  have selectedOrthogonal :=
    PeriodicOneInThreePositioned.embeddedRoute_orthogonal_of_members
      drawing drawingValid.2.1
      embeddedClauseMember embeddedLiteralMember
  simpa [localRoutes, metadataLookup, drawing] using
    selectedOrthogonal

/-- Every genuine selected composed route is simple in the continuous
segment geometry. -/
theorem localRoutes_isSimple_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
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
      (localRoutes source clauseIndex literalIndex) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  rcases formulaClauseMetadata_lookup_valid_embedded
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have metadataSourceMember :
      metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth :
      metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, metadataSourceMember, rfl⟩
  have metadataDistinct :
      metadata.sourceClause.AtomsNodup :=
    sourceDistinct metadata.sourceClause metadataSourceMember
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
      (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause,
        metadata.localClauseIndex) ∈
        drawing.formula.zipIdx := by
    rw [drawingFormula]
    exact localClauseMember
  have embeddedLiteralMember :
      ((literal.atom, literal.value), literalIndex) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause).literals.zipIdx := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(literal, literalIndex),
        metadataLiteralMember, rfl⟩
  have drawingValid :
      drawing.IsValid :=
    instantiatedDrawing_isValid
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth metadataDistinct
  have selectedSimple :=
    drawing.embeddedRoute_isSimple_of_members
      drawingValid.2.2
      embeddedClauseMember embeddedLiteralMember
  simpa [localRoutes, metadataLookup, drawing] using
    selectedSimple

/-- Distinct final incidences belonging to the same original source clause
inherit complete continuous separation from their common composed finite
drawing. -/
theorem localRoutes_avoidEachOther_of_members_of_same_source
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {firstClause secondClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    {firstMetadata secondMetadata : ClauseMetadata Variable}
    (firstLookup :
      (formulaClauseMetadata source)[firstClauseIndex]? =
        some firstMetadata)
    (secondLookup :
      (formulaClauseMetadata source)[secondClauseIndex]? =
        some secondMetadata)
    (sameSource :
      firstMetadata.sourceClauseIndex =
        secondMetadata.sourceClauseIndex)
    (incidencesDistinct :
      firstClauseIndex ≠ secondClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (localRoutes source firstClauseIndex firstLiteralIndex)
      (localRoutes source secondClauseIndex secondLiteralIndex) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  rcases formulaClauseMetadata_lookup_valid_embedded
      source firstClauseMember with
    ⟨actualFirst, actualFirstLookup, firstClauseEqual,
      firstSourceMember, firstLocalMember⟩
  have actualFirstEqual : actualFirst = firstMetadata := by
    apply Option.some.inj
    exact actualFirstLookup.symm.trans firstLookup
  subst actualFirst
  rcases formulaClauseMetadata_lookup_valid_embedded
      source secondClauseMember with
    ⟨actualSecond, actualSecondLookup, secondClauseEqual,
      secondSourceMember, secondLocalMember⟩
  have actualSecondEqual : actualSecond = secondMetadata := by
    apply Option.some.inj
    exact actualSecondLookup.symm.trans secondLookup
  subst actualSecond
  have firstMetadataMember :
      firstMetadata ∈ formulaClauseMetadata source := by
    rcases List.getElem?_eq_some_iff.mp firstLookup with
      ⟨firstIndexLt, firstAt⟩
    rw [← firstAt]
    exact List.getElem_mem firstIndexLt
  have secondMetadataMember :
      secondMetadata ∈ formulaClauseMetadata source := by
    rcases List.getElem?_eq_some_iff.mp secondLookup with
      ⟨secondIndexLt, secondAt⟩
    rw [← secondAt]
    exact List.getElem_mem secondIndexLt
  have sameBlock :=
    formulaClauseMetadata_sourceBlock_eq
      source firstMetadataMember secondMetadataMember sameSource
  have localIncidencesDistinct :
      firstMetadata.localClauseIndex ≠
          secondMetadata.localClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex := by
    rcases incidencesDistinct with
      clauseIndicesDistinct | literalIndicesDistinct
    · left
      intro localIndicesEqual
      apply clauseIndicesDistinct
      apply formulaClauseMetadata_lookup_key_injective
        source firstLookup secondLookup
      exact Prod.ext sameSource localIndicesEqual
    · exact Or.inr literalIndicesDistinct
  have firstSourceClauseMember :
      firstMetadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx firstSourceMember
  have firstWidth :
      firstMetadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth firstMetadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨firstMetadata.sourceClause,
        firstSourceClauseMember, rfl⟩
  have firstDistinct :
      firstMetadata.sourceClause.AtomsNodup :=
    sourceDistinct
      firstMetadata.sourceClause firstSourceClauseMember
  let firstDrawing :=
    instantiatedDrawing
      firstMetadata.sourceClauseIndex
      firstMetadata.figureNineClauseStart
      firstMetadata.sourceClause
  let secondDrawing :=
    instantiatedDrawing
      secondMetadata.sourceClauseIndex
      secondMetadata.figureNineClauseStart
      secondMetadata.sourceClause
  have drawingsEqual : firstDrawing = secondDrawing := by
    simp [firstDrawing, secondDrawing,
      sameSource, sameBlock.1, sameBlock.2]
  have firstDrawingFormula :
      firstDrawing.formula =
        composedClauseGadget
          firstMetadata.sourceClauseIndex
          firstMetadata.figureNineClauseStart
          firstMetadata.sourceClause :=
    instantiatedDrawing_formula
      firstMetadata.sourceClauseIndex
      firstMetadata.figureNineClauseStart
      firstMetadata.sourceClause firstWidth
  have secondWidth :
      secondMetadata.sourceClause.literals.length ≤ 3 := by
    simpa [← sameBlock.1] using firstWidth
  have secondDrawingFormula :
      secondDrawing.formula =
        composedClauseGadget
          secondMetadata.sourceClauseIndex
          secondMetadata.figureNineClauseStart
          secondMetadata.sourceClause :=
    instantiatedDrawing_formula
      secondMetadata.sourceClauseIndex
      secondMetadata.figureNineClauseStart
      secondMetadata.sourceClause secondWidth
  have firstEmbeddedClauseMember :
      (PlanarOneInThreeNoUnits.embedPositionedClause
          firstMetadata.clause,
        firstMetadata.localClauseIndex) ∈
        firstDrawing.formula.zipIdx := by
    rw [firstDrawingFormula]
    exact firstLocalMember
  have secondEmbeddedClauseMember :
      (PlanarOneInThreeNoUnits.embedPositionedClause
          secondMetadata.clause,
        secondMetadata.localClauseIndex) ∈
        secondDrawing.formula.zipIdx := by
    rw [secondDrawingFormula]
    exact secondLocalMember
  have firstMetadataLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstMetadata.clause.literals.zipIdx := by
    simpa [firstClauseEqual] using firstLiteralMember
  have secondMetadataLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondMetadata.clause.literals.zipIdx := by
    simpa [secondClauseEqual] using secondLiteralMember
  have firstEmbeddedLiteralMember :
      ((firstLiteral.atom, firstLiteral.value),
          firstLiteralIndex) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          firstMetadata.clause).literals.zipIdx := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(firstLiteral, firstLiteralIndex),
        firstMetadataLiteralMember, rfl⟩
  have secondEmbeddedLiteralMember :
      ((secondLiteral.atom, secondLiteral.value),
          secondLiteralIndex) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          secondMetadata.clause).literals.zipIdx := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(secondLiteral, secondLiteralIndex),
        secondMetadataLiteralMember, rfl⟩
  have firstDrawingValid :
      firstDrawing.IsValid :=
    instantiatedDrawing_isValid
      firstMetadata.sourceClauseIndex
      firstMetadata.figureNineClauseStart
      firstMetadata.sourceClause firstWidth firstDistinct
  rw [← drawingsEqual] at secondEmbeddedClauseMember
  have selectedSeparated :=
    firstDrawing.embeddedRoutes_avoidEachOther_of_members
      firstDrawingValid.2.2
      firstEmbeddedClauseMember secondEmbeddedClauseMember
      firstEmbeddedLiteralMember secondEmbeddedLiteralMember
      localIncidencesDistinct
  simpa [localRoutes, firstLookup, secondLookup,
    firstDrawing, secondDrawing, ← drawingsEqual] using
      selectedSeparated

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
