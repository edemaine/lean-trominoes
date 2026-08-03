import LeanTrominoes.RetainedAngularFanFinalDirectSourceRouteChoicePairs
import LeanTrominoes.PeriodicCNFPlanarRetainedCertificate

/-!
# Uniform direct-source selection within a final clause

The final selector first chooses one canonical retained metadata
representative for the whole clause, then selects a direct-source atlas
route at a literal index.  Consequently, if selection succeeds at one
literal, that representative is a direct crossover, routed-clause, or
routed-variable component.  Every other genuine literal of the same final
clause therefore also has a successful checked direct-source choice.

This closes the selector case split needed to turn pairwise direct-route
separation into an unconditional same-clause route-family theorem.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 400000

/-- A physical witness whose retained metadata comes from one of the three
direct component families reconstructs a successful choice for the
corresponding final route.  This is the witness-level converse needed to
interpret failure of the checked final selector. -/
theorem
    exists_finalDirectSourceRouteChoice_of_witness_directCases
    {Variable : Type*} [variableDecEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (directCases :
      (∃ crossing localClauseIndex,
          witness.metadata.source =
            .crossover crossing localClauseIndex) ∨
        (∃ site,
          witness.metadata.source = .routedClause site) ∨
        (∃ site armIndex arm link localClauseIndex,
          witness.metadata.source =
            .routedVariable
              site armIndex arm link localClauseIndex)) :
    ∃ choice,
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice := by
  rcases
      LeanTrominoes.PeriodicEightOccurrenceSplit.DrawingPlanarSATClauseMetadata.exists_retainedDirectSourceRouteChoice
        witness.metadata
        witness.metadata_retainedValid
        witness.literalMember directCases with
    ⟨rawChoice, rawLookup, _rawMatches⟩
  let translation :=
    retainedFinalDirectSourceMetadataTranslation
      formula witness.metadata
  let choice :=
    rawChoice.translateOrigin translation
  have rawRepresents :=
    retainedDirectSourceRouteChoice?_represents_of_eq_some
      formula witness.metadata.source literalIndex
      rawChoice rawLookup
  have localRouteEq :
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
          (metadataPhysicalIncidence witness.metadata
            witness.metadataIndex witness.literal
            literalIndex) =
        (witness.metadata.source.incidenceDrawing formula).routes
          witness.metadata.source.localClauseIndex
          literalIndex := by
    simp [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
      retainedDrawingPlanarSATLocalIncidenceRoutes,
      metadataPhysicalIncidence,
      EmbeddedCNFIncidenceDrawing.routeAt,
      witness.metadataLookup]
  have witnessRouteEq :
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula clauseIndex literalIndex =
        translatePolyline translation
          ((witness.metadata.source.incidenceDrawing formula).routes
            witness.metadata.source.localClauseIndex
            literalIndex) := by
    have routeEq := witness.routeEq
    unfold finalGaugedRouteOccurrence
      metadataPhysicalRouteOccurrence at routeEq
    let placement :=
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
    let backwards := placement.translation (Cell.neg shift)
    have shifted :=
      congrArg (translatePolyline backwards) routeEq
    have leftCancel :
        Cell.add (placement.translation shift) backwards = (0, 0) := by
      rcases shift with ⟨shiftX, shiftY⟩
      simp [placement, backwards,
        PeriodicVariablePlacement.translation,
        Cell.neg, Cell.sub, Cell.add, Cell.scale]
    have rightReduce :
        Cell.add
            (placement.translation
              (Cell.sub shift
                (PeriodicCNF.clauseAnchor
                  (metadataGaugedPositionedClause
                    formula witness.metadata).literals)))
            backwards =
          placement.translation
            (Cell.sub (0, 0)
              (PeriodicCNF.clauseAnchor
                (metadataGaugedPositionedClause
                  formula witness.metadata).literals)) := by
      rcases shift with ⟨shiftX, shiftY⟩
      rcases anchorEq :
          PeriodicCNF.clauseAnchor
            (metadataGaugedPositionedClause
              formula witness.metadata).literals with
        ⟨anchorX, anchorY⟩
      simp [placement, backwards,
        PeriodicVariablePlacement.translation,
        Cell.neg, Cell.sub, Cell.add, Cell.scale]
      constructor <;> ring
    rw [translatePolyline_add, leftCancel, translatePolyline_zero,
      translatePolyline_add, rightReduce] at shifted
    rw [localRouteEq] at shifted
    simpa [translation,
      retainedFinalDirectSourceMetadataTranslation,
      placement] using shifted
  have represents :
      choice.RepresentsFinalRoute
        formula clauseIndex literalIndex := by
    unfold RetainedDirectSourceRouteChoice.RepresentsFinalRoute
    rw [witnessRouteEq]
    unfold choice RetainedDirectSourceRouteChoice.translateOrigin
    simp only
    rw [← rawRepresents]
    rw [translatePolyline_add]
    apply congrArg₂ translatePolyline
    · rcases translation with ⟨tx, ty⟩
      rcases rawChoice.origin with ⟨ox, oy⟩
      simp [Cell.add]
      constructor <;> ring
    · rfl
  have wrappedDecidableEqEq :
      (@instDecidableEqWrappedPeriodicVariable
          (PeriodicPlanarSATVariable Variable)
          (@instDecidableEqPeriodicPlanarSATVariable
            Variable variableDecEq)) =
        (@drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq
          Variable variableDecEq) := by
    funext first second
    exact Subsingleton.elim _ _
  have representativeLookup :=
    witness.representativeMetadataLookup
  rw [wrappedDecidableEqEq] at representativeLookup
  refine ⟨choice, ?_⟩
  exact
    retainedFinalDirectSourceRouteChoice_eq_some_of_lookups
      formula clauseIndex literalIndex
      witness.finalClause witness.metadata
      rawChoice witness.finalClauseLookup
      representativeLookup rawLookup represents

/-- If the checked direct-source selector succeeds for one literal of a
final clause, it succeeds for every genuine literal of that clause. -/
theorem retainedFinalDirectSourceRouteChoice_exists_of_sameClause_choice_some
    {Variable : Type*} [variableDecEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ clause.literals.zipIdx)
    (firstChoice : RetainedDirectSourceRouteChoice)
    (firstChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex firstLiteralIndex =
        some firstChoice) :
    ∃ secondChoice,
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex secondLiteralIndex =
        some secondChoice := by
  have graphWellFormed :
      formula.incidenceGraph.IsWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed formula
  have graphDegree :
      formula.incidenceGraph.DegreeAtMost 3 :=
    PeriodicCNF.incidenceGraph_degreeAtMost
      sourceWidth sourceOccurrences
  have graphLocal :
      formula.incidenceGraph.IsLocal :=
    PeriodicCNF.incidenceGraph_isLocal sourceLocal
  have retainedClausesNonempty :
      ∀ retainedClause ∈ retainedDrawingPlanarSATFormula formula,
        retainedClause.literals ≠ [] :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  rcases
      exists_retainedPhysicalIncidence_of_finalRouteOccurrence
        formula graphWellFormed graphDegree graphLocal
        retainedClausesNonempty
        (clause, clauseIndex) clauseMember
        (secondLiteral, secondLiteralIndex) secondLiteralMember
        (0, 0) with
    ⟨secondWitness⟩
  rcases retainedFinalDirectSourceRouteChoice_exists_raw
      formula clauseIndex firstLiteralIndex
      firstChoice firstChoiceLookup with
    ⟨firstMetadata, _firstRawChoice, firstMetadataLookup,
      firstRawLookup, _firstChoiceEq⟩
  have finalClauseLookup :
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses[clauseIndex]? = some clause :=
    (List.mem_zipIdx_iff_getElem?
      (x := (clause, clauseIndex))
      (l :=
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses)).mp clauseMember
  have witnessClauseEq : secondWitness.finalClause = clause :=
    Option.some.inj
      (secondWitness.finalClauseLookup.symm.trans finalClauseLookup)
  have secondRepresentativeLookup :=
    secondWitness.representativeMetadataLookup
  rw [witnessClauseEq] at secondRepresentativeLookup
  have wrappedDecidableEqEq :
      (@instDecidableEqWrappedPeriodicVariable
          (PeriodicPlanarSATVariable Variable)
          (@instDecidableEqPeriodicPlanarSATVariable
            Variable variableDecEq)) =
        (@drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq
          Variable variableDecEq) := by
    funext first second
    exact Subsingleton.elim _ _
  rw [wrappedDecidableEqEq] at secondRepresentativeLookup
  have firstRepresentativeLookup := firstMetadataLookup
  unfold retainedFinalDirectSourceMetadata? at firstRepresentativeLookup
  rw [finalClauseLookup] at firstRepresentativeLookup
  simp only at firstRepresentativeLookup
  have metadataEq : firstMetadata = secondWitness.metadata := by
    rw [firstRepresentativeLookup] at secondRepresentativeLookup
    exact Option.some.inj secondRepresentativeLookup
  subst firstMetadata
  have directCases :
      (∃ crossing localClauseIndex,
          secondWitness.metadata.source =
            .crossover crossing localClauseIndex) ∨
        (∃ site,
          secondWitness.metadata.source = .routedClause site) ∨
        (∃ site armIndex arm link localClauseIndex,
          secondWitness.metadata.source =
            .routedVariable
              site armIndex arm link localClauseIndex) := by
    cases sourceEq : secondWitness.metadata.source with
    | crossover crossing localClauseIndex =>
        exact Or.inl ⟨crossing, localClauseIndex, rfl⟩
    | carrier link localClauseIndex =>
        simp [sourceEq, retainedDirectSourceRouteChoice?] at firstRawLookup
    | bend routeBend localClauseIndex =>
        simp [sourceEq, retainedDirectSourceRouteChoice?] at firstRawLookup
    | routedClause site =>
        exact Or.inr (Or.inl ⟨site, rfl⟩)
    | routedVariable site armIndex arm link localClauseIndex =>
        exact Or.inr (Or.inr
          ⟨site, armIndex, arm, link, localClauseIndex, rfl⟩)
  exact
    exists_finalDirectSourceRouteChoice_of_witness_directCases
      formula secondWitness directCases

end PeriodicEightOccurrenceSplit
end LeanTrominoes
