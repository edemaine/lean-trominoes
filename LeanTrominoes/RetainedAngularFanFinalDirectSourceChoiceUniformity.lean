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
    ⟨firstMetadata, firstRawChoice, firstMetadataLookup,
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
  have finalRepresentativeLookup :=
    secondWitness.representativeMetadataLookup
  rw [wrappedDecidableEqEq] at finalRepresentativeLookup
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
  rcases
      LeanTrominoes.PeriodicEightOccurrenceSplit.DrawingPlanarSATClauseMetadata.exists_retainedDirectSourceRouteChoice
        secondWitness.metadata
        secondWitness.metadata_retainedValid
        secondWitness.literalMember directCases with
    ⟨secondRawChoice, secondRawLookup, _secondMatches⟩
  let translation :=
    retainedFinalDirectSourceMetadataTranslation
      formula secondWitness.metadata
  let secondChoice :=
    secondRawChoice.translateOrigin translation
  have rawRepresents :=
    retainedDirectSourceRouteChoice?_represents_of_eq_some
      formula secondWitness.metadata.source secondLiteralIndex
      secondRawChoice secondRawLookup
  have localRouteEq :
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
          (metadataPhysicalIncidence secondWitness.metadata
            secondWitness.metadataIndex secondWitness.literal
            secondLiteralIndex) =
        (secondWitness.metadata.source.incidenceDrawing formula).routes
          secondWitness.metadata.source.localClauseIndex
          secondLiteralIndex := by
    simp [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
      retainedDrawingPlanarSATLocalIncidenceRoutes,
      metadataPhysicalIncidence,
      EmbeddedCNFIncidenceDrawing.routeAt,
      secondWitness.metadataLookup]
  have witnessRouteEq :
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula clauseIndex secondLiteralIndex =
        translatePolyline translation
          ((secondWitness.metadata.source.incidenceDrawing formula).routes
            secondWitness.metadata.source.localClauseIndex
            secondLiteralIndex) := by
    have routeEq := secondWitness.routeEq
    unfold finalGaugedRouteOccurrence
      metadataPhysicalRouteOccurrence at routeEq
    have zeroTranslation :
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation (0, 0) = (0, 0) := by
      simp [PeriodicVariablePlacement.translation, Cell.scale]
    rw [zeroTranslation] at routeEq
    have translatePolyline_zero (points : List Cell) :
        translatePolyline (0, 0) points = points := by
      induction points with
      | nil => rfl
      | cons point points induction =>
          change
            List.map (Cell.add (0, 0)) points = points at induction
          simp only [translatePolyline, List.map_cons]
          rw [induction]
          simp [Cell.add]
    rw [translatePolyline_zero] at routeEq
    rw [localRouteEq] at routeEq
    simpa [translation,
      retainedFinalDirectSourceMetadataTranslation] using routeEq
  have represents :
      secondChoice.RepresentsFinalRoute
        formula clauseIndex secondLiteralIndex := by
    unfold RetainedDirectSourceRouteChoice.RepresentsFinalRoute
    rw [witnessRouteEq]
    unfold secondChoice RetainedDirectSourceRouteChoice.translateOrigin
    simp only
    rw [← rawRepresents]
    rw [translatePolyline_add]
    apply congrArg₂ translatePolyline
    · rcases translation with ⟨tx, ty⟩
      rcases secondRawChoice.origin with ⟨ox, oy⟩
      simp [Cell.add]
      constructor <;> ring
    · rfl
  refine ⟨secondChoice, ?_⟩
  exact
    retainedFinalDirectSourceRouteChoice_eq_some_of_lookups
      formula clauseIndex secondLiteralIndex
      secondWitness.finalClause secondWitness.metadata
      secondRawChoice secondWitness.finalClauseLookup
      finalRepresentativeLookup
      secondRawLookup represents

end PeriodicEightOccurrenceSplit
end LeanTrominoes
