import LeanTrominoes.RetainedAngularFanFinalDirectSourceChoiceUniformity

/-!
# Classifying failed final direct-source choices

A genuine copied-source incidence always has a physical retained-metadata
representative.  The three direct metadata families reconstruct a successful
checked final choice, so failure at such an incidence leaves exactly the two
fallback component families: a retained carrier lens or a route-bend corner.

This is the selector-to-geometry bridge used by the fallback same-clause
separation proof.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PlanarThreeSAT

set_option maxHeartbeats 400000

/-- A failed checked choice at a genuine final incidence has a physical
route witness whose metadata source is a carrier or a bend. -/
theorem
    exists_carrier_or_bend_witness_of_finalDirectSourceRouteChoice_none
    {Variable : Type*} [DecidableEq Variable]
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
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none) :
    ∃ witness :
        FinalGaugedRouteOccurrenceWitness
          formula clauseIndex literalIndex (0, 0),
      (∃ link localClauseIndex,
          witness.metadata.source =
            .carrier link localClauseIndex) ∨
        (∃ routeBend localClauseIndex,
          witness.metadata.source =
            .bend routeBend localClauseIndex) := by
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
        (literal, literalIndex) literalMember
        (0, 0) with
    ⟨witness⟩
  refine ⟨witness, ?_⟩
  cases sourceEq : witness.metadata.source with
  | crossover crossing localClauseIndex =>
      rcases
          exists_finalDirectSourceRouteChoice_of_witness_directCases
            formula witness
            (Or.inl ⟨crossing, localClauseIndex, sourceEq⟩) with
        ⟨choice, choiceSome⟩
      rw [choiceNone] at choiceSome
      cases choiceSome
  | carrier link localClauseIndex =>
      exact Or.inl ⟨link, localClauseIndex, rfl⟩
  | bend routeBend localClauseIndex =>
      exact Or.inr ⟨routeBend, localClauseIndex, rfl⟩
  | routedClause site =>
      rcases
          exists_finalDirectSourceRouteChoice_of_witness_directCases
            formula witness
            (Or.inr (Or.inl ⟨site, sourceEq⟩)) with
        ⟨choice, choiceSome⟩
      rw [choiceNone] at choiceSome
      cases choiceSome
  | routedVariable site armIndex arm link localClauseIndex =>
      rcases
          exists_finalDirectSourceRouteChoice_of_witness_directCases
            formula witness
            (Or.inr (Or.inr
              ⟨site, armIndex, arm, link,
                localClauseIndex, sourceEq⟩)) with
        ⟨choice, choiceSome⟩
      rw [choiceNone] at choiceSome
      cases choiceSome

end PeriodicEightOccurrenceSplit
end LeanTrominoes
