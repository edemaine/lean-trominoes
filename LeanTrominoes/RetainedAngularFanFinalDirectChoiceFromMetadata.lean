/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectSourceChoiceUniformity

/-! # Recovering a raw direct choice from final metadata

A genuine literal of a final clause whose canonical metadata representative
belongs to a direct component family has a successful final direct choice.
Moreover, that choice is exactly the anchor-normalized translation of the
corresponding raw atlas choice.  This packages the witness construction and
metadata-identification argument shared by the three direct query families.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

set_option maxHeartbeats 400000

/-- Direct canonical metadata at a genuine final literal reconstructs both
the selected final choice and the raw component-atlas choice from which it
was translated. -/
theorem exists_finalDirectChoiceRaw_of_metadata_direct
    {Variable : Type*} [variableDecEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ sourceClause ∈ formula.clauses, sourceClause ≠ [])
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
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (metadataLookup :
      retainedFinalDirectSourceMetadata? formula clauseIndex =
        some metadata)
    (directCases :
      (∃ crossing localClauseIndex,
          metadata.source = .crossover crossing localClauseIndex) ∨
        (∃ site,
          metadata.source = .routedClause site) ∨
        (∃ site armIndex arm link localClauseIndex,
          metadata.source =
            .routedVariable
              site armIndex arm link localClauseIndex)) :
    ∃ choice rawChoice,
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice ∧
      retainedDirectSourceRouteChoice?
          formula metadata.source literalIndex = some rawChoice ∧
      choice =
        rawChoice.translateOrigin
          (retainedFinalDirectSourceMetadataTranslation
            formula metadata) := by
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
  have finalClauseLookup :
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses[clauseIndex]? = some clause :=
    (List.mem_zipIdx_iff_getElem?
      (x := (clause, clauseIndex))
      (l :=
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses)).mp clauseMember
  have witnessClauseEq : witness.finalClause = clause :=
    Option.some.inj
      (witness.finalClauseLookup.symm.trans finalClauseLookup)
  have witnessRepresentativeLookup :=
    witness.representativeMetadataLookup
  rw [witnessClauseEq] at witnessRepresentativeLookup
  have wrappedDecidableEqEq :
      (@instDecidableEqWrappedPeriodicVariable
          (PeriodicPlanarSATVariable Variable)
          (@instDecidableEqPeriodicPlanarSATVariable
            Variable variableDecEq)) =
        (@drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq
          Variable variableDecEq) := by
    funext first second
    exact Subsingleton.elim _ _
  rw [wrappedDecidableEqEq] at witnessRepresentativeLookup
  have representativeLookup := metadataLookup
  unfold retainedFinalDirectSourceMetadata? at representativeLookup
  unfold retainedRepresentativeItem? at representativeLookup
  unfold PositionedPeriodicCNF.representativeItem? at representativeLookup
  rw [finalClauseLookup] at representativeLookup
  simp only at representativeLookup
  rw [wrappedDecidableEqEq] at representativeLookup
  have metadataEq : metadata = witness.metadata := by
    rw [representativeLookup] at witnessRepresentativeLookup
    exact Option.some.inj witnessRepresentativeLookup
  subst metadata
  rcases
      exists_finalDirectSourceRouteChoice_of_witness_directCases
        formula witness directCases with
    ⟨choice, choiceLookup⟩
  rcases
      retainedFinalDirectSourceRouteChoice_exists_raw
        formula clauseIndex literalIndex choice choiceLookup with
    ⟨selectedMetadata, rawChoice, selectedMetadataLookup,
      rawLookup, choiceEq⟩
  have selectedMetadataEq : selectedMetadata = witness.metadata :=
    Option.some.inj
      (selectedMetadataLookup.symm.trans metadataLookup)
  subst selectedMetadata
  exact ⟨choice, rawChoice, choiceLookup, rawLookup, choiceEq⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
