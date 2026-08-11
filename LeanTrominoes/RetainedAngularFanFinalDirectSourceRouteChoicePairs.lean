import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoicePairs
import LeanTrominoes.RetainedAngularFanFinalDirectSourceRouteChoice

/-!
# Pairwise separation for final direct-source route choices

The final direct-source selector reaches a raw component atlas through two
quotients: clause-anchor normalization and duplicate-clause representative
selection.  This module inverts a successful final lookup far enough to
recover its canonical raw metadata and atlas choice.

Because the metadata representative is a deterministic function of the
final clause index, two choices for that clause recover one common raw
source and one common physical translation.  Distinct literal indices then
use the raw atlas pair theorem, and common translation preserves both route
avoidance and head-only contact.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- Every successful raw selector lookup carries the terminal-direction
matching contract of its selected atlas entry. -/
theorem retainedDirectSourceRouteChoice?_matches_of_eq_some
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (lookup :
      retainedDirectSourceRouteChoice? formula source literalIndex =
        some choice) :
    choice.Matches formula source literalIndex := by
  cases source with
  | crossover crossing localClauseIndex =>
      simp only [retainedDirectSourceRouteChoice?] at lookup
      split at lookup
      next localClauseIndexLt =>
        split at lookup
        next literalIndexLt =>
          simp only [Option.some.injEq] at lookup
          subst choice
          simpa [RetainedDirectSourceRouteChoice.Matches,
            DrawingPlanarSATClauseSource.incidenceDrawing,
            DrawingPlanarSATClauseSource.localClauseIndex] using
            retainedDirectCrossoverPrefixChoice_positionedDirection
              formula crossing
              ⟨localClauseIndex, localClauseIndexLt⟩
              ⟨literalIndex, literalIndexLt⟩
        next => contradiction
      next => contradiction
  | carrier link localClauseIndex =>
      simp [retainedDirectSourceRouteChoice?] at lookup
  | bend routeBend localClauseIndex =>
      simp [retainedDirectSourceRouteChoice?] at lookup
  | routedClause site =>
      simp only [retainedDirectSourceRouteChoice?] at lookup
      split at lookup
      next literalIndexLt =>
        simp only [Option.some.injEq] at lookup
        subst choice
        simpa [RetainedDirectSourceRouteChoice.Matches,
          DrawingPlanarSATClauseSource.incidenceDrawing,
          DrawingPlanarSATClauseSource.localClauseIndex] using
          retainedDirectRoutedClauseArmChoice_positionedDirection
            formula site ⟨literalIndex, literalIndexLt⟩
      next => contradiction
  | routedVariable site armIndex arm link localClauseIndex =>
      simp only [retainedDirectSourceRouteChoice?] at lookup
      split at lookup
      next localClauseIndexLt =>
        split at lookup
        next literalIndexLt =>
          simp only [Option.some.injEq] at lookup
          subst choice
          simpa [RetainedDirectSourceRouteChoice.Matches,
            DrawingPlanarSATClauseSource.incidenceDrawing,
            DrawingPlanarSATClauseSource.localClauseIndex] using
            retainedDirectDuplicatorPrefixChoice_positionedDirection
              formula site arm link
              ⟨localClauseIndex, localClauseIndexLt⟩
              ⟨literalIndex, literalIndexLt⟩
        next => contradiction
      next => contradiction

/-- Translating a component origin translates its entire coordinated route
by the corresponding fully scaled physical offset. -/
theorem RetainedDirectSourceRouteChoice.translateOrigin_completeRoute
    (choice : RetainedDirectSourceRouteChoice)
    (offset : Cell)
    (slot : RetainedTerminalSlot) :
    (choice.translateOrigin offset).completeRoute slot =
      translatePolyline
        (retainedDirectSourceFanPositioningOffset offset)
        (choice.completeRoute slot) := by
  rw [RetainedDirectSourceRouteChoice.completeRoute,
    RetainedDirectSourceRouteChoice.completeRoute,
    retainedDirectSourcePositionedFanCompleteRouteAt,
    retainedDirectSourcePositionedFanCompleteRouteAt,
    translatePolyline_add]
  apply congrArg₂ translatePolyline
  · rcases choice with ⟨origin, kind, index⟩
    rcases origin with ⟨originX, originY⟩
    rcases offset with ⟨offsetX, offsetY⟩
    simp [RetainedDirectSourceRouteChoice.translateOrigin,
      retainedDirectSourceFanPositioningOffset,
      Cell.add, Cell.scale]
    constructor <;> ring
  · rfl

/-- Invert the metadata-level selector to its raw atlas choice. -/
theorem retainedFinalDirectSourceRouteChoiceFromMetadata_exists_raw
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literalIndex : Nat)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (choice : RetainedDirectSourceRouteChoice)
    (lookup :
      retainedFinalDirectSourceRouteChoiceFromMetadata?
          formula literalIndex (some metadata) =
        some choice) :
    ∃ rawChoice,
      retainedDirectSourceRouteChoice?
          formula metadata.source literalIndex =
        some rawChoice ∧
      choice =
        rawChoice.translateOrigin
          (retainedFinalDirectSourceMetadataTranslation
            formula metadata) := by
  unfold retainedFinalDirectSourceRouteChoiceFromMetadata? at lookup
  generalize rawLookup :
      retainedDirectSourceRouteChoice?
        formula metadata.source literalIndex = rawChoice? at lookup
  cases rawChoice? with
  | none =>
      simp only at lookup
      rw [rawLookup] at lookup
      cases lookup
  | some rawChoice =>
      simp only at lookup
      rw [rawLookup] at lookup
      simp only [Option.some.injEq] at lookup
      subst choice
      exact ⟨rawChoice, rfl, rfl⟩

/-- Every successful final choice comes from the canonical metadata
representative and one successful raw choice, translated by that
representative's physical anchor shift. -/
private theorem retainedFinalDirectSourceCheckedOption_exists_candidate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (candidate? : Option RetainedDirectSourceRouteChoice)
    (choice : RetainedDirectSourceRouteChoice)
    (lookup :
      retainedFinalDirectSourceRouteChoiceSelect?
          formula clauseIndex literalIndex candidate? = some choice) :
    ∃ candidate, candidate? = some candidate ∧ choice = candidate := by
  unfold retainedFinalDirectSourceRouteChoiceSelect? at lookup
  cases candidate? with
  | none =>
      simp only at lookup
      cases lookup
  | some candidate =>
      simp only at lookup
      split at lookup
      next =>
        simp only [Option.some.injEq] at lookup
        subst choice
        exact ⟨candidate, rfl, rfl⟩
      next => cases lookup

private theorem retainedFinalDirectSourceRouteChoiceFromMetadata_exists_input
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literalIndex : Nat)
    (metadata? : Option (DrawingPlanarSATClauseMetadata Variable))
    (choice : RetainedDirectSourceRouteChoice)
    (lookup :
      retainedFinalDirectSourceRouteChoiceFromMetadata?
          formula literalIndex metadata? = some choice) :
    ∃ metadata,
      metadata? = some metadata ∧
      retainedFinalDirectSourceRouteChoiceFromMetadata?
          formula literalIndex (some metadata) = some choice := by
  cases metadata? with
  | none =>
      simp [retainedFinalDirectSourceRouteChoiceFromMetadata?] at lookup
  | some metadata =>
      exact ⟨metadata, rfl, lookup⟩

private theorem retainedFinalDirectSourceRouteChoiceQuery_exists_candidate
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalDirectQuery Variable)
    (candidate? : Option RetainedDirectSourceRouteChoice)
    (candidateEq :
      retainedFinalDirectSourceRouteChoiceCandidate? input = candidate?)
    (choice : RetainedDirectSourceRouteChoice)
    (lookup :
      retainedFinalDirectSourceRouteChoiceQuery? input = some choice) :
    ∃ candidate,
      candidate? = some candidate ∧
      choice = candidate := by
  unfold retainedFinalDirectSourceRouteChoiceQuery? at lookup
  unfold retainedFinalDirectSourceRouteChoiceSelectInput? at lookup
  rw [candidateEq] at lookup
  exact retainedFinalDirectSourceCheckedOption_exists_candidate
    input.1.1 input.1.2 input.2 candidate? choice lookup

private theorem retainedFinalDirectSourceRouteChoiceCandidate_exists_metadata
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalDirectQuery Variable)
    (metadata? : Option (DrawingPlanarSATClauseMetadata Variable))
    (metadataEq :
      retainedFinalDirectSourceMetadata? input.1.1 input.1.2 = metadata?)
    (choice : RetainedDirectSourceRouteChoice)
    (lookup :
      retainedFinalDirectSourceRouteChoiceCandidate? input = some choice) :
    ∃ metadata,
      metadata? = some metadata ∧
      retainedFinalDirectSourceRouteChoiceFromMetadata?
        input.1.1 input.2 (some metadata) = some choice := by
  unfold retainedFinalDirectSourceRouteChoiceCandidate? at lookup
  unfold retainedFinalDirectSourceRouteChoiceCandidateInput at lookup
  unfold retainedFinalDirectSourceRouteChoiceFromMetadataInput? at lookup
  rw [metadataEq] at lookup
  exact retainedFinalDirectSourceRouteChoiceFromMetadata_exists_input
    input.1.1 input.2 metadata? choice lookup

theorem retainedFinalDirectSourceRouteChoice_exists_raw
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (lookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    ∃ (metadata : DrawingPlanarSATClauseMetadata Variable)
      (rawChoice : RetainedDirectSourceRouteChoice),
      retainedFinalDirectSourceMetadata? formula clauseIndex = some metadata ∧
      retainedDirectSourceRouteChoice?
          formula metadata.source literalIndex =
        some rawChoice ∧
      choice =
        rawChoice.translateOrigin
          (retainedFinalDirectSourceMetadataTranslation
            formula metadata) := by
  unfold retainedFinalDirectSourceRouteChoice? at lookup
  rcases retainedFinalDirectSourceRouteChoiceQuery_exists_candidate
      ((formula, clauseIndex), literalIndex)
      (retainedFinalDirectSourceRouteChoiceCandidate?
        ((formula, clauseIndex), literalIndex))
      rfl choice lookup with
    ⟨candidate, candidateLookup, choiceEq⟩
  rcases retainedFinalDirectSourceRouteChoiceCandidate_exists_metadata
      ((formula, clauseIndex), literalIndex)
      (retainedFinalDirectSourceMetadata? formula clauseIndex)
      rfl candidate candidateLookup with
    ⟨metadata, metadataLookup, selectedLookup⟩
  rcases retainedFinalDirectSourceRouteChoiceFromMetadata_exists_raw
      formula literalIndex metadata candidate selectedLookup with
    ⟨rawChoice, rawLookup, candidateEq⟩
  refine ⟨metadata, rawChoice, metadataLookup, rawLookup, ?_⟩
  exact choiceEq.trans candidateEq

/-- Successful direct-source choices for distinct literals of one final
clause have separated complete routes, with their common heads as the only
permitted contact. -/
theorem retainedFinalDirectSourceRouteChoices_completeRoutes_separated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (clauseIndex firstLiteralIndex secondLiteralIndex : Nat)
    (firstChoice secondChoice : RetainedDirectSourceRouteChoice)
    (firstLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex firstLiteralIndex =
        some firstChoice)
    (secondLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex secondLiteralIndex =
        some secondChoice)
    (indicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex)
    (firstSlot secondSlot : RetainedTerminalSlot) :
    RoutesAvoidEachOther
        (firstChoice.completeRoute firstSlot)
        (secondChoice.completeRoute secondSlot) ∧
      RoutesMeetOnlyAtHeads
        (firstChoice.completeRoute firstSlot)
        (secondChoice.completeRoute secondSlot) := by
  rcases retainedFinalDirectSourceRouteChoice_exists_raw
      formula clauseIndex firstLiteralIndex firstChoice firstLookup with
    ⟨firstMetadata, firstRawChoice, firstMetadataLookup,
      firstRawLookup, firstChoiceEq⟩
  rcases retainedFinalDirectSourceRouteChoice_exists_raw
      formula clauseIndex secondLiteralIndex secondChoice secondLookup with
    ⟨secondMetadata, secondRawChoice, secondMetadataLookup,
      secondRawLookup, secondChoiceEq⟩
  have metadataEq : firstMetadata = secondMetadata := by
    apply Option.some.inj
    rw [← firstMetadataLookup, ← secondMetadataLookup]
  subst secondMetadata
  have firstMatches :=
    retainedDirectSourceRouteChoice?_matches_of_eq_some
      formula firstMetadata.source
      firstLiteralIndex firstRawChoice firstRawLookup
  have secondMatches :=
    retainedDirectSourceRouteChoice?_matches_of_eq_some
      formula firstMetadata.source
      secondLiteralIndex secondRawChoice secondRawLookup
  have separated :=
    retainedDirectSourceRouteChoices_completeRoutes_separated
      formula degree firstMetadata.source
      firstLiteralIndex secondLiteralIndex
      firstRawChoice secondRawChoice
      firstRawLookup secondRawLookup
      firstMatches secondMatches indicesDifferent
      firstSlot secondSlot
  subst firstChoice
  subst secondChoice
  rw [RetainedDirectSourceRouteChoice.translateOrigin_completeRoute,
    RetainedDirectSourceRouteChoice.translateOrigin_completeRoute]
  exact
    ⟨separated.1.translate
        (retainedDirectSourceFanPositioningOffset
          (retainedFinalDirectSourceMetadataTranslation
            formula firstMetadata)),
      separated.2.translate
        (retainedDirectSourceFanPositioningOffset
          (retainedFinalDirectSourceMetadataTranslation
            formula firstMetadata))⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
