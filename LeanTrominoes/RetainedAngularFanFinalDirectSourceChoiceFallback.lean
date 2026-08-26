/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectSourceRouteChoice

/-! # Final direct-choice rejection for fallback metadata -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- A final clause represented by carrier or bend metadata has no direct
atlas choice at any literal index. -/
theorem retainedFinalDirectSourceRouteChoice_eq_none_of_fallbackMetadata
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (metadataLookup :
      retainedFinalDirectSourceMetadata? formula clauseIndex =
        some metadata)
    (fallbackSource :
      (∃ link localClauseIndex,
          metadata.source = .carrier link localClauseIndex) ∨
        (∃ routeBend localClauseIndex,
          metadata.source = .bend routeBend localClauseIndex)) :
    retainedFinalDirectSourceRouteChoice?
        formula clauseIndex literalIndex = none := by
  unfold retainedFinalDirectSourceRouteChoice?
    retainedFinalDirectSourceRouteChoiceQuery?
    retainedFinalDirectSourceRouteChoiceSelectInput?
    retainedFinalDirectSourceRouteChoiceCandidate?
    retainedFinalDirectSourceRouteChoiceCandidateInput
    retainedFinalDirectSourceRouteChoiceFromMetadataInput?
  rw [metadataLookup]
  rcases fallbackSource with
    ⟨link, localClauseIndex, sourceEq⟩ |
      ⟨routeBend, localClauseIndex, sourceEq⟩
  · simp [retainedFinalDirectSourceRouteChoiceFromMetadata?,
      retainedDirectSourceRouteChoice?, sourceEq,
      retainedFinalDirectSourceRouteChoiceSelect?]
  · simp [retainedFinalDirectSourceRouteChoiceFromMetadata?,
      retainedDirectSourceRouteChoice?, sourceEq,
      retainedFinalDirectSourceRouteChoiceSelect?]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
