/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementCodeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceDirectionCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceElementCodeCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Counted contraction instantiated on the direct final source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCountedContractionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Canonical degree-two/degree-three contraction output assembled from the
complete element, degree, incidence-identity, and incidence-direction
columns of the direct final source. -/
noncomputable def directSourceFinalCountedContractedDirectionTokens
    (symbols : List encoding.Γ) :
    List NormalizationDirectionRequest.Batch.NormalizedToken :=
  CountedContractedIncidence.output
    (directSourceFinalCanonicalElementCodes decider symbols)
    (directSourceFinalCanonicalElementDegrees decider symbols)
    (directSourceFinalCanonicalIncidenceElementCodes decider symbols)
    (directSourceFinalCanonicalIncidenceDirectionTokens decider symbols)

/-- The concrete counted contraction of the direct final source compiles in
polynomial time. -/
noncomputable def
    directSourceFinalCountedContractedDirectionTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCountedContractedDirectionTokens decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCountedContractedDirectionTokens
    exact CountedContractedIncidence.outputComputableInPolyTimeOf
      id
      (directSourceFinalCanonicalElementCodes decider)
      (directSourceFinalCanonicalElementDegrees decider)
      (directSourceFinalCanonicalIncidenceElementCodes decider)
      (directSourceFinalCanonicalIncidenceDirectionTokens decider)
      (directSourceFinalCanonicalElementCodesComputableInPolyTime decider)
      (directSourceFinalCanonicalElementDegreesComputableInPolyTime decider)
      (directSourceFinalCanonicalIncidenceElementCodesComputableInPolyTime
        decider)
      (directSourceFinalCanonicalIncidenceDirectionTokensComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
