/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitData
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time finite clause-profile occurrence splitting -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace ClauseProfileOccurrenceSplit

open UnaryProgramClauseProfile

noncomputable def generatedProfilesComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List ClauseProfile) (List ClauseProfile)
      ClauseProfile ClauseProfile id id generatedProfiles := by
  let generated := TM2CompositionMachine.computableInPolyTime
    (IndexedTemplateEmitterMachine.computableInPolyTime cycleFamily)
    (FiniteBlockTransducer.computableInPolyTime decodeItem)
  exact generated

/-- Copying the source profiles and appending one implication profile per
literal is polynomial time. -/
noncomputable def profilesComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List ClauseProfile) (List ClauseProfile)
      ClauseProfile ClauseProfile id id profiles :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    generatedProfilesComputableInPolyTime generatedProfiles_eq

end ClauseProfileOccurrenceSplit
end PeriodicCNF
end LeanTrominoes
