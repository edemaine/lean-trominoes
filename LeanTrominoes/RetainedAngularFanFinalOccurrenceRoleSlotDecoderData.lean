/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteRoleSlotUnaryDecoderData
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseOccurrenceRoleData

/-! # Final occurrence-role/slot decoder data -/

noncomputable section

namespace LeanTrominoes.FinalOccurrenceRoleSlotDecoder

open PeriodicEightOccurrenceSplit

abbrev Role := RetainedFinalCopiedClauseOccurrenceRole
abbrev Slot := FiniteRoleSlotUnaryDecoder.Slot
abbrev Pair := Role × Slot

noncomputable def pairs (codes : List Nat) : List Pair :=
  FiniteRoleSlotUnaryDecoder.pairs (Role := Role) codes

end LeanTrominoes.FinalOccurrenceRoleSlotDecoder

end
