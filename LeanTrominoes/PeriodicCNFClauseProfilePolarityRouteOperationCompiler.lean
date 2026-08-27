/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFClauseProfilePolarityRouteOperationData

/-! # Compiler for finite polarity route-operation schedules -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace ClauseProfilePolarityRouteOperation

open UnaryProgramClauseProfile

/-- A fixed finite block transducer emits the exact source-slot and operation
descriptor of every polarity-normalized incidence. -/
noncomputable def streamComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List ClauseProfile) (List Descriptor)
      ClauseProfile Descriptor id id stream :=
  FiniteBlockTransducer.computableInPolyTime descriptors

end ClauseProfilePolarityRouteOperation
end PeriodicCNF
end LeanTrominoes

end
