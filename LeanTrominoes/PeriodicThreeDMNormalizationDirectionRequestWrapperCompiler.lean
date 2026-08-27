/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestWrapper
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Polynomial-time dynamic template wrappers -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest
namespace Wrapper

open Computability Turing

noncomputable def outputComputableInPolyTime (round : Round) :
    TM2ComputableInPolyTime id id (output round) := by
  change TM2ComputableInPolyTime id id
    (FiniteStateTransducer.output initial (transition round)
      (finish round))
  exact FiniteStateTransducer.computableInPolyTime
    initial (transition round) (finish round)

noncomputable def requestTokensComputableInPolyTime (round : Round) :
    TM2ComputableInPolyTime Request.tokens id
      (fun input => (request round input).tokens) := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    Request.tokens (outputComputableInPolyTime round)
    (fun _ => rfl) (output_request round)

end Wrapper
end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes

end
