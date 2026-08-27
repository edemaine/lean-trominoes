/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestDropFirst
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Polynomial-time leading trim inside a normalization request -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest
namespace DropFirst

open Computability Turing

noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  change TM2ComputableInPolyTime id id
    (FiniteStateTransducer.output initial transition finish)
  exact FiniteStateTransducer.computableInPolyTime
    initial transition finish

noncomputable def requestTokensComputableInPolyTime :
    TM2ComputableInPolyTime Request.tokens id
      (fun input => (request input).tokens) := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    Request.tokens outputComputableInPolyTime
    (fun _ => rfl) output_request

end DropFirst
end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes

end
