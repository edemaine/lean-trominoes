/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestExpansion
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Polynomial-time request direction expansion -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest

open Computability Turing

noncomputable def expandDirectionTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id expandDirectionTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens : List Token => tokens.flatMap expansionBlock)
  exact FiniteBlockTransducer.computableInPolyTime expansionBlock

/-- From a canonically encoded request, expand only its route directions by
the normalization factor while retaining the six tagged choices. -/
noncomputable def expandRequestTokensComputableInPolyTime :
    TM2ComputableInPolyTime Request.tokens id
      (fun request => (expandRequest request).tokens) := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    Request.tokens expandDirectionTokensComputableInPolyTime
    (fun _ => rfl) expandDirectionTokens_request

end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes

end
