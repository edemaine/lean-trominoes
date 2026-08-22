/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenData

/-! # Current-slice source-occurrence offset normalization -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteTokens

theorem scan_offsetTokens_zero :
    FiniteStateTransducer.scan transition false
        (SourceOccurrenceTokens.offsetTokens 0) =
      (false, []) := by
  rfl

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteTokens
