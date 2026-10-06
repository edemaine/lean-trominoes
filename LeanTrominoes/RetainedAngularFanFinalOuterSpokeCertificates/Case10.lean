/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalOuterSpokeCertificateData

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem outerCenteredLocalCheck_case10 : outerCenteredLocalCheck (.routedClause .right) = true := by
  decide +kernel

theorem outerCenteredStubCheck_case10 : outerCenteredStubCheck (.routedClause .right) = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
