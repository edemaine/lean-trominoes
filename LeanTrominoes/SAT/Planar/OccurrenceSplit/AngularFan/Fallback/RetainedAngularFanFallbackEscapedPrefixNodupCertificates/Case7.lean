/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Fallback.RetainedAngularFanFallbackEscapedPrefixNodupData

namespace LeanTrominoes.PeriodicEightOccurrenceSplit.FallbackSuffixDirectionCompiler
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem escapedFixedPrefixNodupCheck_case7 : escapedFixedPrefixNodupCheck (.compass .northeast) = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit.FallbackSuffixDirectionCompiler
