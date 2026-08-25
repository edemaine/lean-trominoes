/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorHorizontalWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorVerticalWordSemantics

/-! # Correctness witnesses for signed carrier-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyFieldProjector

theorem wordCorrect_horizontalPositive : WordCorrect .horizontalPositive :=
  scan_semanticWord_horizontalPositive

theorem wordCorrect_horizontalNegative : WordCorrect .horizontalNegative :=
  scan_semanticWord_horizontalNegative

theorem wordCorrect_verticalPositive : WordCorrect .verticalPositive :=
  scan_semanticWord_verticalPositive

theorem wordCorrect_verticalNegative : WordCorrect .verticalNegative :=
  scan_semanticWord_verticalNegative

end CarrierKeyFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
