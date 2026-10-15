/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computation.Encoding.Bounded.BoundedDelimitedDirectionCancellationOppositeRunData

namespace LeanTrominoes.BoundedDelimitedDirectionCancellation
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem oppositeRunCheck_east : oppositeRunCheck .east = true := by
  decide +kernel

end LeanTrominoes.BoundedDelimitedDirectionCancellation
