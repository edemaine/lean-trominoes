/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarTerminals

/-! # Lightweight tags for compact carrier-node source keys -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierNodeSourceKeys

def segmentEndTag : SegmentEnd → Nat
  | .start => 0
  | .finish => 1

def crossingSideTag : CrossingSide → Nat
  | .left => 2
  | .right => 3
  | .top => 4
  | .bottom => 5

end LeanTrominoes.PeriodicOrthocrossing.CarrierNodeSourceKeys
