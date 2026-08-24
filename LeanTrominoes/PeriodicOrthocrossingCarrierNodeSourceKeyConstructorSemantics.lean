/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyTagSemantics

/-! # Constructor separation by compact carrier-node source tags -/

namespace LeanTrominoes.PeriodicOrthocrossing

open CarrierNodeSourceKeys

/-- Terminal tags `0,1` and boundary tags `2,…,5` make the two carrier-node
constructors disjoint in the compact source-key representation. -/
theorem terminal_sourceKeyPair_ne_boundary
    (terminal : SegmentTerminal) (boundary : CrossingBoundary) :
    pair (CarrierNode.terminal terminal) ≠
      pair (CarrierNode.boundary boundary) := by
  intro equal
  have taggedEqual :
      taggedKey terminal.carrierKey (segmentEndTag terminal.endpoint) =
        taggedKey (firstCrossingKey boundary)
          (crossingSideTag boundary.side) := by
    simpa [pair] using congrArg Prod.fst equal
  have recovered := taggedKey_eq _ _ _ _
    (segmentEndTag_lt_eight terminal.endpoint)
    (crossingSideTag_lt_eight boundary.side) taggedEqual
  exact (segmentEndTag_ne_crossingSideTag
    terminal.endpoint boundary.side) recovered.2

end LeanTrominoes.PeriodicOrthocrossing
