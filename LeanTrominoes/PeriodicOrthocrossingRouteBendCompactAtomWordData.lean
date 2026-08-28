/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyData
import LeanTrominoes.PeriodicOrthocrossingPlanarBends

/-! # Compact occurrence atom words of routed bends -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open CarrierNodeSourceKeys

/-- Compact retained-atom word of one segment terminal. -/
def SegmentTerminal.compactAtomWord
    (terminal : SegmentTerminal) : List Bool :=
  [false, false] ++ CarrierKeyWords.word
    (taggedKey terminal.carrierKey (segmentEndTag terminal.endpoint))

/-- Clause-major compact atom-word block contributed by one bend equality. -/
def RouteBend.compactAtomWords
    (routeBend : RouteBend) : List (List Bool) :=
  [routeBend.incomingTerminal.compactAtomWord,
    routeBend.outgoingTerminal.compactAtomWord,
    routeBend.incomingTerminal.compactAtomWord,
    routeBend.outgoingTerminal.compactAtomWord]

end PeriodicOrthocrossing
end LeanTrominoes
