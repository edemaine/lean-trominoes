/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalDataBlockKeyDescriptorSemantics

/-! # Flattened stable-key semantics of compiled carrier terminal blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

/-- Flattened stable-key presentation of the selected carrier terminal-data
column. -/
def retainedKeyTerminalData
    (descriptors : List RouteDescriptor) :
    List PeriodicEightOccurrenceSplit.RetainedTerminalData :=
  (retainedKeyTerminalDataBlocks descriptors).flatten

/-- Flattening the sparse carrier terminal stream gives the exact terminal
column selected inside the stable semantic key blocks. -/
theorem retainedTerminalDataBlocks_flatten_eq_keyBlocks
    (descriptors : List RouteDescriptor) :
    (retainedTerminalDataBlocks descriptors).flatten =
      retainedKeyTerminalData descriptors := by
  exact congrArg List.flatten
    (retainedTerminalDataBlocks_eq_keyBlocks descriptors)

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
