/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalDataBlockKeySemantics

/-! # Descriptor semantics of stable-key carrier terminal blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

/-- The descriptor-compiled carrier terminal block stream is exactly its
stable-key presentation. -/
theorem retainedTerminalDataBlocks_eq_keyBlocks
    (descriptors : List RouteDescriptor) :
    retainedTerminalDataBlocks descriptors =
      retainedKeyTerminalDataBlocks descriptors := by
  unfold retainedTerminalDataBlocks retainedKeyTerminalDataBlocks
  exact retainedTerminalDataBlocksFromDatums_eq_keyBlocks _

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
