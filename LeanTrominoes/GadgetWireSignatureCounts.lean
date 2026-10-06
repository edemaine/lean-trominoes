/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.GadgetGeometricSearch

/-! # Kernel-checked boundary signature counts for the red wires -/

namespace LeanTrominoes.Gadget

/-- Before neighboring gadgets impose compatibility, the L-wire window has
thirteen geometric boundary signatures. -/
theorem figure11RedWire_boundarySignatureCount :
    (boundarySignatures .L figure11RedWire.window
      figure11RedWire.region).card = 13 := by
  rw [← geometricBoundarySignatures_eq .L figure11RedWire
    figure11RedWire_wellFormed figure11RedWireCells rfl]
  decide +kernel

/-- Before neighboring gadgets impose compatibility, the I-wire window has
five geometric boundary signatures. -/
theorem figure12RedWire_boundarySignatureCount :
    (boundarySignatures .I figure12RedWire.window
      figure12RedWire.region).card = 5 := by
  rw [← geometricBoundarySignatures_eq .I figure12RedWire
    figure12RedWire_wellFormed figure12RedWireCells rfl]
  decide +kernel

end LeanTrominoes.Gadget
