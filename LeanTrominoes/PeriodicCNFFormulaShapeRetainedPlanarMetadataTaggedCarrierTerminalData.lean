/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalColumnData

/-! # Boolean-tagged carrier terminal data -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicEightOccurrenceSplit

/-- Terminal datum selected by one direction of a carrier implication. -/
def carrierLensRouteTerminalDataTagged
    (horizontal : Bool) (span : Int)
    (direction : Bool) (literalIndex : Nat) : RetainedTerminalData :=
  carrierLensRouteTerminalData horizontal span
    (if direction then 0 else 1) literalIndex

/-- Scanning both tagged implications in clause-major order gives the
canonical four-incidence terminal block. -/
theorem carrierLensRouteTerminalDataTagged_block_eq
    (horizontal : Bool) (span : Int) :
    [carrierLensRouteTerminalDataTagged horizontal span true 0,
      carrierLensRouteTerminalDataTagged horizontal span true 1,
      carrierLensRouteTerminalDataTagged horizontal span false 0,
      carrierLensRouteTerminalDataTagged horizontal span false 1] =
      carrierLensRouteTerminalDataBlock horizontal span := by
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
