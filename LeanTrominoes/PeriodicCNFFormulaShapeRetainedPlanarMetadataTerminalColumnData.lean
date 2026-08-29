/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalData

/-! # Terminal-coordinate column blocks for retained carriers and bends -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT

/-- The four carrier incidences in clause-major, literal-major order. -/
def carrierLensRouteTerminalDataBlock
    (horizontal : Bool) (span : Int) : List RetainedTerminalData :=
  [carrierLensRouteTerminalData horizontal span 0 0,
    carrierLensRouteTerminalData horizontal span 0 1,
    carrierLensRouteTerminalData horizontal span 1 0,
    carrierLensRouteTerminalData horizontal span 1 1]

/-- The four bend incidences in the same local presentation order. -/
def bendRouteTerminalDataBlock
    (firstPort secondPort : CornerPort) : List RetainedTerminalData :=
  [bendRouteTerminalData firstPort secondPort 0 0,
    bendRouteTerminalData firstPort secondPort 0 1,
    bendRouteTerminalData firstPort secondPort 1 0,
    bendRouteTerminalData firstPort secondPort 1 1]

/-- Direction-rank projection of a terminal-data block. -/
def terminalDataDirectionRanks
    (terminals : List RetainedTerminalData) : List Nat :=
  terminals.map fun terminal => terminal.1.angularRank

/-- Radial-length projection of a terminal-data block. -/
def terminalDataRadialLengths
    (terminals : List RetainedTerminalData) : List Nat :=
  terminals.map Prod.snd

/-- The carrier block already clamps its only span-dependent length at zero,
so converting a signed span through `Nat` does not change the block. -/
@[simp] theorem carrierLensRouteTerminalDataBlock_toNat
    (horizontal : Bool) (span : Int) :
    carrierLensRouteTerminalDataBlock horizontal span.toNat =
      carrierLensRouteTerminalDataBlock horizontal span := by
  cases span <;> rfl

/-- Carrier direction ranks depend only on the selected axis. -/
theorem carrierLensRouteTerminalDataBlock_directionRanks
    (horizontal : Bool) (span : Int) :
    terminalDataDirectionRanks
        (carrierLensRouteTerminalDataBlock horizontal span) =
      if horizontal then [0, 8, 3, 6] else [3, 0, 6, 8] := by
  cases horizontal <;>
    rfl

/-- Only the fourth carrier radial length depends on the carrier span. -/
theorem carrierLensRouteTerminalDataBlock_radialLengths
    (horizontal : Bool) (span : Int) :
    terminalDataRadialLengths
        (carrierLensRouteTerminalDataBlock horizontal span) =
      [3, 2, 1, (span - 6).toNat] := by
  cases horizontal <;>
    rfl

@[simp] theorem carrierLensRouteTerminalDataBlock_length
    (horizontal : Bool) (span : Int) :
    (carrierLensRouteTerminalDataBlock horizontal span).length = 4 := by
  rfl

@[simp] theorem bendRouteTerminalDataBlock_length
    (firstPort secondPort : CornerPort) :
    (bendRouteTerminalDataBlock firstPort secondPort).length = 4 := by
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
