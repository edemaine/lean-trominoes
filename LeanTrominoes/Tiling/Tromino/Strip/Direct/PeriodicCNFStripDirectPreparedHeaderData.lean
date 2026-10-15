/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetPreparedHeaderSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectExecutableFields
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectGridUnitData
import LeanTrominoes.Tiling.Tromino.Strip.Normalization.PeriodicCNFStripNormalizationPeriodSize
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMNormalizationStripCompilerSize

/-! # Direct prepared strip-header data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The prepared height and width fields obtained from the direct unary
orthocrossing-grid scale. -/
def directPreparedHeaderOfSymbols (symbols : List encoding.Γ) :
    List GadgetPixelFiniteTokens.Token :=
  GadgetPreparedHeaderEmitter.preparedHeader normalizationPeriodFactor
    (directGridUnitsOfSymbols decider symbols)

/-- The streamed prepared header is exactly the header of the compiled
rectangular strip drawing. -/
@[simp] theorem directPreparedHeaderOfSymbols_eq
    (symbols : List encoding.Γ) :
    directPreparedHeaderOfSymbols decider symbols =
      GadgetPixelFiniteTokens.headerField
          (directCompiledStripDrawingOfSymbols decider symbols).verticalPeriod ++
        GadgetPixelFiniteTokens.headerField
          (directCompiledStripDrawingOfSymbols decider symbols).horizontalPeriod := by
  unfold directPreparedHeaderOfSymbols
  rw [GadgetPreparedHeaderEmitter.preparedHeader_eq,
    directGridUnitsOfSymbols_length]
  unfold directCompiledStripDrawingOfSymbols compiledStripDrawing
  rw [PeriodicThreeDM.NormalizationCompiler.compileStrip_verticalPeriod,
    PeriodicThreeDM.NormalizationCompiler.compileStrip_horizontalPeriod]
  unfold PeriodicThreeDM.NormalizationCompiler.finalStripHeight
  rw [normalizationInput_finalNormalizationPeriod_eq]

end PeriodicCNFStripReduction
end LeanTrominoes
