/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Carrier.PeriodicCNFStripDirectSourceCarrierCompactAtomWordBlockData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Carrier.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Compact.PeriodicCNFStripDirectSourceFinalCompactOccurrenceAtomWordFamilies

/-! # Direct compact carrier occurrence words agree with the final block -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directCarrierCompactBlockSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Delimited target carrying exactly the carrier-family compact block. -/
def directSourceFinalCompactCarrierAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  ⟨directSourceFinalCompactCarrierAtomWordBlock decider symbols⟩

/-- Expanding every retained compact endpoint pair to its four clause
occurrences gives exactly the carrier-family block of the final compact
occurrence column. -/
theorem directSourceCarrierCompactAtomWordBlock_eq_finalBlock
    (symbols : List encoding.Γ) :
    directSourceCarrierCompactAtomWordBlock decider symbols =
      directSourceFinalCompactCarrierAtomWords decider symbols := by
  unfold directSourceCarrierCompactAtomWordBlock
    DelimitedBinaryWordPairFourWordExpansion.expandedInput
    directSourceFinalCompactCarrierAtomWords
    directSourceFinalCompactCarrierAtomWordBlock
    directThreeCNFSourceFormula
  rw [directSourceCarrierRetainedCompactAtomWordPairs_eq_normalizedLinks]
  rw [directSourceFormula_eq_threeSATThree]
  simp only [List.flatMap_map, List.map_map, Function.comp_def]

end PeriodicCNFStripReduction
end LeanTrominoes

end
