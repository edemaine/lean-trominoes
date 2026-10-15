/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeRetainedFigureNineDirectionData
import LeanTrominoes.Tiling.Tromino.Strip.Source.PeriodicCNFStripSourceFormula

/-! # Direct retained Figure 9 direction-descriptor streams -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directRetainedDirectionDescriptorDataVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- Finite literal-profile/exit-direction descriptors for the actual guarded
PSPACE source after retained planarization and fixed-eight splitting. -/
def directRetainedFigureNineDirectionDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedFigureNineDirection.descriptors
    (sourceFormula (ProgramSource.formulaOfSymbols decider symbols))

end PeriodicCNFStripReduction
end LeanTrominoes
