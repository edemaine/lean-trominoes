/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightDirectionData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarDirectionData
import LeanTrominoes.PeriodicCNFStripSourceFormula

/-! # Direct retained planar direction-descriptor data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directRetainedPlanarDirectionDataVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- Exact pre-split direction descriptors of the retained planarized source
generated from a PSPACE source-symbol word. -/
def directRetainedPlanarDirectionDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedPlanarDirection.descriptors
    (sourceFormula (ProgramSource.formulaOfSymbols decider symbols))

/-- Exact phase-major fixed-eight expansion of the pre-split retained
descriptor stream. -/
def directRetainedFixedEightDirectionDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeFixedEightDirection.descriptors
    (directRetainedPlanarDirectionDescriptors decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes
