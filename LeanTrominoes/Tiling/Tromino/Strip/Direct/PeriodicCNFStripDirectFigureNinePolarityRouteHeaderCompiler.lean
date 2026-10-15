/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.FormulaShape.Polarity.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectFigureNinePolarityRouteHeaderData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFinalDirectionDescriptorConcreteCompiler
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Compiler for direct finite Figure 9 and polarity route headers -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The established direct descriptor compiler followed by the fixed finite
header expansion computes every final route header in polynomial time. -/
noncomputable def
    directFigureNinePolarityRouteHeadersComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directFigureNinePolarityRouteHeaders decider) := by
  let descriptors :=
    directRetainedFigureNineDirectionDescriptorsComputableInPolyTime decider
  let headers :=
    FormulaShapeFigureNinePolarityRouteHeader.sourceHeadersComputableInPolyTime
  let complete :=
    TM2CompositionMachine.computableInPolyTime descriptors headers
  change TM2ComputableInPolyTime id id
    (fun symbols =>
      FormulaShapeFigureNinePolarityRouteHeader.sourceHeaders
        (directRetainedFigureNineDirectionDescriptors decider symbols))
  exact complete

end PeriodicCNFStripReduction
end LeanTrominoes

end
