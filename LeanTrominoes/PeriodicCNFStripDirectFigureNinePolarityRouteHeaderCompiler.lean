/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderCompiler
import LeanTrominoes.PeriodicCNFStripDirectFigureNinePolarityRouteHeaderData
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalDirectionDescriptorConcreteCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for direct finite Figure 9 and polarity route headers -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFigureNinePolarityHeaderCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

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
