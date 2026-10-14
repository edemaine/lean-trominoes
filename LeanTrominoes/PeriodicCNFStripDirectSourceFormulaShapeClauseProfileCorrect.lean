/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeCorrect

/-! # Direct formula-shape clause-profile correctness -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The direct finite shape has exactly the named source formula's clause
profiles. -/
theorem directSourceFormulaShape_clauseProfiles_correct
    (symbols : List encoding.Γ) :
    (FormulaShape.clauseProfiles
        (directSourceFormulaShape decider symbols)).map
          ClauseProfile.literals =
      (directSourceFormula decider symbols).clauses.map
        ClauseProfileOccurrenceSplit.literalProfiles :=
  (directSourceFormulaShape_correct_named decider symbols).1

end PeriodicCNFStripReduction
end LeanTrominoes

end
