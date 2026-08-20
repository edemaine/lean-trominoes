/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceShapeSemantics
import LeanTrominoes.PeriodicCNFClauseProfileThreeCNFSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeData

/-! # Exact guarded direct source formula shapes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceFormulaShapeSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The finite shape gives both exact guarded clause profiles and the exact
number of distinct guarded occurrence variables. -/
theorem directSourceFormulaShape_correct (symbols : List encoding.Γ) :
    (FormulaShape.clauseProfiles
        (directSourceFormulaShape decider symbols)).map
          ClauseProfile.literals =
        (sourceFormula
          (PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.map
            ClauseProfileOccurrenceSplit.literalProfiles ∧
      FormulaShape.variableCount
          (directSourceFormulaShape decider symbols) =
        (PeriodicCNF.variableOccurrences
          (sourceFormula
            (PolySpaceCompiler.formulaOfSymbols decider symbols))).dedup.length := by
  let source := PolySpaceCompiler.formulaOfSymbols decider symbols
  let sourceProfiles :=
    StripDirectClauseProfileScan.sourceClauseProfiles decider symbols
  have sourceCorrect :
      sourceProfiles.map ClauseProfile.literals =
        source.clauses.map ClauseProfileOccurrenceSplit.literalProfiles := by
    have profileEq :
        (List.map LiteralProfile.ofLiteral :
          PeriodicClause Nat → List LiteralProfile) =
          ClauseProfileOccurrenceSplit.literalProfiles := by
      funext clause
      rfl
    have scanned :=
      StripDirectClauseProfileScan.sourceClauseProfiles_literals_eq_formula
        decider symbols
    rw [profileEq] at scanned
    simpa [source, sourceProfiles] using scanned
  have threeCorrect :
      sourceProfiles.map ClauseProfile.literals =
        (PeriodicThreeCNF.formula source).clauses.map
          ClauseProfileOccurrenceSplit.literalProfiles :=
    sourceCorrect.trans
      (ClauseProfileThreeCNF.formula_literalProfiles_of_widthAtMostThree
        source (formulaOfSymbols_widthAtMostThree decider symbols)).symm
  have correct := ClauseProfileOccurrenceShape.shape_correct
    (PeriodicThreeCNF.formula source) sourceProfiles threeCorrect
  simpa [directSourceFormulaShape, sourceProfiles, source,
    sourceFormula_formulaOfSymbols, normalizedFormula] using correct

end PeriodicCNFStripReduction
end LeanTrominoes
