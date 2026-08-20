/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitCompiler
import LeanTrominoes.PeriodicCNFClauseProfileThreeCNFSemantics
import LeanTrominoes.PeriodicCNFStripDirectClauseProfileScan
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaFacts

/-! # Exact finite clause profiles of the guarded direct source formula -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceFormulaProfilesStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Profiles of the exact guarded 3SAT-3 source consumed by the planar
geometric pipeline. -/
def directSourceFormulaClauseProfiles (symbols : List encoding.Γ) :
    List ClauseProfile :=
  PeriodicCNF.ClauseProfileOccurrenceSplit.profiles
    (PeriodicCNF.StripDirectClauseProfileScan.sourceClauseProfiles
      decider symbols)

noncomputable def directSourceFormulaClauseProfilesComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List ClauseProfile)
      encoding.Γ ClauseProfile id id
      (directSourceFormulaClauseProfiles decider) := by
  let complete := TM2CompositionMachine.computableInPolyTime
    (PeriodicCNF.StripDirectClauseProfileScan.sourceClauseProfilesComputableInPolyTime
      decider)
    PeriodicCNF.ClauseProfileOccurrenceSplit.profilesComputableInPolyTime
  exact complete

/-- The finite stream is exactly the polarity-and-slice profile of every
clause in `sourceFormula`, including all occurrence-cycle clauses. -/
theorem directSourceFormulaClauseProfiles_literals_eq
    (symbols : List encoding.Γ) :
    (directSourceFormulaClauseProfiles decider symbols).map
        ClauseProfile.literals =
      (sourceFormula
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
          decider symbols)).clauses.map
        PeriodicCNF.ClauseProfileOccurrenceSplit.literalProfiles := by
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  let sourceProfiles :=
    PeriodicCNF.StripDirectClauseProfileScan.sourceClauseProfiles
      decider symbols
  have sourceCorrect :
      sourceProfiles.map ClauseProfile.literals =
        source.clauses.map
          PeriodicCNF.ClauseProfileOccurrenceSplit.literalProfiles := by
    have profileEq :
        (List.map LiteralProfile.ofLiteral :
          PeriodicClause Nat → List LiteralProfile) =
          PeriodicCNF.ClauseProfileOccurrenceSplit.literalProfiles := by
      funext clause
      rfl
    have scanned :=
      PeriodicCNF.StripDirectClauseProfileScan.sourceClauseProfiles_literals_eq_formula
        decider symbols
    rw [profileEq] at scanned
    simpa [source, sourceProfiles] using scanned
  have threeCorrect :
      sourceProfiles.map ClauseProfile.literals =
        (PeriodicThreeCNF.formula source).clauses.map
          PeriodicCNF.ClauseProfileOccurrenceSplit.literalProfiles :=
    sourceCorrect.trans
      (PeriodicCNF.ClauseProfileThreeCNF.formula_literalProfiles_of_widthAtMostThree
          source
          (formulaOfSymbols_widthAtMostThree decider symbols)).symm
  have split := PeriodicCNF.ClauseProfileOccurrenceSplit.profiles_literals_eq_formula
      sourceProfiles
      (PeriodicThreeCNF.formula source) threeCorrect
  simpa [directSourceFormulaClauseProfiles, sourceProfiles, source,
    sourceFormula_formulaOfSymbols, normalizedFormula] using split

end PeriodicCNFStripReduction
end LeanTrominoes
