/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileFinalExactOneData
import LeanTrominoes.PeriodicCNFClauseProfileFigureNineProfileSemantics
import LeanTrominoes.PeriodicCNFClauseProfilePolarityNormalizationSemantics

/-! # Exact semantics of final normalized exact-one profiles -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace ClauseProfileFinalExactOne

open UnaryProgramClauseProfile
open ClauseProfileOccurrenceSplit

/-- An exact source stream becomes the exact clause profile stream after
both Figure 9 stages and polarity normalization. -/
theorem profiles_literals_eq_formula
    {Variable : Type} (source : PeriodicCNF Variable)
    (sourceProfiles : List ClauseProfile)
    (sourceCorrect : sourceProfiles.map ClauseProfile.literals =
      source.clauses.map literalProfiles) :
    (profiles sourceProfiles).map ClauseProfile.literals =
      (PeriodicOneInThreePolarityNormalization.formula
        (PeriodicOneInThreeNoUnits.formula
          (PeriodicOneInThree.formula source))).clauses.map
            literalProfiles := by
  have figureNine :=
    ClauseProfileFigureNine.profiles_literals_eq_formula
      source sourceProfiles sourceCorrect
  have normalized :=
    ClauseProfilePolarityNormalization.profiles_literals_eq_formula
      (PeriodicOneInThreeNoUnits.formula
        (PeriodicOneInThree.formula source))
      (ClauseProfileFigureNine.profiles sourceProfiles)
      figureNine
  exact normalized

end ClauseProfileFinalExactOne
end PeriodicCNF
end LeanTrominoes
