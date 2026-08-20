/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileFinalExactOneData
import LeanTrominoes.PeriodicCNFClauseProfileFigureNineProfileCompiler
import LeanTrominoes.PeriodicCNFClauseProfilePolarityNormalizationCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Polynomial-time final normalized exact-one profiles -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace ClauseProfileFinalExactOne

open UnaryProgramClauseProfile

noncomputable def profilesComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List ClauseProfile) (List ClauseProfile)
      ClauseProfile ClauseProfile id id profiles := by
  let figureNine :
      @TM2ComputableInPolyTime
        (List ClauseProfile) (List ClauseProfile)
        ClauseProfile ClauseProfile id id
        ClauseProfileFigureNine.profiles :=
    ClauseProfileFigureNine.profilesComputableInPolyTime
  let normalized :
      @TM2ComputableInPolyTime
        (List ClauseProfile) (List ClauseProfile)
        ClauseProfile ClauseProfile id id
        ClauseProfilePolarityNormalization.profiles :=
    ClauseProfilePolarityNormalization.profilesComputableInPolyTime
  let complete := TM2CompositionMachine.computableInPolyTime
    figureNine normalized
  unfold profiles
  exact complete

end ClauseProfileFinalExactOne
end PeriodicCNF
end LeanTrominoes
