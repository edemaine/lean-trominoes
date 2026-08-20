/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFClauseProfileFigureNineProfileData

/-! # Polynomial-time exact Figure 9 profile expansion -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace ClauseProfileFigureNine

open UnaryProgramClauseProfile

noncomputable def profilesComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List ClauseProfile) (List ClauseProfile)
      ClauseProfile ClauseProfile id id profiles :=
  FiniteBlockTransducer.computableInPolyTime clauseProfiles

end ClauseProfileFigureNine
end PeriodicCNF
end LeanTrominoes
