/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFClauseProfileFigureNineData

/-! # Polynomial-time Figure 9 clause-arity expansion -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace ClauseProfileFigureNine

open UnaryProgramClauseArity
open UnaryProgramClauseProfile

/-- The two Figure 9 clause transformations are a fixed finite block scan of
the guarded source profiles. -/
noncomputable def aritiesComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List ClauseProfile) (List Arity)
      ClauseProfile Arity id id arities :=
  FiniteBlockTransducer.computableInPolyTime clauseArities

end ClauseProfileFigureNine
end PeriodicCNF
end LeanTrominoes
