/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQuery
import LeanTrominoes.FiniteBlockTransducer

/-! # Compiling finite final copied-clause queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing

/-- Finite copied-clause queries are evaluated by a fixed one-pass
polynomial-time transducer. -/
noncomputable def retainedFinalCopiedClauseDescriptorsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List RetainedFinalCopiedClauseQuery)
      (List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
      RetainedFinalCopiedClauseQuery
      PeriodicCNF.FormulaShapeDirectionOrdering.Token
      id id retainedFinalCopiedClauseDescriptors :=
  FiniteBlockTransducer.computableInPolyTime fun query =>
    [retainedFinalCopiedClauseDescriptorOfQuery query]

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
