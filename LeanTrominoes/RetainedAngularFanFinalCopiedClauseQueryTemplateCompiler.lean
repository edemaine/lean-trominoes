/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryTemplates
import LeanTrominoes.FiniteBlockTransducer

/-! # Compilers for stable copied-clause query templates -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing

/-- Wrapping already-final finite descriptor tokens as precomputed queries is
a fixed one-pass polynomial-time transduction. -/
noncomputable def retainedFinalPrecomputedClauseQueriesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      retainedFinalPrecomputedClauseQueries :=
  FiniteBlockTransducer.computableInPolyTime
    retainedFinalPrecomputedClauseQueryBlock

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
