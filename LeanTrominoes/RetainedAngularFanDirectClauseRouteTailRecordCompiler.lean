/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordQuery

/-! # Compiling finite Figure 9 record queries for direct copied clauses -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing

/-- Direct clause-record queries expand through one fixed finite-alphabet
transducer; route lengths occur only inside its finite lookup table. -/
noncomputable def
    retainedDirectClauseRouteTailRecordStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id
      retainedDirectClauseRouteTailRecordStream :=
  FiniteBlockTransducer.computableInPolyTime
    retainedDirectClauseRouteTailRecordTokens

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
