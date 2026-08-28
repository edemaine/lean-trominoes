/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableCompactAtomWordCleanupData

/-! # Compiler for routed-variable compact atom-word cleanup -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RoutedVariableCompactAtomWordCleanup

open Computability Turing

noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens := by
  unfold tokens
  exact FiniteStateTransducer.computableInPolyTime
    (.between .terminal) transition finish

end RoutedVariableCompactAtomWordCleanup
end LeanTrominoes.PeriodicOrthocrossing

end
