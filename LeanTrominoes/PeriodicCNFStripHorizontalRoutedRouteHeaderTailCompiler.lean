/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderTailData

/-! # Compiler for dynamic routed-header tails -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderTail

open Computability Turing

/-- Header recognition, local-tail suppression, and inherited-tail streaming
form one fixed finite-state linear-time compiler. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime false transition finish

end HorizontalRoutedRouteHeaderTail
end PeriodicCNFStripReduction
end LeanTrominoes

end
