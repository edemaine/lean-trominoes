/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenFieldSemantics

/-! # Source-occurrence atom-field erasure -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteTokens

open Turing

theorem scan_atomTokens (seen : Bool) (atom : Nat) :
    FiniteStateTransducer.scan transition seen
        (SourceOccurrenceTokens.atomTokens atom) =
      (seen, []) := by
  unfold SourceOccurrenceTokens.atomTokens
  simpa only [List.map_map, Function.comp_def] using
    scan_atomBits seen
      ((PartrecToTM2.trNat atom).map SourceOccurrenceTokens.nativeBit)

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteTokens
