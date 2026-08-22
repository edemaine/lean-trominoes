/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenData

/-! # Field semantics of finite source-occurrence route tokens -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceRouteTokens

theorem scan_atomBits (seen : Bool) (bits : List Bool) :
    FiniteStateTransducer.scan transition seen
        (bits.map SourceOccurrenceTokens.Token.atomBit) =
      (seen, []) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, FiniteStateTransducer.scan, transition,
        List.nil_append, induction]

end SourceOccurrenceRouteTokens
end PeriodicCNF
end LeanTrominoes
