/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Count

/-! # Prefix multiplicity-rank data -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

/-- One-based multiplicity ranks, carrying the already scanned word. -/
def prefixRanksFrom {Value : Type*} [BEq Value] :
    List Value → List Value → List Nat
  | _, [] => []
  | seen, value :: values =>
      (1 + seen.count value) :: prefixRanksFrom (seen ++ [value]) values

/-- Each value's one-based occurrence rank in presentation order. -/
def prefixRanks {Value : Type*} [BEq Value]
    (values : List Value) : List Nat :=
  prefixRanksFrom [] values

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes
