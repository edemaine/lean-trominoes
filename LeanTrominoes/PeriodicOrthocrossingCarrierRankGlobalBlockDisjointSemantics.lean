/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalBlockSemantics

/-! # Disjointness of distinct global carrier-rank blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

theorem keyBlocks_disjoint (datums : List CarrierNodeRankDatum)
    {first second : CarrierRankCompiledKey} (different : first ≠ second) :
    List.Disjoint (keyBlock datums first) (keyBlock datums second) :=
  fun {_entry} firstMember secondMember =>
    different ((entryKey_eq_of_mem_keyBlock
      datums first _entry firstMember).symm.trans
        (entryKey_eq_of_mem_keyBlock datums second _entry secondMember))

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
