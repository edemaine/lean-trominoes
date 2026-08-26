/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalBlockDisjointSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalBlockNodupSemantics

/-! # Distinctness of global carrier-rank enumeration -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

theorem enumeration_nodup (datums : List CarrierNodeRankDatum) :
    (enumeration datums).Nodup := by
  unfold enumeration
  rw [List.nodup_flatMap]
  constructor
  · intro key _keyMember
    exact keyBlock_nodup datums key
  · exact (List.nodup_dedup
      (datums.map CarrierRankCompiledKey.ofDatum)).imp fun different =>
        keyBlocks_disjoint datums different

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
