/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalEnumerationMembershipSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalEnumerationNodupSemantics
import Mathlib.Data.List.Perm.Basic

/-! # Completeness of global carrier-rank enumeration -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

/-- Global rank enumeration neither drops nor duplicates any indexed datum. -/
theorem enumeration_perm_zipIdx (datums : List CarrierNodeRankDatum) :
    List.Perm (enumeration datums) datums.zipIdx := by
  apply (List.perm_ext_iff_of_nodup
    (enumeration_nodup datums)
    (List.Nodup.of_map Prod.snd
      (List.nodup_zipIdx_map_snd datums))).mpr
  exact mem_enumeration_iff datums

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
