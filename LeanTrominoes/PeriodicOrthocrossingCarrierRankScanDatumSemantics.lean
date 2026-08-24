/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankScanDatumData

/-! # Operational semantics of identity-free carrier scan data -/

namespace LeanTrominoes.PeriodicOrthocrossing

@[simp] theorem CarrierNodeRankDatum.scanDatum_sameCrossoverSite
    (first second : CarrierNodeRankDatum) :
    first.scanDatum.sameCrossoverSite second.scanDatum =
      first.sameCrossoverSite second :=
  rfl

@[simp] theorem CarrierNodeRankDatum.scanDatum_pairRepresentativeShift
    (first second : CarrierNodeRankDatum) :
    first.scanDatum.pairRepresentativeShift second.scanDatum =
      first.pairRepresentativeShift second :=
  rfl

@[simp] theorem CarrierNodeRankDatum.scanDatum_pairIsRepresentative
    (first second : CarrierNodeRankDatum) :
    first.scanDatum.pairIsRepresentative second.scanDatum =
      first.pairIsRepresentative second :=
  rfl

@[simp] theorem CarrierNodeRankDatum.scanDatum_pairNextSlice
    (first second : CarrierNodeRankDatum) :
    first.scanDatum.pairNextSlice second.scanDatum =
      first.pairNextSlice second :=
  rfl

@[simp] theorem CarrierNodeRankDatum.scanDatum_pairBits
    (first second : CarrierNodeRankDatum) :
    first.scanDatum.pairBits second.scanDatum =
      first.pairBits second :=
  rfl

end LeanTrominoes.PeriodicOrthocrossing
