/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairGlobalSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalColumnStreamDefinitions

/-! # Stable-key semantics of compiled carrier terminal blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Stable-key presentation of selected carrier terminal-data blocks from a
deduplicated rank-data stream. -/
def retainedKeyTerminalDataBlocksFromDatums
    (datums : List CarrierNodeRankDatum) :
    List (List PeriodicEightOccurrenceSplit.RetainedTerminalData) :=
  (datums.map CarrierNodeRankDatum.key).dedup.flatMap fun key =>
    (((CarrierRankGlobal.keyBlockDatumPairs datums key).filter fun pair =>
        !pair.1.sameCrossoverSite pair.2).filter fun pair =>
          pair.1.pairIsRepresentative pair.2).map fun pair =>
            retainedPairTerminalDataBlock pair.1 pair.2

/-- Stable-key presentation of the selected carrier terminal-data blocks. -/
def retainedKeyTerminalDataBlocks
    (descriptors : List RouteDescriptor) :
    List (List PeriodicEightOccurrenceSplit.RetainedTerminalData) :=
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  retainedKeyTerminalDataBlocksFromDatums datums

/-- The sparse carrier terminal block stream is exactly the concatenation
of the blocks selected inside each stable semantic key block. -/
theorem retainedTerminalDataBlocksFromDatums_eq_keyBlocks
    (datums : List CarrierNodeRankDatum) :
    retainedTerminalDataBlocksFromDatums datums =
      retainedKeyTerminalDataBlocksFromDatums datums := by
  unfold retainedTerminalDataBlocksFromDatums
    retainedKeyTerminalDataBlocksFromDatums
  exact retainedRowMajorSelectedWith_eq_keyBlocks datums
    retainedPairTerminalDataBlock

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
