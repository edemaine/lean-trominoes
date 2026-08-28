/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendTerminalColumnData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Compiling retained-bend terminal columns -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing PlanarThreeSAT RouteDescriptorPairFieldTags

set_option maxRecDepth 4000

/-- Select every bend terminal-direction block in polynomial time. -/
noncomputable def
    affineBaseBendTerminalDirectionBlockComputableInPolyTime :
    TM2ComputableInPolyTime id id
      affineBaseBendTerminalDirectionBlock :=
  predicateListBlocksComputableInPolyTime bendDescriptorPredicates
    bendTerminalDirectionBlocks

/-- Select every bend terminal-radial block in polynomial time. -/
noncomputable def
    affineBaseBendTerminalRadialBlockComputableInPolyTime :
    TM2ComputableInPolyTime id id
      affineBaseBendTerminalRadialBlock :=
  predicateListBlocksComputableInPolyTime bendDescriptorPredicates
    bendTerminalRadialBlocks

/-- Compile all selected bend terminal direction fields. -/
noncomputable def
    affineBaseBendTerminalDirectionStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id
      affineBaseBendTerminalDirectionStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    affineBaseBendTerminalDirectionBlockComputableInPolyTime isPairEnd

/-- Compile all selected bend terminal radial fields. -/
noncomputable def
    affineBaseBendTerminalRadialStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id
      affineBaseBendTerminalRadialStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    affineBaseBendTerminalRadialBlockComputableInPolyTime isPairEnd

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
