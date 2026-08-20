/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticAssembledRouteAtTagData
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteTripleLookupSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticAssembledRouteAtTagData

/-! # Computed tag lookup agrees with shallow semantic data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalAssembledRouteAtTagComputed_eq_semanticData
    (source : PeriodicCNF Nat)
    (tag : PeriodicThreeDM.IncidenceTag) :
    horizontalAssembledRouteAtTagComputed (source, tag) =
      horizontalSemanticAssembledRouteAtTagData source tag := by
  unfold horizontalAssembledRouteAtTagComputed
    horizontalSemanticAssembledRouteAtTagData
    PeriodicPlanarOneInThreeToThreeDM.typedRouteAtTagListData
  exact congrArg
    (PeriodicPlanarOneInThreeToThreeDM.typedRouteFromOptionData
      (fun triple color =>
        horizontalTypedIncidenceRouteComputed ((source, triple), color))
      tag.color)
    (horizontalAssembledRouteTriple?Computed_eq_semantic source tag)

end PeriodicCNFStripReduction
end LeanTrominoes
