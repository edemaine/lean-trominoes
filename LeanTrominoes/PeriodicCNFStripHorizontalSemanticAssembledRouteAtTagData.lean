/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledEdgeRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticTypedTriplesData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRouteAtTagDataBridge

/-! # Shallow semantic tag-route lookup data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Proof-free route lookup over the shallow proof-backed typed-triple list. -/
def horizontalSemanticAssembledRouteAtTagData
    (source : PeriodicCNF Nat)
    (tag : PeriodicThreeDM.IncidenceTag) : List Cell :=
  typedRouteAtTagListData
    (horizontalSemanticThreeDMTypedTriples source)
    (fun triple color =>
      horizontalTypedIncidenceRouteComputed ((source, triple), color))
    tag

end PeriodicCNFStripReduction
end LeanTrominoes
