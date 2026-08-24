/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRouteTerminalData

/-! # External variables of the routed planar SAT construction -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- External variables consist of route carriers and central lifted atoms. -/
inductive PlanarSATNode (Variable : Type*)
  | carrier (node : CarrierNode)
  | atom (occurrence : Variable × Cell)
  deriving DecidableEq, Repr

end LeanTrominoes.PeriodicOrthocrossing
