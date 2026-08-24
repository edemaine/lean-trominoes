/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements
import LeanTrominoes.PositionedPeriodicCNFVariableGauge

/-! # Canonical retained periodic planar-SAT variable gauge data -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Lightweight copy of the canonical lattice-cell quotient used when
normalizing retained carrier endpoints. -/
def retainedDrawingWrappedPeriodicPlanarSATVariableGaugeData
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    WrappedPeriodicPlanarSATVariable Variable → Cell :=
  (wrappedDrawingPeriodicPlanarSATPlacement
    formula).canonicalPositionGauge

end LeanTrominoes.PeriodicOrthocrossing
