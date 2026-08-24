/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATVariableGaugeData

/-! # Endpoint normalization data for retained carrier clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Periodicize a physical carrier node, wrap its prototype, and incorporate
the canonical variable gauge. -/
def carrierWrappedVariableNormalization
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (node : CarrierNode) :
    WrappedPeriodicPlanarSATVariable Variable × Cell :=
  let normalized :=
    normalizePlanarSATVariable source (.inl (.carrier node))
  let wrapped : WrappedPeriodicPlanarSATVariable Variable :=
    ⟨normalized.1⟩
  (wrapped,
    Cell.add normalized.2
      (retainedDrawingWrappedPeriodicPlanarSATVariableGaugeData
        source wrapped))

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
