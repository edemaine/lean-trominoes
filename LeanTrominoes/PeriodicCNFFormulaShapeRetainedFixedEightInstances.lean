/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarThreeSATThree

/-! # Stable equality procedures for retained fixed-eight shapes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFixedEight

open PeriodicOrthocrossing

/-- Capture the ordinary structural equality procedure before the
geometry-ordered pipeline introduces its opaque elaboration-only instance. -/
def wrappedVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (WrappedPeriodicPlanarSATVariable Variable) :=
  inferInstance

/-- Ordinary structural equality for a fixed-eight occurrence copy of a
wrapped retained variable. -/
def variableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  inferInstance

end FormulaShapeRetainedFixedEight
end PeriodicCNF
end LeanTrominoes
