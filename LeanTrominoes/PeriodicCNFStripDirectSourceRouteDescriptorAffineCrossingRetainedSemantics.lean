/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorAffineCrossingSemantics
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorAffineCrossingSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorCrossingMarkers

/-! # Retained-marker semantics of the direct affine crossing scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceAffineCrossingRetainedStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourceAffineCrossingRetainedVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Specializing the affine scan to variable markers gives exactly the
semantic direct crossing-marker target. -/
theorem directSourceAffineCrossingMarkers_eq_crossingMarkers
    (symbols : List encoding.Γ) :
    directSourceAffineCrossingMarkers decider
        FormulaShapeDirectionOrdering.Token.variable symbols =
      directSourceRouteDescriptorCrossingMarkers decider symbols := by
  rw [directSourceAffineCrossingMarkers_eq_stream]
  rw [PeriodicCNF.numericRouteDescriptors_affineCrossingMarkerStream_eq_replicate
    FormulaShapeDirectionOrdering.Token.variable
    (directSourceFormula decider symbols)
    (directSourceFormula_isForwardLocal decider symbols)
    (directSource_incidencesWithMetadata_ne_nil decider symbols)]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

end
