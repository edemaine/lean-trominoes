/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedFieldNumericSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierCanonicalTerminalCoordinateStreamCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceTerminalCoordinateCompiler
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodePositionSemantics

/-! # Direct-source compilers for canonically wrapped terminal coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCanonicalTerminalCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- Four signed coordinate columns, with inactive affine candidates removed. -/
def directSourceCanonicalTerminalCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  CanonicalTerminalCoordinateFieldStream.values horizontal keepPositive
    (numericRouteDescriptors (directSourceFormula decider symbols))

noncomputable def directSourceCanonicalTerminalCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Nat) encoding.Γ UnaryFieldEncoderMachine.Symbol
      id UnaryFieldEncoderMachine.unaryFields
      (directSourceCanonicalTerminalCoordinates decider horizontal keepPositive) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun symbols => CanonicalTerminalCoordinateFieldStream.values horizontal keepPositive
      (numericRouteDescriptors (directSourceFormula decider symbols)))
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceNumericRouteDescriptorsComputableInPolyTime decider)
    (CanonicalTerminalCoordinateFieldStream.valuesComputableInPolyTime horizontal keepPositive)

/-- Every compiled coordinate has the actual drawing period and names the
corresponding terminal in the geometric endpoint list. -/
theorem directSourceCanonicalTerminalCoordinates_eq_nodes
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceCanonicalTerminalCoordinates decider horizontal keepPositive symbols =
      (directSourceTerminalCoordinateNodes decider symbols).map
        (carrierNodeCanonicalCoordinateFieldAtPeriod horizontal keepPositive
          (drawingGridSize (directSourceFormula decider symbols).incidenceGraph)) := by
  let formula := directSourceFormula decider symbols
  have isLocal : formula.incidenceGraph.IsLocal := by
    unfold formula directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  unfold directSourceCanonicalTerminalCoordinates directSourceTerminalCoordinateNodes
  rw [CanonicalTerminalCoordinateFieldStream.values_numericRouteDescriptors
    horizontal keepPositive formula
    (PeriodicCNF.incidenceGraph_isWellFormed formula)
    (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
    isLocal (directSourceFormula_isForwardLocal decider symbols)
    (directSource_incidencesWithMetadata_ne_nil decider symbols)]
  rw [PeriodicCNF.routeDescriptorStreamGridSize_numericRouteDescriptors formula
    (directSource_incidencesWithMetadata_ne_nil decider symbols)]

/-- All four columns have exactly one field per actual terminal. -/
theorem directSourceCanonicalTerminalCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceCanonicalTerminalCoordinates decider horizontal keepPositive symbols).length =
      (directSourceTerminalCoordinateNodes decider symbols).length := by
  rw [directSourceCanonicalTerminalCoordinates_eq_nodes]
  exact List.length_map _

end LeanTrominoes.PeriodicCNFStripReduction

end
