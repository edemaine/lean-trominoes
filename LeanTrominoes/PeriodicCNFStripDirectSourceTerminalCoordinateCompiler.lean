/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedFieldNumericSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierPositionActiveTerminalStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodePositionSemantics

/-! # Direct-source compilers for all physical terminal coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directTerminalCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- The actual two endpoints of every neighboring segment occurrence. -/
def directSourceTerminalCoordinateNodes (symbols : List encoding.Γ) : List CarrierNode :=
  (routeDescriptorNeighborOccurrences
    (numericRouteDescriptors (directSourceFormula decider symbols))).flatMap
      occurrenceCarrierTerminalNodes

/-- Four signed coordinate columns, with inactive affine candidates removed. -/
def directSourceTerminalCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  ActiveTerminalCoordinateFieldStream.values horizontal keepPositive
    (numericRouteDescriptors (directSourceFormula decider symbols))

noncomputable def directSourceTerminalCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Nat) encoding.Γ UnaryFieldEncoderMachine.Symbol
      id UnaryFieldEncoderMachine.unaryFields
      (directSourceTerminalCoordinates decider horizontal keepPositive) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun symbols => ActiveTerminalCoordinateFieldStream.values horizontal keepPositive
      (numericRouteDescriptors (directSourceFormula decider symbols)))
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceNumericRouteDescriptorsComputableInPolyTime decider)
    (ActiveTerminalCoordinateFieldStream.valuesComputableInPolyTime horizontal keepPositive)

/-- Every compiled coordinate has the actual drawing period and names the
corresponding terminal in the geometric endpoint list. -/
theorem directSourceTerminalCoordinates_eq_nodes
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceTerminalCoordinates decider horizontal keepPositive symbols =
      (directSourceTerminalCoordinateNodes decider symbols).map
        (carrierNodeCoordinateFieldAtPeriod horizontal keepPositive
          (drawingGridSize (directSourceFormula decider symbols).incidenceGraph)) := by
  let formula := directSourceFormula decider symbols
  have isLocal : formula.incidenceGraph.IsLocal := by
    unfold formula directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  unfold directSourceTerminalCoordinates directSourceTerminalCoordinateNodes
  rw [ActiveTerminalCoordinateFieldStream.values_numericRouteDescriptors
    horizontal keepPositive formula
    (PeriodicCNF.incidenceGraph_isWellFormed formula)
    (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
    isLocal (directSourceFormula_isForwardLocal decider symbols)
    (directSource_incidencesWithMetadata_ne_nil decider symbols)]
  rw [PeriodicCNF.routeDescriptorStreamGridSize_numericRouteDescriptors formula
    (directSource_incidencesWithMetadata_ne_nil decider symbols)]

/-- Equivalently, the columns contain the signed magnitudes of the actual
geometric node positions, with no remaining route-descriptor interpretation. -/
theorem directSourceTerminalCoordinates_eq_positions
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceTerminalCoordinates decider horizontal keepPositive symbols =
      (directSourceTerminalCoordinateNodes decider symbols).map fun node =>
        let position := node.position (directSourceFormula decider symbols).incidenceGraph
        let coordinate := if horizontal then position.1 else position.2
        if keepPositive then coordinate.toNat else (-coordinate).toNat := by
  rw [directSourceTerminalCoordinates_eq_nodes]
  apply List.map_congr_left
  intro node _nodeMember
  unfold carrierNodeCoordinateFieldAtPeriod carrierNodeCoordinateAtPeriod
  rw [carrierNodePositionAtPeriod_drawingGridSize]

/-- All four columns have exactly one field per actual terminal. -/
theorem directSourceTerminalCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceTerminalCoordinates decider horizontal keepPositive symbols).length =
      (directSourceTerminalCoordinateNodes decider symbols).length := by
  rw [directSourceTerminalCoordinates_eq_nodes]
  exact List.length_map _

end LeanTrominoes.PeriodicCNFStripReduction

end
