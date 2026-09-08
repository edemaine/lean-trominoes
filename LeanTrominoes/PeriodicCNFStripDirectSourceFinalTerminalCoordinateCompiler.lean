/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceTerminalCoordinateKeyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOriginalAtomCoordinateSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalCoordinateLookupSemantics

/-! # Physical terminal coordinates in the exact final atom-occurrence order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

private theorem input_eq_mk {input : DelimitedBinaryWords.Input} {words : List (List Bool)}
    (equal : input.words = words) : input = ⟨words⟩ :=
  DelimitedBinaryWords.eq_of_words_eq equal

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance finalTerminalCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- The terminal contribution to each final occurrence: its physical
translation-zero coordinate, or zero for a different atom constructor. -/
def directSourceFinalTerminalCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  DelimitedBinaryWordKeyedValueLookup.values
    (directSourceFinalCompactOccurrenceAtomWords decider symbols)
    (directSourceTerminalCoordinateKeys decider symbols)
    (directSourceTerminalCoordinates decider horizontal keepPositive symbols)

noncomputable def directSourceFinalTerminalCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalTerminalCoordinates decider horizontal keepPositive) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalTerminalCoordinates
    exact DelimitedBinaryWordKeyedValueLookup.valuesComputableInPolyTime
      (directSourceFinalCompactOccurrenceAtomWords decider)
      (directSourceTerminalCoordinateKeys decider)
      (directSourceTerminalCoordinates decider horizontal keepPositive)
      (fun symbols => (directSourceTerminalCoordinateKeys_length_coordinates
        decider horizontal keepPositive symbols).symm)
      (directSourceFinalCompactOccurrenceAtomWordsComputableInPolyTime decider)
      (directSourceTerminalCoordinateKeysComputableInPolyTime decider)
      (directSourceTerminalCoordinatesComputableInPolyTime decider horizontal keepPositive)
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

private theorem coordinate_query_valid (symbols : List encoding.Γ)
    (query : WrappedPeriodicPlanarSATVariable Variable)
    (member : query ∈ directSourceFinalCoordinateAtoms decider symbols) :
    RetainedDrawingPeriodicPlanarSATVariableValid
      (directSourceFormula decider symbols) query.original := by
  have valid := directSourceFinalCoordinateAtoms_valid decider symbols query member
  change @RetainedDrawingPeriodicPlanarSATVariableValid Variable originalAtomWordVariableDecidableEq
    (directSourceFormula decider symbols) query.original at valid
  rw [show originalAtomWordVariableDecidableEq = directSourceVariableDecidableEq from
    Subsingleton.elim _ _] at valid
  exact valid

/-- The compiler selects the exact physical representative datum at every
valid terminal occurrence, with zero in the other constructor families. -/
theorem directSourceFinalTerminalCoordinates_eq_queryData
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalTerminalCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map
        (ActiveTerminalCompactKeys.queryDatum
          (carrierNodeCoordinateFieldAtPeriod horizontal keepPositive
            (drawingGridSize (directSourceFormula decider symbols).incidenceGraph))) := by
  have keysEq := input_eq_mk (directSourceTerminalCoordinateKeys_eq_nodes decider symbols)
  unfold directSourceFinalTerminalCoordinates
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_coordinateAtoms, keysEq,
    directSourceTerminalCoordinates_eq_nodes]
  exact ActiveTerminalCompactKeys.lookup_eq_queryData (directSourceFormula decider symbols)
    (directSourceFinalCoordinateAtoms decider symbols) (coordinate_query_valid decider symbols)
    (DirectSourceFinalIndexedAtomWords.sourceVariableWord (directSourceFormula decider symbols))
    (carrierNodeCoordinateFieldAtPeriod horizontal keepPositive
      (drawingGridSize (directSourceFormula decider symbols).incidenceGraph))

/-- Equivalently, all terminal entries are the signed coordinates of their
actual geometric translation-zero nodes, before canonical gauging. -/
theorem directSourceFinalTerminalCoordinates_eq_positions
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalTerminalCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map fun query =>
        match query.original with
        | .terminal indexed endpoint =>
            let position := (CarrierNode.terminal ⟨indexed, (0, 0), endpoint⟩).position
              (directSourceFormula decider symbols).incidenceGraph
            let coordinate := if horizontal then position.1 else position.2
            if keepPositive then coordinate.toNat else (-coordinate).toNat
        | _ => 0 := by
  rw [directSourceFinalTerminalCoordinates_eq_queryData]
  apply List.map_congr_left
  rintro ⟨query⟩ _member
  cases query <;>
    simp [ActiveTerminalCompactKeys.queryDatum, ActiveTerminalCompactKeys.queryNode,
      carrierNodeCoordinateFieldAtPeriod, carrierNodeCoordinateAtPeriod,
      carrierNodePositionAtPeriod_drawingGridSize]

/-- All four terminal columns align with the complete final occurrence list. -/
theorem directSourceFinalTerminalCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalTerminalCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCoordinateAtoms decider symbols).length := by
  rw [directSourceFinalTerminalCoordinates_eq_queryData, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction

end
