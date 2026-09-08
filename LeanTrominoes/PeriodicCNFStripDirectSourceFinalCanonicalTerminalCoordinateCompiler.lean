/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceTerminalCoordinateKeyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCanonicalTerminalCoordinateCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierCanonicalTerminalCoordinateGeometry
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOriginalAtomCoordinateSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalCoordinateLookupSemantics

/-! # Canonical terminal coordinates in the exact final atom-occurrence order -/

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

noncomputable local instance finalCanonicalTerminalCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- The terminal contribution to each final occurrence: its
canonical coordinate, or zero for a different atom constructor. -/
def directSourceFinalCanonicalTerminalCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  DelimitedBinaryWordKeyedValueLookup.values
    (directSourceFinalCompactOccurrenceAtomWords decider symbols)
    (directSourceTerminalCoordinateKeys decider symbols)
    (directSourceCanonicalTerminalCoordinates decider horizontal keepPositive symbols)

noncomputable def directSourceFinalCanonicalTerminalCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCanonicalTerminalCoordinates decider horizontal keepPositive) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCanonicalTerminalCoordinates
    exact DelimitedBinaryWordKeyedValueLookup.valuesComputableInPolyTime
      (directSourceFinalCompactOccurrenceAtomWords decider)
      (directSourceTerminalCoordinateKeys decider)
      (directSourceCanonicalTerminalCoordinates decider horizontal keepPositive)
      (fun symbols => by
        rw [directSourceCanonicalTerminalCoordinates_length,
          directSourceTerminalCoordinateKeys_eq_nodes, List.length_map])
      (directSourceFinalCompactOccurrenceAtomWordsComputableInPolyTime decider)
      (directSourceTerminalCoordinateKeysComputableInPolyTime decider)
      (directSourceCanonicalTerminalCoordinatesComputableInPolyTime decider horizontal keepPositive)
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

/-- The compiler selects the exact canonical representative datum at every
valid terminal occurrence, with zero in the other constructor families. -/
theorem directSourceFinalCanonicalTerminalCoordinates_eq_queryData
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalCanonicalTerminalCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map
        (ActiveTerminalCompactKeys.queryDatum
          (carrierNodeCanonicalCoordinateFieldAtPeriod horizontal keepPositive
            (drawingGridSize (directSourceFormula decider symbols).incidenceGraph))) := by
  have keysEq := input_eq_mk (directSourceTerminalCoordinateKeys_eq_nodes decider symbols)
  unfold directSourceFinalCanonicalTerminalCoordinates
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_coordinateAtoms, keysEq,
    directSourceCanonicalTerminalCoordinates_eq_nodes]
  exact ActiveTerminalCompactKeys.lookup_eq_queryData (directSourceFormula decider symbols)
    (directSourceFinalCoordinateAtoms decider symbols) (coordinate_query_valid decider symbols)
    (DirectSourceFinalIndexedAtomWords.sourceVariableWord (directSourceFormula decider symbols))
    (carrierNodeCanonicalCoordinateFieldAtPeriod horizontal keepPositive
      (drawingGridSize (directSourceFormula decider symbols).incidenceGraph))

/-- Equivalently, all terminal entries are the signed coordinates of their
actual canonically gauged geometric nodes. -/
theorem directSourceFinalCanonicalTerminalCoordinates_eq_positions
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalCanonicalTerminalCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map fun query =>
        match query.original with
        | .terminal indexed endpoint =>
            let position := (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
              (directSourceFormula decider symbols)).position ⟨.terminal indexed endpoint⟩
            let coordinate := if horizontal then position.1 else position.2
            if keepPositive then coordinate.toNat else (-coordinate).toNat
        | _ => 0 := by
  rw [directSourceFinalCanonicalTerminalCoordinates_eq_queryData]
  apply List.map_congr_left
  rintro ⟨query⟩ _member
  cases query <;>
    simp [ActiveTerminalCompactKeys.queryDatum, ActiveTerminalCompactKeys.queryNode,
      carrierNodeCanonicalCoordinateFieldAtPeriod, carrierNodeCanonicalCoordinateAtPeriod,
      carrierNodeCanonicalPositionAtPeriod_terminal_eq_gaugedPosition]

/-- All four terminal columns align with the complete final occurrence list. -/
theorem directSourceFinalCanonicalTerminalCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalTerminalCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCoordinateAtoms decider symbols).length := by
  rw [directSourceFinalCanonicalTerminalCoordinates_eq_queryData, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction

end
