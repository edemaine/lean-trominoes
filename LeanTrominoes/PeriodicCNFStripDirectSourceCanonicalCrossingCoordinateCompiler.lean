/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedFieldNumericSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedNodeWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCanonicalCrossingCoordinateRankCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceInternalCrossingCoordinateCompiler

/-! # Direct-source canonical crossing coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCanonicalCrossingCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- Canonical crossing coordinates, including the chosen finite side offsets. -/
def directSourceCarrierCanonicalCrossingCoordinates
    (offset : CrossingSide → Cell)
    (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) : List Nat :=
  CarrierCanonicalCrossingCoordinates.rankedValues offset field
    (numericRouteDescriptors (directSourceFormula decider symbols))

noncomputable def
    directSourceCarrierCanonicalCrossingCoordinatesComputableInPolyTime
    (offset : CrossingSide → Cell)
    (field : CarrierCrossingMacroOrigin.Field) :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Nat)
      encoding.Γ UnaryFieldEncoderMachine.Symbol
      id UnaryFieldEncoderMachine.unaryFields
      (directSourceCarrierCanonicalCrossingCoordinates decider offset field) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun symbols => CarrierCanonicalCrossingCoordinates.rankedValues offset field
      (numericRouteDescriptors (directSourceFormula decider symbols)))
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceNumericRouteDescriptorsComputableInPolyTime decider)
    (CarrierCanonicalCrossingCoordinates.rankedValuesComputableInPolyTime offset field)

/-- The compiled columns denote the exact canonical crossing points at each retained node. -/
theorem directSourceCarrierCanonicalCrossingCoordinates_eq_nodes
    (offset : CrossingSide → Cell)
    (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) :
    directSourceCarrierCanonicalCrossingCoordinates decider offset field symbols =
      (CarrierCrossingMacroOrigin.nodes
        (numericRouteDescriptors (directSourceFormula decider symbols))).map
          (CarrierCanonicalCrossingCoordinates.nodeValue offset field
            (routeDescriptorStreamGridSize (numericRouteDescriptors (directSourceFormula decider symbols)))) := by
  let formula := directSourceFormula decider symbols
  have isLocal : formula.incidenceGraph.IsLocal := by
    unfold formula directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  unfold directSourceCarrierCanonicalCrossingCoordinates
  exact CarrierCanonicalCrossingCoordinates.rankedValues_numericRouteDescriptors offset field formula
    (PeriodicCNF.incidenceGraph_isWellFormed formula)
    (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
    isLocal
    (directSourceFormula_isForwardLocal decider symbols)
    (directSource_incidencesWithMetadata_ne_nil decider symbols)

/-- All four coordinate columns have one entry per physical carrier node. -/
theorem directSourceCarrierCanonicalCrossingCoordinates_length
    (offset : CrossingSide → Cell)
    (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) :
    (directSourceCarrierCanonicalCrossingCoordinates decider offset field symbols).length =
      (CarrierCrossingMacroOrigin.nodes
        (numericRouteDescriptors (directSourceFormula decider symbols))).length := by
  rw [directSourceCarrierCanonicalCrossingCoordinates_eq_nodes]
  exact List.length_map _


/-- Canonical coordinates for all nine internal roles, in the existing role-major dictionary order. -/
def directSourceInternalCanonicalCoordinateData (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) : List Nat :=
  InternalCrossingCoordinateKeys.roles.flatMap fun role =>
    directSourceCarrierCanonicalCrossingCoordinates decider
      (fun _ => PlanarThreeSAT.CrossoverVariable.position (crossoverInternalVariable role)) field symbols

noncomputable def directSourceInternalCanonicalCoordinateDataComputableInPolyTime
    (field : CarrierCrossingMacroOrigin.Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceInternalCanonicalCoordinateData decider field) := by
  exact UnaryFieldEncoderMachine.flatMapComputableInPolyTime InternalCrossingCoordinateKeys.roles
    (fun role => directSourceCarrierCanonicalCrossingCoordinates decider
      (fun _ => PlanarThreeSAT.CrossoverVariable.position (crossoverInternalVariable role)) field)
    (fun role => directSourceCarrierCanonicalCrossingCoordinatesComputableInPolyTime decider
      (fun _ => PlanarThreeSAT.CrossoverVariable.position (crossoverInternalVariable role)) field)

theorem directSourceInternalCanonicalCoordinateData_eq_candidates
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    directSourceInternalCanonicalCoordinateData decider field symbols =
      (InternalCrossingCoordinateKeys.candidates (numericRouteDescriptors (directSourceFormula decider symbols))).map
        (fun candidate => CarrierCanonicalCrossingCoordinates.nodeValue
          (fun _ => PlanarThreeSAT.CrossoverVariable.position (crossoverInternalVariable candidate.1)) field
          (routeDescriptorStreamGridSize (numericRouteDescriptors (directSourceFormula decider symbols))) candidate.2) := by
  unfold directSourceInternalCanonicalCoordinateData
  simp only [directSourceCarrierCanonicalCrossingCoordinates_eq_nodes,
    InternalCrossingCoordinateKeys.candidates, List.map_flatMap, List.map_map, Function.comp_def]

theorem directSourceInternalCanonicalCoordinateData_length
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    (directSourceInternalCanonicalCoordinateData decider field symbols).length =
      (directSourceInternalCrossingCoordinateKeys decider symbols).words.length := by
  rw [directSourceInternalCanonicalCoordinateData_eq_candidates,
    directSourceInternalCrossingCoordinateKeys_eq_candidates, List.length_map, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction
end
