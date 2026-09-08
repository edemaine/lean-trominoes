/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceInternalCrossingCoordinateCompiler
import LeanTrominoes.UnaryFieldConstantStreamCompiler
import LeanTrominoes.UnaryFieldConstantOffsetCompiler

/-! # Finite internal-role data aligned with the crossing dictionary -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance internalRoleDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- A fixed datum per role, with one entry for every physical dictionary node. -/
def directSourceInternalCrossingRoleData (roleValue : PlanarThreeSAT.CrossoverInternal → Nat)
    (symbols : List encoding.Γ) : List Nat :=
  InternalCrossingCoordinateKeys.roles.flatMap fun role =>
    UnaryFieldConstantOffsets.values (roleValue role)
      (UnaryFieldConstantStreams.zeros
        (directSourceCarrierCrossingMacroOriginCoordinates decider .horizontalPositive symbols))

noncomputable def directSourceInternalCrossingRoleDataComputableInPolyTime
    (roleValue : PlanarThreeSAT.CrossoverInternal → Nat) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceInternalCrossingRoleData decider roleValue) := by
  let zeros := TM2CompositionMachine.computableInPolyTime
    (directSourceCarrierCrossingMacroOriginCoordinatesComputableInPolyTime decider .horizontalPositive)
    UnaryFieldConstantStreams.zerosComputableInPolyTime
  exact UnaryFieldEncoderMachine.flatMapComputableInPolyTime InternalCrossingCoordinateKeys.roles
    (fun role symbols => UnaryFieldConstantOffsets.values (roleValue role)
      (UnaryFieldConstantStreams.zeros
        (directSourceCarrierCrossingMacroOriginCoordinates decider .horizontalPositive symbols)))
    (fun role => TM2CompositionMachine.computableInPolyTime zeros
      (UnaryFieldConstantOffsets.computableInPolyTime (roleValue role)))

theorem directSourceInternalCrossingRoleData_eq_candidates
    (roleValue : PlanarThreeSAT.CrossoverInternal → Nat) (symbols : List encoding.Γ) :
    directSourceInternalCrossingRoleData decider roleValue symbols =
      (InternalCrossingCoordinateKeys.candidates
        (numericRouteDescriptors (directSourceFormula decider symbols))).map
        (fun candidate => roleValue candidate.1) := by
  unfold directSourceInternalCrossingRoleData
  rw [directSourceCarrierCrossingMacroOriginCoordinates_eq_nodes]
  simp [UnaryFieldConstantOffsets.values, UnaryFieldConstantStreams.zeros,
    InternalCrossingCoordinateKeys.candidates, List.map_flatMap, List.map_map, Function.comp_def]

theorem directSourceInternalCrossingCoordinateKeys_length_roleData
    (roleValue : PlanarThreeSAT.CrossoverInternal → Nat) (symbols : List encoding.Γ) :
    (directSourceInternalCrossingCoordinateKeys decider symbols).words.length =
      (directSourceInternalCrossingRoleData decider roleValue symbols).length := by
  rw [directSourceInternalCrossingCoordinateKeys_eq_candidates,
    directSourceInternalCrossingRoleData_eq_candidates, List.length_map, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction
end
