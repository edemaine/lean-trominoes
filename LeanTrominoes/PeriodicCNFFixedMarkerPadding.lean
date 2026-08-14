/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFAffineTemplateEmitterTime
import LeanTrominoes.PeriodicCNFAffineEmitterPipeline
import LeanTrominoes.TM2CompositionMachine

/-!
# Fixed data-marker padding for shared emitter workspaces

Some bivariate templates need one runtime counter and one fixed-size counter.
Append the latter as temporary data, without confusing it with any formula
token already present in the shared workspace.  A nested affine workspace
first appends ordinary outer tokens; a finite block map then reinterprets only
those outer tokens as unit data markers.  A second block map removes them.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace FixedMarkerPadding

open AffineEmitterPipeline
open AffineTemplateEmitterMachine
open UnaryProgramTokens

abbrev Workspace (Data : Type) := AffineEmitterPipeline.Workspace Data
abbrev NestedWorkspace (Data : Type) :=
  AffineEmitterPipeline.Workspace (Workspace Data)
abbrev MarkedData (Data : Type) := Data ⊕ Unit
abbrev MarkedWorkspace (Data : Type) := Workspace (MarkedData Data)

def liftItem {Data : Type} : Workspace Data → MarkedWorkspace Data
  | .inl data => .inl (.inl data)
  | .inr token => .inr token

def marker {Data : Type} : MarkedWorkspace Data := .inl (.inr ())

instance markedWorkspaceInhabited {Data : Type} :
    Inhabited (MarkedWorkspace Data) := ⟨marker⟩

def flattenItem {Data : Type} :
    NestedWorkspace Data → List (MarkedWorkspace Data)
  | .inl item => [liftItem item]
  | .inr _ => [marker]

def flatten {Data : Type} :
    List (NestedWorkspace Data) → List (MarkedWorkspace Data) :=
  List.flatMap flattenItem

def outerEnding (count : Nat) : List Token :=
  List.replicate count .atomUnit

/-- Append exactly `count` temporary unit markers after lifting the original
workspace into the expanded data alphabet. -/
def padded {Data : Type} (count : Nat)
    (workspace : List (Workspace Data)) : List (MarkedWorkspace Data) :=
  flatten
    (AffineTemplateEmitterMachine.appendedOutput
      (fun _ : Workspace Data => false) [] (outerEnding count)
      (embedData workspace))

@[simp]
theorem flatten_embedData {Data : Type} (workspace : List (Workspace Data)) :
    flatten (embedData workspace) = workspace.map liftItem := by
  unfold flatten embedData
  rw [List.flatMap_map]
  change workspace.flatMap (fun item => [liftItem item]) = _
  exact AffineEmitterPipeline.flatMap_singleton_eq_map liftItem workspace

@[simp]
theorem flatten_map_outerTokens {Data : Type} (tokens : List Token) :
    flatten
        (tokens.map fun token =>
          (Sum.inr token : NestedWorkspace Data)) =
      (List.replicate tokens.length (marker : MarkedWorkspace Data)) := by
  unfold flatten
  rw [List.flatMap_map]
  change tokens.flatMap
      (fun _ => [(marker : MarkedWorkspace Data)]) = _
  rw [AffineEmitterPipeline.flatMap_singleton_eq_map]
  simp

@[simp]
theorem padded_eq {Data : Type} (count : Nat)
    (workspace : List (Workspace Data)) :
    padded count workspace =
      workspace.map liftItem ++
        List.replicate count (marker : MarkedWorkspace Data) := by
  unfold padded AffineTemplateEmitterMachine.appendedOutput
  have countZero : AffineTemplateEmitterMachine.selectedCount
      (fun _ : Workspace Data => false) (embedData workspace) = 0 := by
    unfold AffineTemplateEmitterMachine.selectedCount embedData
    induction workspace with
    | nil => rfl
    | cons item workspace induction =>
        simp [AffineTemplateEmitterMachine.dataSelected, induction]
  rw [countZero]
  simp only [positionRangeTokens_zero, List.nil_append]
  rw [show flatten
        (embedData workspace ++
          (outerEnding count).map fun token =>
            (Sum.inr token : NestedWorkspace Data)) =
      flatten (embedData workspace) ++
        flatten
          ((outerEnding count).map fun token =>
            (Sum.inr token : NestedWorkspace Data)) by
      simp [flatten, List.flatMap_append]]
  rw [flatten_embedData, flatten_map_outerTokens]
  simp [outerEnding]

noncomputable def paddedComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (count : Nat) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (MarkedWorkspace Data))
      (Workspace Data) (MarkedWorkspace Data) id id (padded count) := by
  let embedded := AffineEmitterPipeline.embedDataComputableInPolyTime
    (Data := Workspace Data)
  let appended := AffineTemplateEmitterMachine.computableInPolyTime
    (fun _ : Workspace Data => false) [] (outerEnding count)
  let throughAppend := TM2CompositionMachine.computableInPolyTime
    embedded appended
  let flattened := FiniteBlockTransducer.computableInPolyTime
    (flattenItem (Data := Data))
  let complete := TM2CompositionMachine.computableInPolyTime
    throughAppend flattened
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (MarkedWorkspace Data))
    (Workspace Data) (MarkedWorkspace Data) id id
    (fun workspace =>
      flatten
        (AffineTemplateEmitterMachine.appendedOutput
          (fun _ : Workspace Data => false) [] (outerEnding count)
          (embedData workspace)))
  exact complete

def unpadItem {Data : Type} : MarkedWorkspace Data → List (Workspace Data)
  | .inl (.inl data) => [.inl data]
  | .inl (.inr _) => []
  | .inr token => [.inr token]

def unpad {Data : Type} :
    List (MarkedWorkspace Data) → List (Workspace Data) :=
  List.flatMap unpadItem

@[simp]
theorem unpad_map_liftItem {Data : Type} (workspace : List (Workspace Data)) :
    unpad (workspace.map liftItem) = workspace := by
  unfold unpad
  rw [List.flatMap_map]
  calc
    workspace.flatMap (fun item => unpadItem (liftItem item)) =
        workspace.flatMap (fun item => [item]) := by
      apply List.flatMap_congr
      intro item _
      cases item <;> rfl
    _ = workspace := by
      rw [AffineEmitterPipeline.flatMap_singleton_eq_map]
      simp

@[simp]
theorem unpad_replicate_marker {Data : Type} (count : Nat) :
    unpad (List.replicate count (marker : MarkedWorkspace Data)) = [] := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      simp only [unpad]
      change [] ++
          List.flatMap unpadItem
            (List.replicate count (marker : MarkedWorkspace Data)) = []
      simpa [unpad] using induction

@[simp]
theorem unpad_map_tokens {Data : Type} (tokens : List Token) :
    unpad
        (tokens.map fun token =>
          (Sum.inr token : MarkedWorkspace Data)) =
      tokens.map fun token => (Sum.inr token : Workspace Data) := by
  unfold unpad
  rw [List.flatMap_map]
  change tokens.flatMap
      (fun token => [(Sum.inr token : Workspace Data)]) = _
  exact AffineEmitterPipeline.flatMap_singleton_eq_map _ tokens

@[simp]
theorem unpad_append {Data : Type}
    (first second : List (MarkedWorkspace Data)) :
    unpad (first ++ second) = unpad first ++ unpad second := by
  simp [unpad, List.flatMap_append]

@[simp]
theorem unpad_padded {Data : Type} (count : Nat)
    (workspace : List (Workspace Data)) :
    unpad (padded count workspace) = workspace := by
  rw [padded_eq, unpad_append, unpad_map_liftItem,
    unpad_replicate_marker, List.append_nil]

noncomputable def unpadComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] :
    @TM2ComputableInPolyTime
      (List (MarkedWorkspace Data)) (List (Workspace Data))
      (MarkedWorkspace Data) (Workspace Data) id id unpad :=
  FiniteBlockTransducer.computableInPolyTime (unpadItem (Data := Data))

end FixedMarkerPadding
end PeriodicCNF
end LeanTrominoes
