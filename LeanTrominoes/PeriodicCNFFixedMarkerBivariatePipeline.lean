/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFixedMarkerPadding
import LeanTrominoes.PeriodicCNFBivariateTemplateEmitterTime

/-!
# Bivariate emission with a fixed temporary counter

Wrap the verified bivariate emitter between fixed-marker padding and removal.
The first counter is any selected class in the original stable data; the
second counter consists of exactly the temporary marker block.  Consequently
the wrapper can emit fixed-many templates whose atoms depend affinely on a
runtime width, while returning to the original workspace alphabet.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace FixedMarkerBivariatePipeline

open AffineEmitterPipeline
open UnaryProgramTokens

abbrev Recipe := BivariateProgramTemplates.Recipe
abbrev Workspace (Data : Type) := FixedMarkerPadding.Workspace Data
abbrev MarkedData (Data : Type) := FixedMarkerPadding.MarkedData Data
abbrev MarkedWorkspace (Data : Type) :=
  FixedMarkerPadding.MarkedWorkspace Data

instance markedDataInhabited {Data : Type} [Inhabited Data] :
    Inhabited (MarkedData Data) := ⟨.inl default⟩

def liftedFirst {Data : Type} (selected : Data → Bool) :
    MarkedData Data → Bool
  | .inl data => selected data
  | .inr _ => false

def isMarker {Data : Type} : MarkedData Data → Bool
  | .inl _ => false
  | .inr _ => true

theorem selectedCount_append {Data : Type}
    (selected : Data → Bool)
    (first second : List (BivariateTemplateEmitterMachine.Workspace Data)) :
    BivariateTemplateEmitterMachine.selectedCount selected (first ++ second) =
      BivariateTemplateEmitterMachine.selectedCount selected first +
        BivariateTemplateEmitterMachine.selectedCount selected second := by
  unfold BivariateTemplateEmitterMachine.selectedCount
  exact AffineEmitterPipeline.unarySelectedCount_append
    (BivariateTemplateEmitterMachine.dataSelected selected) first second

@[simp]
theorem selectedCount_liftItems {Data : Type} (selected : Data → Bool)
    (workspace : List (Workspace Data)) :
    BivariateTemplateEmitterMachine.selectedCount (liftedFirst selected)
        (workspace.map FixedMarkerPadding.liftItem) =
      BivariateTemplateEmitterMachine.selectedCount selected workspace := by
  unfold BivariateTemplateEmitterMachine.selectedCount
  induction workspace with
  | nil => rfl
  | cons item workspace induction =>
      cases item <;>
        simp [UnaryPolynomialPaddingMachine.selectedCount,
          BivariateTemplateEmitterMachine.dataSelected,
          FixedMarkerPadding.liftItem, liftedFirst, induction]

@[simp]
theorem selectedCount_liftItems_isMarker {Data : Type}
    (workspace : List (Workspace Data)) :
    BivariateTemplateEmitterMachine.selectedCount (isMarker (Data := Data))
        (workspace.map FixedMarkerPadding.liftItem) = 0 := by
  unfold BivariateTemplateEmitterMachine.selectedCount
  induction workspace with
  | nil => rfl
  | cons item workspace induction =>
      cases item <;>
        simp [BivariateTemplateEmitterMachine.dataSelected,
          FixedMarkerPadding.liftItem, isMarker, induction]

@[simp]
theorem selectedCount_markers_liftedFirst {Data : Type}
    (selected : Data → Bool) (count : Nat) :
    BivariateTemplateEmitterMachine.selectedCount (liftedFirst selected)
        (List.replicate count
          (FixedMarkerPadding.marker : MarkedWorkspace Data)) = 0 := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      unfold BivariateTemplateEmitterMachine.selectedCount at induction ⊢
      rw [UnaryPolynomialPaddingMachine.selectedCount_cons]
      simpa [
        BivariateTemplateEmitterMachine.dataSelected,
        FixedMarkerPadding.marker, liftedFirst] using induction

@[simp]
theorem selectedCount_markers_isMarker {Data : Type} (count : Nat) :
    BivariateTemplateEmitterMachine.selectedCount (isMarker (Data := Data))
        (List.replicate count
          (FixedMarkerPadding.marker : MarkedWorkspace Data)) = count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      unfold BivariateTemplateEmitterMachine.selectedCount at induction ⊢
      rw [UnaryPolynomialPaddingMachine.selectedCount_cons]
      simp only [
        BivariateTemplateEmitterMachine.dataSelected,
        FixedMarkerPadding.marker, isMarker, if_true]
      simp only [FixedMarkerPadding.marker] at induction
      rw [induction]
      omega

@[simp]
theorem firstCount_padded {Data : Type} (selected : Data → Bool)
    (count : Nat) (workspace : List (Workspace Data)) :
    BivariateTemplateEmitterMachine.selectedCount (liftedFirst selected)
        (FixedMarkerPadding.padded count workspace) =
      BivariateTemplateEmitterMachine.selectedCount selected workspace := by
  rw [FixedMarkerPadding.padded_eq, selectedCount_append,
    selectedCount_liftItems, selectedCount_markers_liftedFirst,
    Nat.add_zero]

@[simp]
theorem secondCount_padded {Data : Type} (count : Nat)
    (workspace : List (Workspace Data)) :
    BivariateTemplateEmitterMachine.selectedCount (isMarker (Data := Data))
        (FixedMarkerPadding.padded count workspace) = count := by
  rw [FixedMarkerPadding.padded_eq, selectedCount_append,
    selectedCount_liftItems_isMarker, selectedCount_markers_isMarker,
    Nat.zero_add]

/-- Pad, emit with runtime and fixed counters, and erase the padding. -/
def run {Data : Type} (selected : Data → Bool) (markerCount : Nat)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  FixedMarkerPadding.unpad
    (BivariateTemplateEmitterMachine.appendedOutput
      (liftedFirst selected) (isMarker (Data := Data)) recipes ending
      (FixedMarkerPadding.padded markerCount workspace))

/-- Exact input-preserving semantics of the wrapped bivariate pass. -/
theorem run_eq_append {Data : Type} (selected : Data → Bool)
    (markerCount : Nat) (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) :
    run selected markerCount recipes ending workspace =
      workspace ++
        (BivariateTemplateEmitterMachine.positionRangeTokens recipes
          (BivariateTemplateEmitterMachine.selectedCount selected workspace)
          0 markerCount ++ ending).map fun token =>
            (Sum.inr token : Workspace Data) := by
  unfold run BivariateTemplateEmitterMachine.appendedOutput
  rw [firstCount_padded, secondCount_padded,
    FixedMarkerPadding.unpad_append,
    FixedMarkerPadding.unpad_padded,
    FixedMarkerPadding.unpad_map_tokens]

noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (markerCount : Nat) (recipes : List Recipe) (ending : List Token) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (run selected markerCount recipes ending) := by
  let padded := FixedMarkerPadding.paddedComputableInPolyTime
    (Data := Data) markerCount
  let emitted := BivariateTemplateEmitterMachine.computableInPolyTime
    (liftedFirst selected) (isMarker (Data := Data)) recipes ending
  let throughEmission := TM2CompositionMachine.computableInPolyTime
    padded emitted
  let complete := TM2CompositionMachine.computableInPolyTime throughEmission
    (FixedMarkerPadding.unpadComputableInPolyTime (Data := Data))
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      FixedMarkerPadding.unpad
        (BivariateTemplateEmitterMachine.appendedOutput
          (liftedFirst selected) (isMarker (Data := Data)) recipes ending
          (FixedMarkerPadding.padded markerCount workspace)))
  exact complete

end FixedMarkerBivariatePipeline
end PeriodicCNF
end LeanTrominoes
