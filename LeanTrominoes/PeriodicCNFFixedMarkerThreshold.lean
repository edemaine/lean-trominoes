/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFixedMarkerBivariatePipeline
import LeanTrominoes.SelectedPrefixMarkerIntervals

/-!
# One-sentinel threshold selectors

Append one temporary marker after a stable workspace and prefix-mark the
expanded word by an original selected class.  The sentinel's capped prefix
tag is exactly `min(selectedCount, cutoff)`, so it supplies complementary
zero-or-one selectors for widths below and at the cutoff.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF
namespace FixedMarkerThreshold

open AffineEmitterPipeline
open SelectedPrefixMarkerMachine

abbrev Workspace (Data : Type) := FixedMarkerPadding.Workspace Data
abbrev ExpandedData (Data : Type) := FixedMarkerPadding.MarkedData Data
abbrev ExpandedWorkspace (Data : Type) :=
  FixedMarkerPadding.MarkedWorkspace Data
abbrev TaggedWorkspace (cutoff : Nat) (Data : Type) :=
  Tagged cutoff (ExpandedWorkspace Data)

def liftedSelected {Data : Type} (selected : Data → Bool) :
    ExpandedData Data → Bool :=
  FixedMarkerBivariatePipeline.liftedFirst selected

def workspaceSelected {Data : Type} (selected : Data → Bool) :
    ExpandedWorkspace Data → Bool :=
  AffineTemplateEmitterMachine.dataSelected (liftedSelected selected)

def isSentinelItem {Data : Type} : ExpandedWorkspace Data → Bool
  | .inl (.inr _) => true
  | _ => false

def sentinelBelow {Data : Type} {cutoff : Nat} :
    TaggedWorkspace cutoff Data → Bool
  | (item, count) => isSentinelItem item && decide (count.val < cutoff)

def sentinelAt {Data : Type} {cutoff : Nat} :
    TaggedWorkspace cutoff Data → Bool
  | (item, count) => isSentinelItem item && decide (count.val = cutoff)

theorem markAux_append {Item : Type} {cutoff : Nat}
    (selected : Item → Bool) (count : Count cutoff)
    (first second : List Item) :
    markAux selected count (first ++ second) =
      markAux selected count first ++
        markAux selected (countAfter selected count first) second := by
  induction first generalizing count with
  | nil => rfl
  | cons item first induction =>
      simp [markAux, countAfter, induction]

theorem selectedCount_liftedWorkspace {Data : Type}
    (selected : Data → Bool) (workspace : List (Workspace Data)) :
    UnaryPolynomialPaddingMachine.selectedCount (workspaceSelected selected)
        (workspace.map FixedMarkerPadding.liftItem) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  change BivariateTemplateEmitterMachine.selectedCount
      (FixedMarkerBivariatePipeline.liftedFirst selected)
        (workspace.map FixedMarkerPadding.liftItem) =
    BivariateTemplateEmitterMachine.selectedCount selected workspace
  exact FixedMarkerBivariatePipeline.selectedCount_liftItems
    selected workspace

theorem mark_padded_eq {Data : Type} (selected : Data → Bool) (cutoff : Nat)
    (workspace : List (Workspace Data)) :
    mark (workspaceSelected selected) cutoff
        (FixedMarkerPadding.padded 1 workspace) =
      mark (workspaceSelected selected) cutoff
          (workspace.map FixedMarkerPadding.liftItem) ++
        [(FixedMarkerPadding.marker,
          countAfter (workspaceSelected selected) (zeroCount cutoff)
            (workspace.map FixedMarkerPadding.liftItem))] := by
  rw [FixedMarkerPadding.padded_eq]
  simp only [List.replicate_one]
  unfold mark
  rw [markAux_append]
  simp [markAux, workspaceSelected, liftedSelected,
    FixedMarkerPadding.marker]

theorem selectedCount_sentinelBelow_lifts {Data : Type}
    (selected : Data → Bool) {cutoff : Nat} (count : Count cutoff)
    (workspace : List (Workspace Data)) :
    UnaryPolynomialPaddingMachine.selectedCount sentinelBelow
        (markAux (workspaceSelected selected) count
          (workspace.map FixedMarkerPadding.liftItem)) = 0 := by
  induction workspace generalizing count with
  | nil => rfl
  | cons item workspace induction =>
      cases item <;>
        simp [markAux, sentinelBelow, isSentinelItem,
          FixedMarkerPadding.liftItem, induction]

theorem selectedCount_sentinelAt_lifts {Data : Type}
    (selected : Data → Bool) {cutoff : Nat} (count : Count cutoff)
    (workspace : List (Workspace Data)) :
    UnaryPolynomialPaddingMachine.selectedCount sentinelAt
        (markAux (workspaceSelected selected) count
          (workspace.map FixedMarkerPadding.liftItem)) = 0 := by
  induction workspace generalizing count with
  | nil => rfl
  | cons item workspace induction =>
      cases item <;>
        simp [markAux, sentinelAt, isSentinelItem,
          FixedMarkerPadding.liftItem, induction]

theorem selectedCount_append {Item : Type} (selected : Item → Bool)
    (first second : List Item) :
    UnaryPolynomialPaddingMachine.selectedCount selected (first ++ second) =
      UnaryPolynomialPaddingMachine.selectedCount selected first +
        UnaryPolynomialPaddingMachine.selectedCount selected second := by
  exact AffineEmitterPipeline.unarySelectedCount_append selected first second

/-- The below-cutoff sentinel selector is the exact strict comparison bit. -/
@[simp]
theorem selectedCount_sentinelBelow_mark_padded {Data : Type}
    (selected : Data → Bool) (cutoff : Nat)
    (workspace : List (Workspace Data)) :
    UnaryPolynomialPaddingMachine.selectedCount sentinelBelow
        (mark (workspaceSelected selected) cutoff
          (FixedMarkerPadding.padded 1 workspace)) =
      if AffineTemplateEmitterMachine.selectedCount selected workspace < cutoff
      then 1 else 0 := by
  rw [mark_padded_eq, selectedCount_append]
  unfold mark
  rw [selectedCount_sentinelBelow_lifts]
  by_cases below :
      AffineTemplateEmitterMachine.selectedCount selected workspace < cutoff
  · simp [UnaryPolynomialPaddingMachine.selectedCount, sentinelBelow,
      isSentinelItem, FixedMarkerPadding.marker, countAfter_zeroCount_val,
      selectedCount_liftedWorkspace, below,
      Nat.min_eq_right (Nat.le_of_lt below)]
  · have reached : cutoff ≤
        AffineTemplateEmitterMachine.selectedCount selected workspace :=
      Nat.le_of_not_gt below
    simp [UnaryPolynomialPaddingMachine.selectedCount, sentinelBelow,
      isSentinelItem, FixedMarkerPadding.marker, countAfter_zeroCount_val,
      selectedCount_liftedWorkspace, below, Nat.min_eq_left reached]

/-- The at-cutoff sentinel selector is the complementary weak comparison
bit. -/
@[simp]
theorem selectedCount_sentinelAt_mark_padded {Data : Type}
    (selected : Data → Bool) (cutoff : Nat)
    (workspace : List (Workspace Data)) :
    UnaryPolynomialPaddingMachine.selectedCount sentinelAt
        (mark (workspaceSelected selected) cutoff
          (FixedMarkerPadding.padded 1 workspace)) =
      if cutoff ≤ AffineTemplateEmitterMachine.selectedCount selected workspace
      then 1 else 0 := by
  rw [mark_padded_eq, selectedCount_append]
  unfold mark
  rw [selectedCount_sentinelAt_lifts]
  by_cases reached : cutoff ≤
      AffineTemplateEmitterMachine.selectedCount selected workspace
  · simp [UnaryPolynomialPaddingMachine.selectedCount, sentinelAt,
      isSentinelItem, FixedMarkerPadding.marker, countAfter_zeroCount_val,
      selectedCount_liftedWorkspace, reached]
  · have below :
        AffineTemplateEmitterMachine.selectedCount selected workspace < cutoff :=
      Nat.lt_of_not_ge reached
    simp [UnaryPolynomialPaddingMachine.selectedCount, sentinelAt,
      isSentinelItem, FixedMarkerPadding.marker, countAfter_zeroCount_val,
      selectedCount_liftedWorkspace, reached,
      Nat.min_eq_right (Nat.le_of_lt below), Nat.ne_of_lt below]

end FixedMarkerThreshold
end PeriodicCNF
end LeanTrominoes
