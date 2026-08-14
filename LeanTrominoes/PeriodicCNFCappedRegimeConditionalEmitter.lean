/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFixedMarkerThreshold
import LeanTrominoes.PeriodicCNFAffineEmitterPipeline

/-!
# Conditional emission for one capped-count regime

Embed a stable workspace as data in one additional workspace layer, run an
arbitrary input-preserving token emitter, and prefix-mark the result.  Every
new token follows all selected input data, so its tag is the final capped
selected count.  A finite transducer retains original items unconditionally
and retains new tokens exactly in one requested capped-count regime.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace CappedRegimeConditionalEmitter

open AffineEmitterPipeline
open SelectedPrefixMarkerMachine
open UnaryProgramTokens

abbrev Workspace (Data : Type) := AffineEmitterPipeline.Workspace Data
abbrev NestedWorkspace (Data : Type) := Workspace (Workspace Data)
abbrev TaggedWorkspace (cutoff : Nat) (Data : Type) :=
  Tagged cutoff (NestedWorkspace Data)

def nestedSelected {Data : Type} (selected : Data → Bool) :
    NestedWorkspace Data → Bool
  | .inl (.inl data) => selected data
  | _ => false

def flattenItem {Data : Type} {cutoff : Nat} (regime : Nat) :
    TaggedWorkspace cutoff Data → List (Workspace Data)
  | (.inl item, _) => [item]
  | (.inr token, count) =>
      if count.val = regime then [.inr token] else []

def flatten {Data : Type} {cutoff : Nat} (regime : Nat) :
    List (TaggedWorkspace cutoff Data) → List (Workspace Data) :=
  List.flatMap (flattenItem regime)

@[simp]
theorem flatten_append {Data : Type} {cutoff : Nat} (regime : Nat)
    (first second : List (TaggedWorkspace cutoff Data)) :
    flatten regime (first ++ second) =
      flatten regime first ++ flatten regime second := by
  simp [flatten, List.flatMap_append]

@[simp]
theorem selectedCount_nested_embedData {Data : Type}
    (selected : Data → Bool) (workspace : List (Workspace Data)) :
    UnaryPolynomialPaddingMachine.selectedCount (nestedSelected selected)
        (embedData workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  unfold embedData AffineTemplateEmitterMachine.selectedCount
  induction workspace with
  | nil => rfl
  | cons item workspace induction =>
      cases item <;>
        simp [UnaryPolynomialPaddingMachine.selectedCount,
          AffineTemplateEmitterMachine.dataSelected, nestedSelected, induction]

@[simp]
theorem flatten_markAux_embedData {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) (regime : Nat) (count : Count cutoff)
    (workspace : List (Workspace Data)) :
    flatten regime
        (markAux (nestedSelected selected) count (embedData workspace)) =
      workspace := by
  induction workspace generalizing count with
  | nil => rfl
  | cons item workspace induction =>
      simp only [embedData, List.map_cons, markAux, flatten,
        List.flatMap_cons, flattenItem, List.singleton_append]
      congr 1
      simpa only [flatten, embedData] using
        induction
          (nextCount (nestedSelected selected)
            (Sum.inl item : NestedWorkspace Data) count)

@[simp]
theorem markAux_map_tokens {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) (count : Count cutoff)
    (tokens : List Token) :
    markAux (nestedSelected selected) count
        (tokens.map fun token =>
          (Sum.inr token : NestedWorkspace Data)) =
      tokens.map fun token =>
        ((Sum.inr token : NestedWorkspace Data), count) := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp [markAux, nestedSelected, nextCount, induction]

theorem flatten_map_taggedTokens {Data : Type} {cutoff : Nat}
    (regime : Nat) (count : Count cutoff) (tokens : List Token) :
    flatten regime
        (tokens.map fun token =>
          ((Sum.inr token : NestedWorkspace Data), count)) =
      if count.val = regime then
        tokens.map fun token => (Sum.inr token : Workspace Data)
      else [] := by
  unfold flatten
  rw [List.flatMap_map]
  by_cases active : count.val = regime
  · simp [flattenItem, active,
      AffineEmitterPipeline.flatMap_singleton_eq_map]
  · simp [flattenItem, active]

def run {Data : Type} (selected : Data → Bool) (cutoff regime : Nat)
    (branch : List (NestedWorkspace Data) →
      List (NestedWorkspace Data))
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  flatten regime
    (mark (nestedSelected selected) cutoff (branch (embedData workspace)))

/-- Exact conditional behavior, assuming the nested branch preserves its
input and appends the supplied token word at the original selected width. -/
theorem run_eq_if {Data : Type} (selected : Data → Bool)
    (cutoff regime : Nat)
    (branch : List (NestedWorkspace Data) →
      List (NestedWorkspace Data))
    (branchTokens : Nat → List Token)
    (workspace : List (Workspace Data))
    (branchEq : branch (embedData workspace) =
      embedData workspace ++
        (branchTokens
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : NestedWorkspace Data)) :
    run selected cutoff regime branch workspace =
      if min (AffineTemplateEmitterMachine.selectedCount selected workspace)
          cutoff = regime then
        workspace ++
          (branchTokens
            (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
              fun token => (Sum.inr token : Workspace Data)
      else workspace := by
  unfold run
  rw [branchEq]
  unfold mark
  rw [FixedMarkerThreshold.markAux_append, flatten_append,
    flatten_markAux_embedData, markAux_map_tokens,
    flatten_map_taggedTokens,
    countAfter_zeroCount_val, selectedCount_nested_embedData]
  rw [Nat.min_comm cutoff]
  split <;> simp_all

/-- The conditional wrapper is polynomial time whenever its fixed nested
branch is polynomial time. -/
noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data]
    (selected : Data → Bool) (cutoff regime : Nat)
    (branch : List (NestedWorkspace Data) →
      List (NestedWorkspace Data))
    (branchCertificate :
      @TM2ComputableInPolyTime
        (List (NestedWorkspace Data)) (List (NestedWorkspace Data))
        (NestedWorkspace Data) (NestedWorkspace Data) id id branch) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (run selected cutoff regime branch) := by
  let embedded := AffineEmitterPipeline.embedDataComputableInPolyTime
    (Data := Workspace Data)
  let throughBranch := TM2CompositionMachine.computableInPolyTime
    embedded branchCertificate
  let marked := SelectedPrefixMarkerMachine.computableInPolyTime
    (Data := NestedWorkspace Data) (nestedSelected selected) cutoff
  let throughMark := TM2CompositionMachine.computableInPolyTime
    throughBranch marked
  let flattened := FiniteBlockTransducer.computableInPolyTime
    (flattenItem (Data := Data) (cutoff := cutoff) regime)
  let complete := TM2CompositionMachine.computableInPolyTime
    throughMark flattened
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      flatten regime
        (mark (nestedSelected selected) cutoff
          (branch (embedData workspace))))
  exact complete

end CappedRegimeConditionalEmitter
end PeriodicCNF
end LeanTrominoes
