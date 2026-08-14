/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFAffineEmitterPipeline
import LeanTrominoes.SelectedPrefixMarkerTime
import LeanTrominoes.TM2CompositionMachine

/-!
# Input-preserving marked affine emitter pipelines

Some affine phase schedules need capped selected-prefix tags.  This wrapper
marks a shared prepared-data/token workspace, embeds the tags for the ordinary
affine pipeline, executes a fixed phase list, and removes the tags again.
Existing tokens are never selected and remain in place; newly emitted tokens
are appended.  The complete wrapper is polynomial-time.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace MarkedAffineEmitterPipeline

open AffineEmitterPipeline
open SelectedPrefixMarkerMachine
open UnaryProgramTokens

abbrev MarkedWorkspace (cutoff : Nat) (Data : Type) :=
  Tagged cutoff (Workspace Data)

abbrev NestedWorkspace (cutoff : Nat) (Data : Type) :=
  Workspace (MarkedWorkspace cutoff Data)

/-- Delete prefix tags while flattening the nested token alphabet back to the
shared workspace alphabet. -/
def flatten {Data : Type} {cutoff : Nat} :
    List (NestedWorkspace cutoff Data) → List (Workspace Data) :=
  List.flatMap fun
    | .inl (item, _) => [item]
    | .inr token => [.inr token]

/-- Mark, run the fixed phases, and return the untagged input with the emitted
token suffix appended. -/
def run {Data : Type} (selected : Workspace Data → Bool) (cutoff : Nat)
    (phases : List (Phase (MarkedWorkspace cutoff Data)))
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  flatten (runAll phases (embedData (mark selected cutoff workspace)))

theorem flatten_embedData_markAux {Data : Type} {cutoff : Nat}
    (selected : Workspace Data → Bool) (count : Count cutoff)
    (workspace : List (Workspace Data)) :
    flatten (embedData (markAux selected count workspace)) = workspace := by
  unfold flatten embedData
  induction workspace generalizing count with
  | nil => rfl
  | cons item workspace induction =>
      simp only [markAux, List.map_cons, List.flatMap_cons]
      rw [induction]
      rfl

@[simp]
theorem flatten_embedData_mark {Data : Type} (selected : Workspace Data → Bool)
    (cutoff : Nat) (workspace : List (Workspace Data)) :
    flatten (embedData (mark selected cutoff workspace)) = workspace := by
  exact flatten_embedData_markAux selected (zeroCount cutoff) workspace

@[simp]
theorem flatten_map_tokens {Data : Type} {cutoff : Nat}
    (tokens : List Token) :
    flatten
        (tokens.map fun token =>
          (Sum.inr token : NestedWorkspace cutoff Data)) =
      tokens.map fun token => (Sum.inr token : Workspace Data) := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      change (Sum.inr token : Workspace Data) ::
          flatten
            (tokens.map fun token =>
              (Sum.inr token : NestedWorkspace cutoff Data)) =
        (Sum.inr token : Workspace Data) ::
          tokens.map fun token => (Sum.inr token : Workspace Data)
      rw [induction]

/-- Exact input-preserving behavior on an arbitrary existing workspace. -/
theorem run_eq_append {Data : Type} (selected : Workspace Data → Bool)
    (cutoff : Nat) (phases : List (Phase (MarkedWorkspace cutoff Data)))
    (workspace : List (Workspace Data)) :
    run selected cutoff phases workspace =
      workspace ++
        (emittedAll phases (mark selected cutoff workspace)).map
          fun token => (Sum.inr token : Workspace Data) := by
  unfold run
  rw [runAll_embedData]
  unfold flatten
  rw [List.flatMap_append]
  change flatten (embedData (mark selected cutoff workspace)) ++
      flatten
        ((emittedAll phases (mark selected cutoff workspace)).map
          fun token =>
            (Sum.inr token : NestedWorkspace cutoff Data)) = _
  rw [flatten_embedData_mark, flatten_map_tokens]

/-- The complete mark/embed/emit/untag wrapper is polynomial-time. -/
noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data]
    (selected : Workspace Data → Bool) (cutoff : Nat)
    (phases : List (Phase (MarkedWorkspace cutoff Data))) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (run selected cutoff phases) := by
  let marker := SelectedPrefixMarkerMachine.computableInPolyTime
    (Data := Workspace Data) selected cutoff
  let embed := AffineEmitterPipeline.embedDataComputableInPolyTime
    (Data := MarkedWorkspace cutoff Data)
  let markedAndEmbedded :=
    TM2CompositionMachine.computableInPolyTime marker embed
  let printer := AffineEmitterPipeline.runAllComputableInPolyTime phases
  let printed :=
    TM2CompositionMachine.computableInPolyTime markedAndEmbedded printer
  let untag := FiniteBlockTransducer.computableInPolyTime
    (fun item : NestedWorkspace cutoff Data =>
      match item with
      | .inl (workspaceItem, _) => [workspaceItem]
      | .inr token => [(Sum.inr token : Workspace Data)])
  let complete := TM2CompositionMachine.computableInPolyTime printed untag
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      flatten (runAll phases (embedData (mark selected cutoff workspace))))
  exact complete

end MarkedAffineEmitterPipeline
end PeriodicCNF
end LeanTrominoes
