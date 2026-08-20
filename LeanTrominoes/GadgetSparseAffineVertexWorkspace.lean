/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAffineVertexTokens
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Retained-source affine vertex-token expansion -/

namespace LeanTrominoes
namespace GadgetSparseAffineVertexWorkspace

abbrev FirstWorkspace (Source : Type) :=
  Source ⊕ GadgetSparseAffineVertexTokens.Token

abbrev SecondWorkspace (Source : Type) :=
  Source ⊕ GadgetSparseAffineVertexTokens.IntermediateToken

abbrev ThirdWorkspace (Source : Type) :=
  Source ⊕ GadgetSparseAffineVertexTokens.PreparedToken

abbrev OutputWorkspace (Source : Type) :=
  Source ⊕ GadgetSparseAssignmentTokens.Token

def firstBlock {Source : Type} :
    FirstWorkspace Source → List (SecondWorkspace Source)
  | .inl source => [.inl source]
  | .inr token =>
      (GadgetSparseAffineVertexTokens.firstBlock token).map Sum.inr

def secondBlock {Source : Type} :
    SecondWorkspace Source → List (ThirdWorkspace Source)
  | .inl source => [.inl source]
  | .inr token =>
      (GadgetSparseAffineVertexTokens.secondBlock token).map Sum.inr

def thirdBlock {Source : Type} :
    ThirdWorkspace Source → List (OutputWorkspace Source)
  | .inl source => [.inl source]
  | .inr token =>
      (GadgetSparseAffineVertexTokens.thirdBlock token).map Sum.inr

def firstExpand {Source : Type}
    (workspace : List (FirstWorkspace Source)) :
    List (SecondWorkspace Source) :=
  workspace.flatMap firstBlock

def secondExpand {Source : Type}
    (workspace : List (SecondWorkspace Source)) :
    List (ThirdWorkspace Source) :=
  workspace.flatMap secondBlock

def thirdExpand {Source : Type}
    (workspace : List (ThirdWorkspace Source)) :
    List (OutputWorkspace Source) :=
  workspace.flatMap thirdBlock

/-- The complete staged workspace conversion preserves source symbols and
expands only right-side affine request tokens. -/
def expand {Source : Type}
    (workspace : List (FirstWorkspace Source)) :
    List (OutputWorkspace Source) :=
  thirdExpand (secondExpand (firstExpand workspace))

@[simp] theorem firstExpand_append {Source : Type}
    (first second : List (FirstWorkspace Source)) :
    firstExpand (first ++ second) = firstExpand first ++ firstExpand second := by
  simp [firstExpand]

@[simp] theorem secondExpand_append {Source : Type}
    (first second : List (SecondWorkspace Source)) :
    secondExpand (first ++ second) =
      secondExpand first ++ secondExpand second := by
  simp [secondExpand]

@[simp] theorem thirdExpand_append {Source : Type}
    (first second : List (ThirdWorkspace Source)) :
    thirdExpand (first ++ second) = thirdExpand first ++ thirdExpand second := by
  simp [thirdExpand]

@[simp] theorem firstExpand_map_inl {Source : Type}
    (source : List Source) :
    firstExpand (source.map Sum.inl) = source.map Sum.inl := by
  induction source with
  | nil => rfl
  | cons symbol source induction =>
      rw [List.map_cons]
      change [Sum.inl symbol] ++ firstExpand (source.map Sum.inl) = _
      rw [induction]
      rfl

@[simp] theorem secondExpand_map_inl {Source : Type}
    (source : List Source) :
    secondExpand (source.map Sum.inl) = source.map Sum.inl := by
  induction source with
  | nil => rfl
  | cons symbol source induction =>
      rw [List.map_cons]
      change [Sum.inl symbol] ++ secondExpand (source.map Sum.inl) = _
      rw [induction]
      rfl

@[simp] theorem thirdExpand_map_inl {Source : Type}
    (source : List Source) :
    thirdExpand (source.map Sum.inl) = source.map Sum.inl := by
  induction source with
  | nil => rfl
  | cons symbol source induction =>
      rw [List.map_cons]
      change [Sum.inl symbol] ++ thirdExpand (source.map Sum.inl) = _
      rw [induction]
      rfl

@[simp] theorem firstExpand_map_inr {Source : Type}
    (tokens : List GadgetSparseAffineVertexTokens.Token) :
    firstExpand (Source := Source) (tokens.map Sum.inr) =
      (GadgetSparseAffineVertexTokens.firstExpand tokens).map Sum.inr := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      rw [List.map_cons]
      change
        (GadgetSparseAffineVertexTokens.firstBlock token).map Sum.inr ++
            firstExpand (tokens.map Sum.inr) =
          (GadgetSparseAffineVertexTokens.firstBlock token ++
            GadgetSparseAffineVertexTokens.firstExpand tokens).map Sum.inr
      rw [induction, List.map_append]

@[simp] theorem secondExpand_map_inr {Source : Type}
    (tokens : List GadgetSparseAffineVertexTokens.IntermediateToken) :
    secondExpand (Source := Source) (tokens.map Sum.inr) =
      (GadgetSparseAffineVertexTokens.secondExpand tokens).map Sum.inr := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      rw [List.map_cons]
      change
        (GadgetSparseAffineVertexTokens.secondBlock token).map Sum.inr ++
            secondExpand (tokens.map Sum.inr) =
          (GadgetSparseAffineVertexTokens.secondBlock token ++
            GadgetSparseAffineVertexTokens.secondExpand tokens).map Sum.inr
      rw [induction, List.map_append]

@[simp] theorem thirdExpand_map_inr {Source : Type}
    (tokens : List GadgetSparseAffineVertexTokens.PreparedToken) :
    thirdExpand (Source := Source) (tokens.map Sum.inr) =
      (GadgetSparseAffineVertexTokens.thirdExpand tokens).map Sum.inr := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      rw [List.map_cons]
      change
        (GadgetSparseAffineVertexTokens.thirdBlock token).map Sum.inr ++
            thirdExpand (tokens.map Sum.inr) =
          (GadgetSparseAffineVertexTokens.thirdBlock token ++
            GadgetSparseAffineVertexTokens.thirdExpand tokens).map Sum.inr
      rw [induction, List.map_append]

/-- On a retained-source workspace, staged conversion changes only the
appended request word. -/
theorem expand_map_inl_append_map_inr {Source : Type}
    (source : List Source)
    (tokens : List GadgetSparseAffineVertexTokens.Token) :
    expand (source.map Sum.inl ++ tokens.map Sum.inr) =
      source.map Sum.inl ++
        (GadgetSparseAffineVertexTokens.expand tokens).map Sum.inr := by
  unfold expand GadgetSparseAffineVertexTokens.expand
  rw [firstExpand_append, firstExpand_map_inl, firstExpand_map_inr,
    secondExpand_append, secondExpand_map_inl, secondExpand_map_inr,
    thirdExpand_append, thirdExpand_map_inl, thirdExpand_map_inr]

/-- Expanding a retained compact request appends the expanded canonical
record word while preserving the original source. -/
@[simp] theorem expand_appended {Source : Type}
    (requests : List Source →
      List GadgetSparseAffineVertexTokens.Token)
    (source : List Source) :
    expand (RetainedInputAppendPipeline.appended requests source) =
      RetainedInputAppendPipeline.appended
        (fun input => GadgetSparseAffineVertexTokens.expand
          (requests input)) source := by
  unfold RetainedInputAppendPipeline.appended
    RetainedInputAppendPipeline.embed
  exact expand_map_inl_append_map_inr source (requests source)

end GadgetSparseAffineVertexWorkspace
end LeanTrominoes
