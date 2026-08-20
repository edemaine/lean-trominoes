/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAffineVertexWorkspace
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2CompositionMachine

/-! # Polynomial-time retained-source affine vertex expansion -/

noncomputable section

namespace LeanTrominoes
namespace GadgetSparseAffineVertexWorkspace

open Computability Turing

private local instance firstWorkspaceInhabited (Source : Type) :
    Inhabited (FirstWorkspace Source) :=
  ⟨.inr default⟩

private local instance secondWorkspaceInhabited (Source : Type) :
    Inhabited (SecondWorkspace Source) :=
  ⟨.inr default⟩

private local instance thirdWorkspaceInhabited (Source : Type) :
    Inhabited (ThirdWorkspace Source) :=
  ⟨.inr default⟩

private local instance outputWorkspaceInhabited (Source : Type) :
    Inhabited (OutputWorkspace Source) :=
  ⟨.inr default⟩

noncomputable def firstComputableInPolyTime
    {Source : Type} [Fintype Source] :
    TM2ComputableInPolyTime id id
      (firstExpand : List (FirstWorkspace Source) →
        List (SecondWorkspace Source)) :=
  FiniteBlockTransducer.computableInPolyTime firstBlock

noncomputable def secondComputableInPolyTime
    {Source : Type} [Fintype Source] :
    TM2ComputableInPolyTime id id
      (secondExpand : List (SecondWorkspace Source) →
        List (ThirdWorkspace Source)) :=
  FiniteBlockTransducer.computableInPolyTime secondBlock

noncomputable def thirdComputableInPolyTime
    {Source : Type} [Fintype Source] :
    TM2ComputableInPolyTime id id
      (thirdExpand : List (ThirdWorkspace Source) →
        List (OutputWorkspace Source)) :=
  FiniteBlockTransducer.computableInPolyTime thirdBlock

/-- Retained-source affine expansion is a composition of the same three
small factor-12 block substitutions as the output-only expander. -/
noncomputable def computableInPolyTime
    {Source : Type} [Fintype Source] :
    TM2ComputableInPolyTime id id
      (expand : List (FirstWorkspace Source) →
        List (OutputWorkspace Source)) := by
  change TM2ComputableInPolyTime id id
    (fun workspace => thirdExpand (secondExpand (firstExpand workspace)))
  exact TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (firstComputableInPolyTime (Source := Source))
      (secondComputableInPolyTime (Source := Source)))
    (thirdComputableInPolyTime (Source := Source))

end GadgetSparseAffineVertexWorkspace
end LeanTrominoes
