/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteCertificateCNF

/-! # Certificate initialization boundary cases -/
namespace LeanTrominoes.FiniteCertificate

example : ∀ index, CellAllowed [true,false] id 0 index ([true,false] : List Bool)[index]? := by
  apply (cellAllowed_iff _ _ _ _).mpr
  exact ⟨[],by decide,by simp⟩

example : ∀ index, CellAllowed [true] id 2 index ([true,false,true] : List Bool)[index]? := by
  apply (cellAllowed_iff _ _ _ _).mpr
  exact ⟨[false,true],by decide,by simp⟩

example : ¬∀ index, CellAllowed [true] id 1 index ([true,false,true] : List Bool)[index]? := by
  intro accepted
  obtain ⟨certificate,bound,word⟩ := (cellAllowed_iff _ _ _ _).mp accepted
  have lengths := congrArg List.length word
  simp only [List.length_cons,List.length_nil,List.length_append,List.length_map] at lengths
  omega

example : ¬∀ index, CellAllowed [true] id 2 index ([false] : List Bool)[index]? := by
  intro accepted
  have first := accepted 0
  simp [CellAllowed] at first

example : ¬∀ index, CellAllowed [true,false] id 2 index ([true] : List Bool)[index]? := by
  intro accepted
  have second := accepted 1
  simp [CellAllowed] at second

end LeanTrominoes.FiniteCertificate
