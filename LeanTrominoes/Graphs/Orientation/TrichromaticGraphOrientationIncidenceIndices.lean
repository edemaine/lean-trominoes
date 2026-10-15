/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationLineWindow

/-! # Numeric enumeration of source and target incidences, including loops -/
namespace LeanTrominoes.TrichromaticGraphOrientation

private theorem pair_flatMap_length {A B : Type*} (xs : List A) (left right : A → B) :
    (xs.flatMap fun x => [left x,right x]).length = 2*xs.length := by
  simp [List.length_flatMap,Nat.mul_comm]

private theorem pair_flatMap_get {A B : Type*} (xs : List A) (left right : A → B)
    (index : Nat) (bound : index < 2*xs.length) :
    (xs.flatMap fun x => [left x,right x])[index]'(by rw [pair_flatMap_length]; exact bound) =
      if index%2 = 0 then left (xs[index/2]'(by omega)) else right (xs[index/2]'(by omega)) := by
  induction xs generalizing index with
  | nil => simp at bound
  | cons x xs ih =>
    cases index with
    | zero => simp
    | succ index =>
      cases index with
      | zero => simp
      | succ index =>
        have small : index < 2*xs.length := by simp only [List.length_cons] at bound; omega
        have division : (index+1+1)/2 = index/2+1 := by omega
        have residue : (index+1+1)%2 = index%2 := by omega
        simpa only [List.flatMap_cons,List.cons_append,List.nil_append,List.getElem_cons_succ,
          division,residue] using ih index small

def incidenceAt (input : Input) (index : Nat) : End :=
  let record := input.2.getD (index/2) (⟨0,0,(0,0)⟩,.red)
  if index%2 = 0 then (record.1.source,(⟨index/2,(0,0),false⟩,record.2))
  else (record.1.target,(⟨index/2,Cell.sub (0,0) record.1.offset,true⟩,record.2))

theorem ends_eq_incidenceIndices (input : Input) :
    ends input = (List.range (2*input.2.length)).map (incidenceAt input) := by
  have length : (ends input).length = 2*input.2.length := by
    simpa [ends,edgeEnds] using pair_flatMap_length input.2.zipIdx
      (fun tagged => ((tagged.1.1.source,(⟨tagged.2,(0,0),false⟩,tagged.1.2)) : End))
      (fun tagged => ((tagged.1.1.target,(⟨tagged.2,Cell.sub (0,0) tagged.1.1.offset,true⟩,tagged.1.2)) : End))
  apply List.ext_getElem
  · simpa using length
  · intro index leftBound rightBound
    have small : index < 2*input.2.length := by omega
    have halfBound : index/2 < input.2.length := by omega
    have point := pair_flatMap_get input.2.zipIdx
      (fun tagged => ((tagged.1.1.source,(⟨tagged.2,(0,0),false⟩,tagged.1.2)) : End))
      (fun tagged => ((tagged.1.1.target,(⟨tagged.2,Cell.sub (0,0) tagged.1.1.offset,true⟩,tagged.1.2)) : End))
      index (by simpa only [List.length_zipIdx] using small)
    change (ends input)[index]'leftBound = _ at point
    simpa only [List.getElem_map,List.getElem_range,incidenceAt,
      List.getD_eq_getElem _ _ halfBound,List.getElem_zipIdx,Nat.zero_add,Nat.add_zero] using point

theorem incidenceAt_atom (input : Input) (index : Nat) : (incidenceAt input index).2.1.atom = index/2 := by
  unfold incidenceAt
  split <;> rfl

theorem incidenceAt_polarity (input : Input) (index : Nat) :
    (incidenceAt input index).2.1.value = decide (index%2 ≠ 0) := by
  unfold incidenceAt
  split <;> simp_all

theorem incidenceAt_injective (input : Input) : Function.Injective (incidenceAt input) := by
  intro first second equal
  have quotient := congrArg (fun incidence : End => incidence.2.1.atom) equal
  have polarity := congrArg (fun incidence : End => incidence.2.1.value) equal
  rw [incidenceAt_atom,incidenceAt_atom] at quotient
  rw [incidenceAt_polarity,incidenceAt_polarity] at polarity
  have residue : first%2 = second%2 := by
    by_cases firstEven : first%2 = 0 <;> by_cases secondEven : second%2 = 0 <;>
      simp [firstEven,secondEven] at polarity <;> omega
  omega

end LeanTrominoes.TrichromaticGraphOrientation
