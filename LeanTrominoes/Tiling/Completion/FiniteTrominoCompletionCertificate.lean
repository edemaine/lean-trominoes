/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteTrominoRegionCertificate
import LeanTrominoes.Tiling.Completion.FiniteCompletionDecision

/-! # Binary certificates for finite-preplacement tromino completion

One bit selects each candidate tromino meeting the bounding box. The proved
exterior extension theorem makes a valid finite cover sufficient for a plane
completion, including tiles that protrude beyond the box.
-/
namespace LeanTrominoes.Tromino.FiniteWitness
open FiniteRegion (candidateList select select_encode candidateList_eq candidateList_length)

def boxList (r : Nat) : List Cell :=
  (List.range (2*r+1)).flatMap fun x => (List.range (2*r+1)).map fun y =>
    ((x : Int)-(r : Int),(y : Int)-(r : Int))

@[simp] theorem boxList_toFinset (r : Nat) : (boxList r).toFinset=box r := by
  ext cell
  simp [boxList,box,interval,List.mem_flatMap,List.mem_map,Finset.mem_image]
  constructor
  · rintro ⟨x,hx,y,hy,equal⟩
    exact ⟨⟨x,hx,congrArg Prod.fst equal⟩,⟨y,hy,congrArg Prod.snd equal⟩⟩
  · rintro ⟨⟨x,hx,eqX⟩,⟨y,hy,eqY⟩⟩
    exact ⟨x,hx,y,hy,Prod.ext eqX eqY⟩

@[simp] theorem boxList_length (r : Nat) : (boxList r).length=(2*r+1)^2 := by
  simp [boxList,pow_two]

def checkCertificate (t : Tromino) (r : Nat) (prefill : Finset (Finset Cell))
    (bits : List Bool) : Bool :=
  decide (Valid t (box r) prefill (select (candidateList t (boxList r)) bits))

private theorem encode_valid (t : Tromino) (r : Nat) (prefill tiles : Finset (Finset Cell))
    (valid : Valid t (box r) prefill tiles) :
    ∃ bits : List Bool, bits.length≤24*(2*r+1)^2 ∧ checkCertificate t r prefill bits=true := by
  refine ⟨(candidateList t (boxList r)).map fun tile => decide (tile∈tiles),by simp,?_⟩
  have selected : select (candidateList t (boxList r))
      ((candidateList t (boxList r)).map fun tile => decide (tile∈tiles))=tiles := by
    rw [select_encode,candidateList_eq,boxList_toFinset]
    ext tile
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨valid.1 h,h⟩⟩
  simpa [checkCertificate,selected] using valid

theorem completion_iff_box_certificate (t : Tromino) (r : Nat) (prefill : Finset (Finset Cell))
    (meets : ∀ tile∈prefill, ∃ cell∈box r, cell∈tile) :
    t.Completable Set.univ (prefill : Set (Finset Cell)) ↔
      ∃ bits : List Bool, bits.length≤24*(2*r+1)^2 ∧ checkCertificate t r prefill bits=true := by
  constructor
  · intro completion
    obtain ⟨tiles,valid⟩ := of_completion t (box r) prefill meets completion
    exact encode_valid t r prefill tiles valid
  · rintro ⟨bits,_,checked⟩
    exact completion_of_witness (t := t) (by simpa [checkCertificate] using checked)

/-- For arbitrary finite preplacements, the certificate length is at most
24 times the area of their canonical bounding box. -/
theorem completion_iff_bounded_certificate (t : Tromino) (prefill : Finset (Finset Cell)) :
    t.Completable Set.univ (prefill : Set (Finset Cell)) ↔
      ∃ bits : List Bool, bits.length≤24*(2*radius prefill+1)^2 ∧
        checkCertificate t (radius prefill) prefill bits=true := by
  constructor
  · intro completion
    obtain ⟨tiles,valid⟩ := of_completion t (box (radius prefill)) prefill
      (completion_meets_box t prefill completion) completion
    exact encode_valid t (radius prefill) prefill tiles valid
  · rintro ⟨bits,_,checked⟩
    exact completion_of_witness (t := t) (by simpa [checkCertificate] using checked)

end LeanTrominoes.Tromino.FiniteWitness
