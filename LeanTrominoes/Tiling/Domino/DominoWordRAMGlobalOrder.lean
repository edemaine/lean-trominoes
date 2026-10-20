/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCandidate
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointCandidate

/-! # Prefix order and exact storage accounting for the candidate scan -/
namespace LeanTrominoes.Domino.WordRAM.Driver.Order
open PeriodicLatticeGraph
variable {n d : Nat}

noncomputable def block (B : BasisData n d) (u : Fin n) (direction : Fin d) (v : Fin n) :=
  (DoubleCover.phases d).flatMap fun phase => EndpointWriter.candidateWords B (u,direction,v,phase)
noncomputable def targets (B : BasisData n d) (u : Fin n) (direction : Fin d) (vs : List (Fin n)) :=
  vs.flatMap (block B u direction)
noncomputable def directions (B : BasisData n d) (u : Fin n) (dirs : List (Fin d)) :=
  dirs.flatMap fun direction => targets B u direction (List.finRange n)
noncomputable def sources (B : BasisData n d) (us : List (Fin n)) :=
  us.flatMap fun u => directions B u (List.finRange d)
noncomputable def scanPrefix (B : BasisData n d) (u : Fin n) (dirs : List (Fin d)) (direction : Fin d) (v : Nat) :=
  sources B ((List.finRange n).take u.val)++directions B u dirs++targets B u direction ((List.finRange n).take v)

 theorem block_length (B : BasisData n d) (u : Fin n) (direction : Fin d) (v : Fin n) :
    (block B u direction v).length=2*2^d := by
  simp [block,List.length_flatMap,EndpointWriter.candidateWords_length]
  omega
 theorem targets_length (B : BasisData n d) (u : Fin n) (direction : Fin d) (vs : List (Fin n)) :
    (targets B u direction vs).length=vs.length*(2*2^d) := by
  simp [targets,List.length_flatMap,block_length]
 theorem directions_length (B : BasisData n d) (u : Fin n) (dirs : List (Fin d)) :
    (directions B u dirs).length=dirs.length*n*(2*2^d) := by
  simp [directions,List.length_flatMap,targets_length]
  ring
 theorem sources_length (B : BasisData n d) (us : List (Fin n)) :
    (sources B us).length=us.length*d*n*(2*2^d) := by
  simp [sources,List.length_flatMap,directions_length]
  ring
 theorem prefix_length (B : BasisData n d) (u : Fin n) (dirs : List (Fin d)) (direction : Fin d) (v : Nat) (within : v≤n) :
    (scanPrefix B u dirs direction v).length=(u.val*d*n+dirs.length*n+v)*(2*2^d) := by
  have hu : u.val≤n := Nat.le_of_lt u.isLt
  simp [scanPrefix,List.length_append,sources_length,directions_length,targets_length,List.length_take,hu,within]
  ring

 theorem take_finRange_step (i : Nat) (hi : i<n) :
    (List.finRange n).take (i+1)=(List.finRange n).take i++[⟨i,hi⟩] := by
  rw [List.take_add_one,List.getElem?_eq_getElem (by simpa)]
  simp
 theorem targets_append (B : BasisData n d) (u : Fin n) (direction : Fin d) (vs ws : List (Fin n)) :
    targets B u direction (vs++ws)=targets B u direction vs++targets B u direction ws := List.flatMap_append
 theorem directions_append (B : BasisData n d) (u : Fin n) (first rest : List (Fin d)) :
    directions B u (first++rest)=directions B u first++directions B u rest := List.flatMap_append
 theorem sources_append (B : BasisData n d) (first rest : List (Fin n)) :
    sources B (first++rest)=sources B first++sources B rest := List.flatMap_append
 theorem prefix_step (B : BasisData n d) (u : Fin n) (dirs : List (Fin d)) (direction : Fin d) (v : Nat) (within : v<n) :
    scanPrefix B u dirs direction (v+1)=scanPrefix B u dirs direction v++block B u direction ⟨v,within⟩ := by
  simp only [scanPrefix,take_finRange_step v within,targets_append,targets,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
 theorem targets_complete (B : BasisData n d) (u : Fin n) (direction : Fin d) :
    targets B u direction ((List.finRange n).take n)=targets B u direction (List.finRange n) := by
  rw [show (List.finRange n).take n=List.finRange n by simpa only [List.length_finRange] using (List.take_length (l:=List.finRange n))]
 theorem prefix_next_direction (B : BasisData n d) (u : Fin n) (dirs : List (Fin d)) (direction next : Fin d) :
    scanPrefix B u (dirs++[direction]) next 0=scanPrefix B u dirs direction n := by
  have all : (List.finRange n).take n=List.finRange n := by simpa only [List.length_finRange] using (List.take_length (l:=List.finRange n))
  simp [scanPrefix,all,directions,targets,List.flatMap_append,List.append_assoc]
 theorem sources_complete (B : BasisData n d) :
    sources B (List.finRange n)=(PaddedGraph.candidates n d).flatMap (EndpointWriter.candidateWords B) := by
  dsimp [sources,directions,targets,block]
  simp [PaddedGraph.candidates,List.flatMap_assoc,List.flatMap_map]
  rfl

noncomputable def spaceSum (dirs : List (Fin d)) := (dirs.map Binary.Candidate.space).sum
noncomputable def scanSpace (d : Nat) := spaceSum (List.finRange d)
noncomputable def frontier (base length u : Nat) (dirs : List (Fin d)) (direction : Fin d) (v : Nat) :=
  base+(u*n*scanSpace d+n*spaceSum dirs+v*Binary.Candidate.space direction)*length

 theorem spaceSum_append (dirs rest : List (Fin d)) : spaceSum (dirs++rest)=spaceSum dirs+spaceSum rest := by
  simp [spaceSum]
 theorem frontier_step (base length u : Nat) (dirs : List (Fin d)) (direction : Fin d) (v : Nat) :
    frontier (n:=n) base length u dirs direction (v+1)=frontier (n:=n) base length u dirs direction v+Binary.Candidate.space direction*length := by
  unfold frontier; ring
 theorem frontier_next_direction (base length u : Nat) (dirs : List (Fin d)) (direction next : Fin d) :
    frontier (n:=n) base length u (dirs++[direction]) next 0=frontier (n:=n) base length u dirs direction n := by
  simp only [frontier,spaceSum,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.zero_mul]
  ring
 theorem frontier_next_source (base length u : Nat) (direction next : Fin d) :
    frontier (n:=n) base length (u+1) [] next 0=frontier (n:=n) base length u (List.finRange d) direction 0 := by
  simp only [frontier,spaceSum,scanSpace,List.map_nil,List.sum_nil,Nat.mul_zero,Nat.add_zero,Nat.zero_mul]
  ring

 theorem spaceSum_mono (dirs rest : List (Fin d)) (scanPrefix : dirs<+:rest) : spaceSum dirs≤spaceSum rest := by
  obtain ⟨tail,rfl⟩ := scanPrefix
  rw [spaceSum_append]
  omega
 theorem frontier_bound (base length u v : Nat) (dirs : List (Fin d)) (direction : Fin d)
    (hu : u<n) (hv : v<n) (remaining : spaceSum dirs+Binary.Candidate.space direction≤scanSpace d) :
    frontier (n:=n) base length u dirs direction v+Binary.Candidate.space direction*length≤
      base+n*n*scanSpace d*length := by
  have vBound := Nat.mul_le_mul_right (Binary.Candidate.space direction) (Nat.succ_le_of_lt hv)
  have dirBound := Nat.mul_le_mul_left n remaining
  have uBound := Nat.mul_le_mul_right (n*scanSpace d) (Nat.succ_le_of_lt hu)
  have total : u*n*scanSpace d+n*spaceSum dirs+v*Binary.Candidate.space direction+Binary.Candidate.space direction≤n*n*scanSpace d := by
    nlinarith only [vBound,dirBound,uBound]
  have scaled := Nat.mul_le_mul_right length total
  unfold frontier
  nlinarith only [scaled]

end LeanTrominoes.Domino.WordRAM.Driver.Order
