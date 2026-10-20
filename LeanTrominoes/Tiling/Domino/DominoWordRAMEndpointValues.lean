/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMPaddedGraphMatching

/-! # Arithmetic endpoint indices for the padded parity-cover graph -/
namespace LeanTrominoes.Domino.WordRAM.EndpointWriter
open PeriodicLatticeGraph
variable {n d : Nat}
attribute [local instance] Classical.propDecidable

def shiftedPhase (phase : DoubleCover.Phase d) (bits : Fin d → Nat) : DoubleCover.Phase d :=
  fun i => ⟨((phase i).val+bits i)%2,Nat.mod_lt _ (by decide)⟩

def phaseValue (phase : DoubleCover.Phase d) (bits : Fin d → Nat) : Nat :=
  ∑ i : Fin d, (((phase i).val+bits i)%2)*2^i.val

theorem phaseValue_eq (phase : DoubleCover.Phase d) (bits : Fin d → Nat) :
    phaseValue phase bits=(finFunctionFinEquiv (shiftedPhase phase bits)).val := by
  rfl

theorem phaseValue_lt (phase : DoubleCover.Phase d) (bits : Fin d → Nat) : phaseValue phase bits<2^d := by
  rw [phaseValue_eq]
  exact (finFunctionFinEquiv (shiftedPhase phase bits)).isLt

theorem shiftedPhase_eq (phase : DoubleCover.Phase d) (offset : Lattice d) (bits : Fin d → Nat)
    (parities : ∀ i, bits i=(offset i%2).toNat) :
    shiftedPhase phase bits=DoubleCover.residue (DoubleCover.combine phase 0+offset) := by
  funext i
  apply Fin.ext
  have phaseBound := (phase i).isLt
  have nonnegative := Int.emod_nonneg (offset i) (by decide : (2 : Int)≠0)
  have upper := Int.emod_lt_of_pos (offset i) (by decide : (0 : Int)<2)
  have bit := parities i
  dsimp [shiftedPhase,DoubleCover.residue,DoubleCover.combine]
  omega

theorem vertexIndex_value (u : Fin n) (phase : DoubleCover.Phase d) :
    (vertexIndex n d (u,phase)).val=(finFunctionFinEquiv phase).val+2^d*u.val := by
  rfl

theorem coverPair_values (edge : Arc (Fin n) d) (phase : DoubleCover.Phase d) (bits : Fin d → Nat)
    (parities : ∀ i, bits i=(edge.offset i%2).toNat) :
    (PaddedGraph.coverPair edge phase).1.val=(finFunctionFinEquiv phase).val+2^d*edge.source.val ∧
    (PaddedGraph.coverPair edge phase).2.val=phaseValue phase bits+2^d*edge.target.val := by
  constructor
  · rfl
  · change (vertexIndex n d (edge.target,DoubleCover.residue (DoubleCover.combine phase 0+edge.offset))).val=_
    rw [←shiftedPhase_eq phase edge.offset bits parities,vertexIndex_value,phaseValue_eq]

noncomputable def candidateWords (B : BasisData n d) (c : PaddedGraph.Candidate n d) : List (Nat × Nat) :=
  (PaddedGraph.candidateEdges B c).map (fun edge => (edge.1.val,edge.2.val))

theorem candidateWords_length (B : BasisData n d) (c : PaddedGraph.Candidate n d) : (candidateWords B c).length=2 := by
  simp only [candidateWords,List.length_map,PaddedGraph.candidateEdges_length]

theorem candidateWords_eq (B : BasisData n d) (u : Fin n) (direction : Fin d) (v : Fin n)
    (phase : DoubleCover.Phase d) (bits : Fin d → Nat)
    (parities : PaddedGraph.Active B u direction v → ∀ i,
      bits i=(PaddedGraph.coordinates B u direction v i%2).toNat) :
    candidateWords B (u,direction,v,phase)=
      if PaddedGraph.Active B u direction v then
        [((finFunctionFinEquiv phase).val+2^d*u.val,phaseValue phase bits+2^d*v.val),
          (phaseValue phase bits+2^d*v.val,(finFunctionFinEquiv phase).val+2^d*u.val)]
      else [(n*2^d,n*2^d),(n*2^d,n*2^d)] := by
  classical
  by_cases active : PaddedGraph.Active B u direction v
  · have values := coverPair_values (PaddedGraph.arc B u direction v) phase bits (parities active)
    simp [candidateWords,PaddedGraph.candidateEdges,active,PaddedGraph.liftPair,values.1,values.2]
    simp [PaddedGraph.arc]
  · simp [candidateWords,PaddedGraph.candidateEdges,active,PaddedGraph.dummy]

end LeanTrominoes.Domino.WordRAM.EndpointWriter
