/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.PeriodicDominoSolver
import LeanTrominoes.Tiling.Domino.DominoWordRAMCramer
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDummyVertex

/-! # A fixed-size candidate graph for the domino decoder

Every representative, positive coordinate direction, and target representative
has one candidate. Valid candidates emit both orientations in every parity
phase; invalid candidates emit the isolated forced dummy edge. Repeated edges
are retained, so the constructor needs neither filtering nor compaction.
-/
namespace LeanTrominoes.Domino.WordRAM.PaddedGraph
open PeriodicLatticeGraph
variable {n d : ℕ}

abbrev Candidate (n d : ℕ) := Fin n × Fin d × Fin n × DoubleCover.Phase d

def coordinates (B : BasisData n d) (u : Fin n) (direction : Fin d) (v : Fin n) : Lattice d :=
  B.inverseData.coordinates (B.origin u+unit direction-B.origin v)

def arc (B : BasisData n d) (u : Fin n) (direction : Fin d) (v : Fin n) : Arc (Fin n) d :=
  ⟨u,v,coordinates B u direction v⟩

def Active (B : BasisData n d) (u : Fin n) (direction : Fin d) (v : Fin n) : Prop :=
  B.realize (v,coordinates B u direction v)=B.origin u+unit direction

theorem active_iff_divisible (B : BasisData n d) (nonzero : B.basis.det≠0)
    (u : Fin n) (direction : Fin d) (v : Fin n) :
    Active B u direction v ↔ ∀ j, B.basis.det ∣
      B.basis.adjugate.mulVec (B.origin u+unit direction-B.origin v) j := by
  rw [←lattice_mem_iff_adjugate_dvd B.basis nonzero]
  constructor
  · intro active
    refine ⟨coordinates B u direction v,?_⟩
    change B.origin v+B.basis.mulVec (coordinates B u direction v)=B.origin u+unit direction at active
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using active)
  · rintro ⟨z,realizes⟩
    have coords : coordinates B u direction v=z := by
      unfold coordinates
      rw [←realizes,B.coordinates_period nonzero]
    change B.origin v+B.basis.mulVec (coordinates B u direction v)=B.origin u+unit direction
    rw [coords,realizes]
    abel

theorem active_arc_mem (B : BasisData n d) (valid : B.Valid)
    (u : Fin n) (direction : Fin d) (v : Fin n) (active : Active B u direction v) :
    arc B u direction v∈B.cellArcs := by
  apply (neighborArcs_mem B.origin (B.decodeWith B.inverseData) (List.finRange n) _).mpr
  exact ⟨List.mem_finRange _,direction,(B.decode_correct valid _ _).mpr active⟩

theorem every_arc_candidate (B : BasisData n d) (valid : B.Valid) (e : Arc (Fin n) d)
    (member : e∈B.cellArcs) :
    ∃ direction, Active B e.source direction e.target ∧ arc B e.source direction e.target=e := by
  obtain ⟨_,direction,decoded⟩ := (neighborArcs_mem B.origin (B.decodeWith B.inverseData) (List.finRange n) e).mp member
  have realizes := (B.decode_correct valid _ _).mp decoded
  have difference : B.basis.mulVec e.offset=B.origin e.source+unit direction-B.origin e.target := by
    change B.origin e.target+B.basis.mulVec e.offset=B.origin e.source+unit direction at realizes
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using realizes)
  have coords : coordinates B e.source direction e.target=e.offset := by
    unfold coordinates
    rw [←difference,B.coordinates_period valid.1]
  refine ⟨direction,?_,?_⟩
  · simpa only [Active,coords] using realizes
  · cases e
    simp only [arc,coords]

def coverPair (e : Arc (Fin n) d) (phase : DoubleCover.Phase d) : Fin (n*2^d) × Fin (n*2^d) :=
  (vertexIndex n d (DoubleCover.expand e phase).source,vertexIndex n d (DoubleCover.expand e phase).target)

theorem solver_pairs (arcs : List (Arc (Fin n) d)) :
    PeriodicBipartite.edgePairs (solverEdges arcs)=
      (DoubleCover.phases d).flatMap (fun phase => arcs.flatMap fun e =>
        [coverPair e phase,(coverPair e phase).swap]) := by
  simp [PeriodicBipartite.edgePairs,solverEdges,PeriodicBipartite.reindex,symmetricEdges,
    DoubleCover.arcs,coverPair,List.map_flatMap,List.flatMap_map,List.flatMap_assoc,List.map_map,Function.comp_def]

theorem solver_pairs_mem (arcs : List (Arc (Fin n) d)) (pair : Fin (n*2^d) × Fin (n*2^d)) :
    pair∈PeriodicBipartite.edgePairs (solverEdges arcs) ↔
      ∃ e∈arcs, ∃ phase, pair=coverPair e phase ∨ pair=(coverPair e phase).swap := by
  rw [solver_pairs]
  constructor
  · intro member
    obtain ⟨phase,_,inner⟩ := List.mem_flatMap.mp member
    obtain ⟨e,he,member⟩ := List.mem_flatMap.mp inner
    exact ⟨e,he,phase,by simpa using member⟩
  · rintro ⟨e,he,phase,member⟩
    exact List.mem_flatMap.mpr ⟨phase,DoubleCover.mem_phases _,List.mem_flatMap.mpr
      ⟨e,he,by simpa using member⟩⟩

def candidates (n d : ℕ) : List (Candidate n d) :=
  (List.finRange n).flatMap fun u => (List.finRange d).flatMap fun direction =>
    (List.finRange n).flatMap fun v => (DoubleCover.phases d).map fun phase => (u,direction,v,phase)

theorem mem_candidates (c : Candidate n d) : c∈candidates n d := by
  rcases c with ⟨u,direction,v,phase⟩
  simp [candidates]

theorem candidates_length (n d : ℕ) : (candidates n d).length=n*n*d*2^d := by
  simp [candidates,List.length_flatMap]
  ring

end LeanTrominoes.Domino.WordRAM.PaddedGraph
