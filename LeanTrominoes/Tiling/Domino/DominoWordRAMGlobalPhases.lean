/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalLoops
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointPrefix

/-! # Static phase iteration in the actual graph constructor -/
namespace LeanTrominoes.Domino.WordRAM.Driver
open ComplexityAbstract.RAM
open EndpointWriter
local notation "Data" => NaturalData 128

def phaseProgram (d : ℕ) : Structured.Code 128 :=
  sequence (82 : Fin 128) EndpointWriter.program (PeriodicLatticeGraph.DoubleCover.phases d)

structure TableBounds (bound n d total : ℕ) (data : Data) : Prop where
  small : 2≤bound
  dimension : d≤bound
  parities : data.1 H.parities+d≤data.1 H.left
  separation : data.1 H.left≤data.1 H.right
  capacity : 2^d≤bound
  vertices : n*2^d≤bound
  left : data.1 H.left+total≤bound
  right : data.1 H.right+total≤bound
  count : total≤bound

noncomputable def phaseWords {n d : ℕ} (B : BasisData n d) (u : Fin n) (direction : Fin d) (v : Fin n)
    (phases : List (PeriodicLatticeGraph.DoubleCover.Phase d)) :=
  phases.flatMap fun phase => candidateWords B (u,direction,v,phase)

theorem phaseWords_length {n d : ℕ} (B : BasisData n d) (u : Fin n) (direction : Fin d) (v : Fin n)
    (phases : List (PeriodicLatticeGraph.DoubleCover.Phase d)) :
    (phaseWords B u direction v phases).length=2*phases.length := by
  have length (phase : PeriodicLatticeGraph.DoubleCover.Phase d) :
      (candidateWords B (u,direction,v,phase)).length=2 := by
    classical
    by_cases h : PaddedGraph.Active B u direction v
    all_goals simp [candidateWords,PaddedGraph.candidateEdges,h]
  simp only [phaseWords,List.length_flatMap,length,List.map_const',List.sum_replicate]
  simp [nsmul_eq_mul,Nat.mul_comm]

theorem phases_exec {w n d bound total : ℕ} (B : BasisData n d)
    (u : Fin n) (direction : Fin d) (v : Fin n) (bits : Fin d → ℕ) (data : Data)
    (width : Fits w bound) (bounds : TableBounds bound n d total data)
    (unit : data.1 (82 : Fin 128)=1)
    (uInput : data.1 H.u=u.val) (vInput : data.1 H.v=v.val) (nInput : data.1 H.n=n)
    (bitBound : ∀ i, bits i≤1) (known : ∀ i, data.2 (data.1 H.parities+i.val)=bits i)
    (valid : data.1 H.active≠0 ↔ PaddedGraph.Active B u direction v)
    (parities : PaddedGraph.Active B u direction v → ∀ i,
      bits i=(PaddedGraph.coordinates B u direction v i%2).toNat)
    (room : data.1 H.index+2*(PeriodicLatticeGraph.DoubleCover.phases d).length≤total) :
    ∃ result cost, NaturalData.Exec w (phaseProgram d) data result cost ∧
      cost≤(9*d+25)*(PeriodicLatticeGraph.DoubleCover.phases d).length+1 ∧
      Output (phaseWords B u direction v (PeriodicLatticeGraph.DoubleCover.phases d)) data result := by
  let all := PeriodicLatticeGraph.DoubleCover.phases d
  let Invariant := fun done current => Output (phaseWords B u direction v done) data current
  have initial : Invariant [] data := by
    refine ⟨rfl,?_,?_⟩
    · simp [phaseWords]
    · intro i low different; rfl
  have unitWord : Fits w (1 : ℕ) := Allocation.nat_fits_le width (by have := bounds.small; omega)
  have sequenceRun := sequence_exec (82 : Fin 128) EndpointWriter.program all (9*d+25) Invariant unitWord
    (by intro done current progress; exact (progress.fixed _ (by decide) (by decide)).trans unit)
  have step : ∀ done phase rest, done++phase::rest=all → ∀ current, Invariant done current →
      ∃ result cost, NaturalData.Exec w (EndpointWriter.program phase) current result cost ∧
        cost≤9*d+25 ∧ Invariant (done++[phase]) result := by
    intro done phase rest complete current progress
    have fixed (i : Fin 128) (low : i.val<96) (different : i≠H.index) : current.1 i=data.1 i :=
      progress.fixed i low different
    have doneLength := congrArg List.length complete
    simp only [List.length_append,List.length_cons] at doneLength
    change done.length+(rest.length+1)=(PeriodicLatticeGraph.DoubleCover.phases d).length at doneLength
    have tableLeft := bounds.left
    have tableRight := bounds.right
    have tableCount := bounds.count
    have cursor : current.1 H.index=data.1 H.index+2*done.length := by
      rw [progress.index,phaseWords_length]
    have currentBounds : Bounds bound d n current := by
      refine ⟨bounds.small,bounds.dimension,?_,bounds.capacity,bounds.vertices,?_,?_,?_⟩
      · rw [fixed H.parities (by decide) (by decide)]
        exact bounds.parities.trans (Nat.le_add_right _ _ |>.trans bounds.left)
      · rw [fixed H.left (by decide) (by decide),cursor]
        omega
      · rw [fixed H.right (by decide) (by decide),cursor]
        omega
      · rw [cursor]; omega
    have knownCurrent (i : Fin d) : current.2 (current.1 H.parities+i.val)=bits i := by
      rw [fixed H.parities (by decide) (by decide),progress.frame]
      · exact known i
      · left; have := i.isLt; have := bounds.parities; omega
      · left; have := i.isLt; have := bounds.parities; have := bounds.separation; omega
    obtain ⟨result,run,output⟩ := candidate_exec B u direction v phase bits current width currentBounds
      ((fixed H.u (by decide) (by decide)).trans uInput)
      ((fixed H.v (by decide) (by decide)).trans vInput)
      ((fixed H.n (by decide) (by decide)).trans nInput) bitBound knownCurrent
      (by rw [fixed H.active (by decide) (by decide)]; exact valid) parities
    refine ⟨result,9*d+25,run,le_rfl,?_⟩
    have combined := progress.trans output
    simpa only [Invariant,phaseWords,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] using combined
  simpa only [phaseProgram,all] using sequenceRun step all [] (by simp) data initial

end LeanTrominoes.Domino.WordRAM.Driver
