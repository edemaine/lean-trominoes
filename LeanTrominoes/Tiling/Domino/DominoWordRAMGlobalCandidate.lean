/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalState

/-! # Original-origin loads, arithmetic probes, and all padded phase records -/
namespace LeanTrominoes.Domino.WordRAM.Driver
open ComplexityAbstract.RAM
open Binary
local notation "Data" => NaturalData 128

noncomputable def candidateBody (d : ℕ) (direction : Fin d) : Structured.Code 128 :=
  .seq (OriginPointers128.program d) (.seq (Candidate.program direction) (phaseProgram d))

noncomputable def candidateCost (d L : ℕ) :=
  11+(d*Candidate.coordinateCost (Candidate.slotBound d) L+2)+(9*d+25)*2^d+1

theorem origin_constants {n d : ℕ} (B : BasisData n d) (positive : 0<n) :
    d*d+d+4≤Candidate.inputEnd B := by
  have grow : d≤n*d := Nat.le_mul_of_pos_left _ positive
  have length := WordRAM.precision_positive B
  have scaled : d*d+n*d≤(d*d+n*d)*WordRAM.precision B := Nat.le_mul_of_pos_right _ length
  unfold Candidate.inputEnd
  rw [words_length]
  omega

theorem origin_address {n d : ℕ} (B : BasisData n d) (u v : Fin n) (direction : Fin d) :
    4+(d*d+u.val*d)*WordRAM.precision B≤Candidate.inputEnd B ∧
    4+(d*d+v.val*d)*WordRAM.precision B≤Candidate.inputEnd B := by
  have first := original_source_before B u v 0 1 0
    (by have := direction.isLt; norm_num [SourceLoad.count]; omega) 0 (WordRAM.precision_positive B)
  have second := original_source_before B u v 0 2 0
    (by have := direction.isLt; norm_num [SourceLoad.count]; omega) 0 (WordRAM.precision_positive B)
  constructor
  · exact (show 4+(d*d+u.val*d)*WordRAM.precision B<Candidate.inputEnd B by simpa [Candidate.inputEnd,sourceLayout,sourceRank] using first).le
  · exact (show 4+(d*d+v.val*d)*WordRAM.precision B<Candidate.inputEnd B by simpa [Candidate.inputEnd,sourceLayout,sourceRank] using second).le

 theorem candidateBody_exec {n d base total bound H w : ℕ} (B : BasisData n d)
    (u : Fin n) (direction : Fin d) (v : Fin n) (old : List (ℕ×ℕ)) (data : Data)
    (state : GraphState B base total old data) (resources : GraphResources bound n d base total)
    (uInput : data.1 (64 : Fin 128)=u.val) (vInput : data.1 (65 : Fin 128)=v.val)
    (room : old.length+2*(PeriodicLatticeGraph.DoubleCover.phases d).length≤total)
    (budget : data.1 (74 : Fin 128)+Candidate.space direction*WordRAM.precision B≤H)
    (word : Fits w bound) (heapWord : Fits w (FreshProbe.scalarBound (Candidate.slotBound d) H))
    (heapBound : H≤bound) :
    ∃ result cost, NaturalData.Exec w (candidateBody d direction) data result cost ∧
      cost≤candidateCost d (WordRAM.precision B) ∧
      GraphState B base total (old++phaseWords B u direction v (PeriodicLatticeGraph.DoubleCover.phases d)) result ∧
      result.1 (74 : Fin 128)=data.1 (74 : Fin 128)+Candidate.space direction*WordRAM.precision B ∧
      (∀ i : Fin 128, 64≤ i.val → i.val<96 →
        i≠(68 : Fin 128) → i≠(69 : Fin 128) → i≠(74 : Fin 128) →
        i≠(78 : Fin 128) → i≠(79 : Fin 128) → i≠(81 : Fin 128) → result.1 i=data.1 i) := by
  obtain ⟨oldU,oldV,frame⟩ := state.frame
  have inputBound : Candidate.inputEnd B≤bound := by
    have front := frame.frontier
    have current : data.1 (74 : Fin 128)≤H := by omega
    exact (show Candidate.inputEnd B≤data.1 (74 : Fin 128) by change Candidate.inputEnd B+(3+d)*precision B≤data.1 (74 : Fin 128) at front; omega).trans (current.trans heapBound)
  obtain ⟨pointed,pointerRun,pointers⟩ := OriginPointers128.program_exec data word
    (by rw [show (OriginPointers128.H.precision : Fin 128)=(72 : Fin 128) from rfl,frame.precision]; exact WordRAM.precision_positive B)
    ((origin_constants B (by have := u.isLt; omega)).trans inputBound)
    (by rw [show (OriginPointers128.H.u : Fin 128)=(64 : Fin 128) from rfl,uInput,show (OriginPointers128.H.precision : Fin 128)=(72 : Fin 128) from rfl,frame.precision]; exact (origin_address B u v direction).1.trans inputBound)
    (by rw [show (OriginPointers128.H.v : Fin 128)=(65 : Fin 128) from rfl,vInput,show (OriginPointers128.H.precision : Fin 128)=(72 : Fin 128) from rfl,frame.precision]; exact (origin_address B u v direction).2.trans inputBound)
  have pointerFixed (i : Fin 128) (low : i.val<96) (notFirst : i≠(78 : Fin 128)) (notSecond : i≠(79 : Fin 128)) : pointed.1 i=data.1 i :=
    pointers.fixed i (Or.inl low) notFirst notSecond
  have pointedFrame : Candidate.Frame B u v pointed := frame.change_representatives
    (by intro i member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl|rfl|rfl|rfl|rfl <;> exact pointerFixed _ (by decide) (by decide) (by decide))
    (by rw [pointers.first,uInput,frame.precision])
    (by rw [pointers.second,vInput,frame.precision])
    (by rw [pointerFixed _ (by decide) (by decide) (by decide)])
    (by intro address below; rw [pointers.memory])
  obtain ⟨probed,probeCost,probeRun,probeBound,probeFrame,probeFront,active,bitBound,parities,probeFixed,probeMemory⟩ :=
    Candidate.program_exec B u v direction pointed pointedFrame H
      (by rw [pointerFixed _ (by decide) (by decide) (by decide)]; exact budget) heapWord
  have probePreserved (i : Fin 128) (high : 64≤ i.val) (low : i.val<96)
      (notFront : i≠(74 : Fin 128)) (notBase : i≠(81 : Fin 128)) (notActive : i≠(68 : Fin 128)) :
      probed.1 i=pointed.1 i := by
    apply probeFixed i high notFront notBase notActive
    all_goals intro same; have equal := congrArg Fin.val same; norm_num [Collect.zero,Collect.index,Collect.address] at equal; omega
  have probeOriginal (i : Fin 128) (high : 64≤ i.val) (low : i.val<96)
      (notFront : i≠(74 : Fin 128)) (notBase : i≠(81 : Fin 128)) (notActive : i≠(68 : Fin 128))
      (notFirst : i≠(78 : Fin 128)) (notSecond : i≠(79 : Fin 128)) : probed.1 i=data.1 i :=
    (probePreserved i high low notFront notBase notActive).trans (pointerFixed i low notFirst notSecond)
  have probedFront : probed.1 (74 : Fin 128)=data.1 (74 : Fin 128)+Candidate.space direction*precision B := by
    rw [probeFront,pointerFixed _ (by decide) (by decide) (by decide)]
  have pointedPrefix : EndpointWriter.Prefix pointed base (base+total) old := by
    intro i hi; rw [pointers.memory]; exact state.endpoints i hi
  have probedPrefix : EndpointWriter.Prefix probed base (base+total) old := by
    apply pointedPrefix.transport_below (frontier:=pointed.1 (74 : Fin 128))
      (parities:=pointed.1 (67 : Fin 128)) (dimension:=d)
    · rw [pointerFixed _ (by decide) (by decide) (by decide)]; have := state.tables; omega
    · rw [pointerFixed _ (by decide) (by decide) (by decide)]; have := state.tables; omega
    · right; rw [pointerFixed _ (by decide) (by decide) (by decide)]; exact state.parities
    · right; rw [pointerFixed _ (by decide) (by decide) (by decide)]; have := state.parities; omega
    · exact probeMemory
  have probedState : GraphState B base total old probed := by
    refine ⟨⟨u,v,probeFrame⟩,?_,?_,?_,?_,?_,?_,?_,?_,probedPrefix⟩
    · rw [probeOriginal _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact state.vertices
    · rw [probeOriginal _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact state.unit
    · rw [probeOriginal _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact state.count
    · rw [probeOriginal _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact state.left
    · rw [probeOriginal _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact state.right
    · rw [probeOriginal _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact state.parities
    · rw [probedFront]; have := state.tables; omega
    · rw [probeOriginal _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact state.cursor
  let bits : Fin d → ℕ := fun i => probed.2 (probed.1 (67 : Fin 128)+i.val)
  obtain ⟨result,phaseCost,phaseRun,phaseBound,output⟩ := phases_exec B u direction v bits probed word
    (probedState.tableBounds resources) probedState.unit
    (by rw [probeOriginal _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact uInput)
    (by rw [probeOriginal _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact vInput)
    probedState.vertices bitBound (by intro i; rfl) active parities
    (by rw [probedState.cursor]; exact room)
  have outputFixed (i : Fin 128) (low : i.val<96) (different : i≠(69 : Fin 128)) : result.1 i=probed.1 i :=
    output.fixed i low different
  have finalFrame : Candidate.Frame B u v result := probeFrame.transport
    (by intro i member; apply outputFixed <;> simp only [Candidate.persistentHeaders,List.mem_cons,List.not_mem_nil,or_false] at member <;> rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
    (by rw [outputFixed _ (by decide) (by decide)])
    (by
      intro address below
      apply output.frame
      · left; rw [probedState.left]; have parity := probeFrame.parities; change probed.1 (67 : Fin 128)=Candidate.inputEnd B+3*precision B at parity; have := probedState.parities; omega
      · left; rw [probedState.right]; have parity := probeFrame.parities; change probed.1 (67 : Fin 128)=Candidate.inputEnd B+3*precision B at parity; have := probedState.parities; omega)
  refine ⟨result,11+(probeCost+phaseCost),pointerRun.seq (probeRun.seq phaseRun),?_,?_,?_,?_⟩
  · unfold candidateCost
    have phasesLength := PeriodicLatticeGraph.DoubleCover.phases_length (d:=d)
    rw [phasesLength] at phaseBound
    omega
  · refine ⟨⟨u,v,finalFrame⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [outputFixed _ (by decide) (by decide)]; exact probedState.vertices
    · rw [outputFixed _ (by decide) (by decide)]; exact probedState.unit
    · rw [outputFixed _ (by decide) (by decide)]; exact probedState.count
    · rw [outputFixed _ (by decide) (by decide)]; exact probedState.left
    · rw [outputFixed _ (by decide) (by decide)]; exact probedState.right
    · rw [outputFixed _ (by decide) (by decide)]; exact probedState.parities
    · rw [outputFixed _ (by decide) (by decide)]; exact probedState.tables
    · rw [output.index,probedState.cursor,List.length_append]
    · apply output.prefix_append probedState.endpoints probedState.left probedState.right probedState.cursor rfl
      rw [phaseWords_length]; exact room
  · rw [outputFixed _ (by decide) (by decide),probedFront]
  · intro i high low notActive notCursor notFront notFirst notSecond notBase
    rw [outputFixed i low notCursor]
    exact probeOriginal i high low notFront notBase notActive notFirst notSecond

end LeanTrominoes.Domino.WordRAM.Driver
