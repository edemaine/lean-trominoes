/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalAllocation
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalState
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointDummy

/-! # Allocate and initialize the original graph constructor's endpoint arrays -/
namespace LeanTrominoes.Domino.WordRAM.Driver
open ComplexityAbstract.RAM
open Binary

noncomputable def initializeTables (d : ℕ) : Structured.Code 128 :=
  .seq (allocate d) (EndpointWriter.dummyProgram d)

theorem initialize_exec {n d H bound w : ℕ} (B : BasisData n d) (u v : Fin n) (data : Data)
    (frame : Candidate.Frame B u v data) (count : data.1 (66 : Fin 128)=n)
    (budget : data.1 frontier+2*edgeCount n d≤H)
    (resources : GraphResources bound n d (data.1 frontier) (edgeCount n d))
    (heapWord : Fits w H) (word : Fits w bound) :
    ∃ result, NaturalData.Exec w (initializeTables d) data result 17 ∧
      GraphState B (data.1 frontier) (edgeCount n d) [(n*2^d,n*2^d)] result ∧
      result.1 frontier=data.1 frontier+2*edgeCount n d := by
  obtain ⟨allocated,allocationRun,allocation⟩ := allocate_exec data (by have := u.isLt; omega) count budget heapWord
  have fixed (i : Fin 128) (nOne : i≠one) (nCount : i≠edgeCountReg) (nLeft : i≠left)
      (nRight : i≠right) (nFront : i≠frontier) (nCursor : i≠cursor) : allocated.1 i=data.1 i :=
    allocation.fixed i nOne nCount nLeft nRight nFront nCursor
  have allocatedFrame : Candidate.Frame B u v allocated := frame.transport
    (by intro i member; simp only [Candidate.persistentHeaders,List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact fixed _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by change data.1 frontier≤allocated.1 frontier; rw [allocation.frontier]; omega)
    (by intro address below; rw [allocation.memory])
  have allocatedState : GraphState B (data.1 frontier) (edgeCount n d) [] allocated := by
    refine ⟨⟨u,v,allocatedFrame⟩,?_,allocation.unit,allocation.count,allocation.left,allocation.right,?_,?_,?_,?_⟩
    · rw [fixed _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact count
    · rw [fixed _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      have parity := frame.parities
      change data.1 (67 : Fin 128)=Candidate.inputEnd B+3*precision B at parity
      have front := frame.frontier
      change Candidate.inputEnd B+(3+d)*precision B≤data.1 frontier at front
      have length := WordRAM.precision_positive B
      have dimension := Nat.le_mul_of_pos_right d length
      nlinarith only [parity,front,dimension]
    · rw [allocation.frontier]
    · simpa using allocation.index
    · exact EndpointWriter.Prefix.empty _ _ _
  have dummyBounds : EndpointWriter.Bounds bound d n allocated := by
    refine ⟨resources.small,resources.dimension,?_,resources.capacity,resources.vertices,?_,?_,?_⟩
    · change allocated.1 (67 : Fin 128)+d≤bound
      have := allocatedState.parities
      have := resources.tables
      omega
    · change allocated.1 left+allocated.1 cursor+1≤bound
      rw [allocation.left,allocation.index]
      have := resources.tables
      have positive : 1≤edgeCount n d := by unfold edgeCount; omega
      omega
    · change allocated.1 right+allocated.1 cursor+1≤bound
      rw [allocation.right,allocation.index]
      have := resources.tables
      have positive : 1≤edgeCount n d := by unfold edgeCount; omega
      omega
    · change allocated.1 cursor+2≤bound
      rw [allocation.index]; exact resources.small
  obtain ⟨result,dummyRun,output⟩ := EndpointWriter.dummy_exec allocated dummyBounds allocatedState.vertices
  have outputFixed (i : Fin 128) (low : i.val<96) (different : i≠cursor) : result.1 i=allocated.1 i :=
    output.fixed i low different
  have finalFrame : Candidate.Frame B u v result := allocatedFrame.transport
    (by intro i member; apply outputFixed <;> simp only [Candidate.persistentHeaders,List.mem_cons,List.not_mem_nil,or_false] at member <;> rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
    (by rw [outputFixed _ (by decide) (by decide)])
    (by intro address below
        apply output.frame
        · left; change address<allocated.1 left+allocated.1 cursor
          rw [allocation.left,allocation.index]
          have front := frame.frontier
          change Candidate.inputEnd B+(3+d)*precision B≤data.1 frontier at front
          nlinarith only [below,front]
        · left; change address<allocated.1 right+allocated.1 cursor
          rw [allocation.right,allocation.index]
          have front := frame.frontier
          change Candidate.inputEnd B+(3+d)*precision B≤data.1 frontier at front
          nlinarith only [below,front])
  refine ⟨result,allocationRun.seq (dummyRun.compiles word),?_,?_⟩
  · refine ⟨⟨u,v,finalFrame⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [outputFixed _ (by decide) (by decide)]; exact allocatedState.vertices
    · rw [outputFixed _ (by decide) (by decide)]; exact allocatedState.unit
    · rw [outputFixed _ (by decide) (by decide)]; exact allocatedState.count
    · rw [outputFixed _ (by decide) (by decide)]; exact allocatedState.left
    · rw [outputFixed _ (by decide) (by decide)]; exact allocatedState.right
    · rw [outputFixed _ (by decide) (by decide)]; exact allocatedState.parities
    · rw [outputFixed _ (by decide) (by decide)]; exact allocatedState.tables
    · simpa only [List.length_cons,List.length_nil,Nat.zero_add] using output.index.trans (by rw [allocatedState.cursor]; rfl)
    · have initial := EndpointWriter.Prefix.empty allocated (data.1 frontier) (data.1 frontier+edgeCount n d)
      have append := output.prefix_append initial allocatedState.left allocatedState.right allocatedState.cursor rfl
        (show [].length+[(n*2^d,n*2^d)].length≤edgeCount n d by simp only [List.length_cons,List.length_nil]; unfold edgeCount; omega)
      simpa only [List.nil_append] using append
  · rw [outputFixed _ (by decide) (by decide),allocation.frontier]

end LeanTrominoes.Domino.WordRAM.Driver
