/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalScan
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalGeometry
import LeanTrominoes.Tiling.Domino.DominoWordRAMFinalBounds

/-! # Constructing the entire matching instance from the original binary input -/
namespace LeanTrominoes.Domino.WordRAM
open ComplexityAbstract.RAM Binary
variable {n d : ℕ}

noncomputable def endpointWords (B : BasisData n d) : List (ℕ×ℕ) :=
  (PaddedGraph.edges B).map fun edge => (edge.1.val,edge.2.val)

 theorem endpointWords_eq (B : BasisData n d) : endpointWords B=
    [(n*2^d,n*2^d)]++Driver.Order.sources B (List.finRange n) := by
  rw [Driver.Order.sources_complete]
  simp only [endpointWords,PaddedGraph.edges,List.map_cons,List.map_flatMap,EndpointWriter.candidateWords]
  rfl

 theorem endpointWords_length (B : BasisData n d) : (endpointWords B).length=Driver.edgeCount n d := by
  rw [endpointWords,List.length_map,PaddedGraph.edges_length]
  unfold Driver.edgeCount
  ring

noncomputable def graphProgram (d : ℕ) : Structured.Code 128 :=
  .seq (GlobalPrepare128.afterHeader d) (.seq (Driver.initializeTables d) (Driver.scanProgram d))

 theorem graphProgram_exec {w : ℕ} (B : BasisData n d) (positive : 0<n) (nonzero : B.basis.det≠0)
    (prepareWord : Fits w (GlobalPrepare128.resourceBound B))
    (operationWord : Fits w (SizeBounds.operationBound B : ℕ)) :
    ∃ result cost, NaturalData.Exec w (graphProgram d)
      (GlobalPrepare128.headerState (initialData 128 B)) result cost ∧
      cost≤GlobalPrepare128.costBound B+17+FinalBounds.scanCost n d (precision B) ∧
      Driver.GraphState B (GlobalPrepare128.endAddress B) (Driver.edgeCount n d) (endpointWords B) result := by
  obtain ⟨prepared,prepareCost,prepareRun,prepareBound,frame,count,front⟩ :=
    GlobalPrepare128.afterHeader_exec B positive nonzero prepareWord
  have heapWord : Fits w (SizeBounds.driverHeap B : ℕ) := Allocation.nat_fits_le operationWord (Driver.heap_le_operation B)
  have resources : Driver.GraphResources (SizeBounds.operationBound B) n d
      (prepared.1 Driver.frontier) (Driver.edgeCount n d) := by
    rw [front]
    exact Driver.graphResources B
  obtain ⟨allocated,allocationRun,allocationState,allocationFront⟩ := Driver.initialize_exec B
    ⟨0,positive⟩ ⟨0,positive⟩ prepared frame count
    (by rw [front]; exact Driver.initial_tables_bound B) resources heapWord operationWord
  have state : Driver.GraphState B (GlobalPrepare128.endAddress B) (Driver.edgeCount n d)
      [(n*2^d,n*2^d)] allocated := by simpa only [front] using allocationState
  have freshFront : allocated.1 (74 : Fin 128)=GlobalPrepare128.endAddress B+2*Driver.edgeCount n d := by
    simpa only [front] using allocationFront
  have heapKernelWord : Fits w (FreshProbe.scalarBound (Candidate.slotBound d) (SizeBounds.driverHeap B) : ℕ) :=
    Allocation.nat_fits_le operationWord (by unfold SizeBounds.operationBound; omega)
  obtain ⟨result,scanCost,scanRun,scanBound,finalState,_,_⟩ := Driver.scanProgram_exec B
    [(n*2^d,n*2^d)] allocated state (Driver.graphResources B)
    (by simp only [List.length_cons,List.length_nil]; unfold Driver.edgeCount; ring_nf; omega)
    (by rw [freshFront,Driver.driverHeap_eq]; unfold Driver.maxSpace SizeBounds.uniformSpace; ring_nf; omega)
    operationWord heapKernelWord (Driver.heap_le_operation B)
  refine ⟨result,prepareCost+(17+scanCost),prepareRun.seq (allocationRun.seq scanRun),?_,?_⟩
  · change scanCost≤FinalBounds.scanCost n d (precision B) at scanBound
    omega
  · simpa only [←endpointWords_eq B] using finalState

end LeanTrominoes.Domino.WordRAM
