/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGraphConstruction

/-! # Exact generated endpoint arrays at the matching-call boundary -/
namespace LeanTrominoes.Domino.WordRAM
open ComplexityAbstract.RAM Binary
variable {n d : ℕ}

 theorem edgeCount_edges (B : BasisData n d) : Driver.edgeCount n d=(PaddedGraph.edges B).length := by
  rw [PaddedGraph.edges_length]
  unfold Driver.edgeCount
  ring

 theorem generated_arrays (B : BasisData n d) (data : NaturalData 128)
    (state : Driver.GraphState B (GlobalPrepare128.endAddress B) (Driver.edgeCount n d) (endpointWords B) data) :
    (∀ i, (hi : i<(PaddedGraph.edges B).length) →
      data.word.2 (GlobalPrepare128.endAddress B+i)=((PaddedGraph.edges B)[i]).1.val) ∧
    (∀ i, (hi : i<(PaddedGraph.edges B).length) →
      data.word.2 (GlobalPrepare128.endAddress B+(PaddedGraph.edges B).length+i)=((PaddedGraph.edges B)[i]).2.val) := by
  constructor
  · intro i hi
    have within : i<(endpointWords B).length := by simpa only [endpointWords,List.length_map] using hi
    have values := (state.endpoints i within).1
    simp only [endpointWords,List.getElem_map] at values
    exact congrArg Int.ofNat values
  · intro i hi
    have within : i<(endpointWords B).length := by simpa only [endpointWords,List.length_map] using hi
    have values := (state.endpoints i within).2
    simp only [endpointWords,List.getElem_map] at values
    rw [edgeCount_edges B] at values
    exact congrArg Int.ofNat values

 theorem generated_values_fit {w : ℕ} (B : BasisData n d) (data : NaturalData 128)
    (state : Driver.GraphState B (GlobalPrepare128.endAddress B) (Driver.edgeCount n d) (endpointWords B) data)
    (word : Fits w (SizeBounds.operationBound B : ℕ)) :
    (∀ i, i<(PaddedGraph.edges B).length → Fits w (data.word.2 (GlobalPrepare128.endAddress B+i))) ∧
    (∀ i, i<(PaddedGraph.edges B).length → Fits w (data.word.2 (GlobalPrepare128.endAddress B+(PaddedGraph.edges B).length+i))) := by
  have arrays := generated_arrays B data state
  have resources := Driver.graphResources B
  constructor
  · intro i hi
    rw [arrays.1 i hi]
    apply Allocation.nat_fits_le word
    have endpoint := ((PaddedGraph.edges B)[i]).1.isLt
    have vertices := resources.vertices
    omega
  · intro i hi
    rw [arrays.2 i hi]
    apply Allocation.nat_fits_le word
    have endpoint := ((PaddedGraph.edges B)[i]).2.isLt
    have vertices := resources.vertices
    omega

end LeanTrominoes.Domino.WordRAM
