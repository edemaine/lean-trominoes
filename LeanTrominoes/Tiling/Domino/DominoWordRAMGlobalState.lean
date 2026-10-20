/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalPhases
import LeanTrominoes.Tiling.Domino.DominoWordRAMCandidate
import LeanTrominoes.Tiling.Domino.DominoWordRAMOriginPointers128

/-! # Persistent graph-constructor state across candidate computations -/
namespace LeanTrominoes.Domino.WordRAM.Driver
open ComplexityAbstract.RAM
local notation "Data" => NaturalData 128
open Binary

structure GraphState {n d : ℕ} (B : BasisData n d) (base total : ℕ)
    (words : List (ℕ×ℕ)) (data : Data) : Prop where
  frame : ∃ u v : Fin n, Candidate.Frame B u v data
  vertices : data.1 (66 : Fin 128)=n
  unit : data.1 (82 : Fin 128)=1
  count : data.1 (83 : Fin 128)=total
  left : data.1 (70 : Fin 128)=base
  right : data.1 (71 : Fin 128)=base+total
  parities : data.1 (67 : Fin 128)+d≤base
  tables : base+2*total≤data.1 (74 : Fin 128)
  cursor : data.1 (69 : Fin 128)=words.length
  endpoints : EndpointWriter.Prefix data base (base+total) words

structure GraphResources (bound n d base total : ℕ) : Prop where
  small : 2≤bound
  dimension : d≤bound
  capacity : 2^d≤bound
  vertices : n*2^d≤bound
  tables : base+2*total≤bound
  count : total≤bound

 theorem GraphState.tableBounds {n d base total bound : ℕ} {B : BasisData n d}
    {words : List (ℕ×ℕ)} {data : Data} (h : GraphState B base total words data)
    (resources : GraphResources bound n d base total) : TableBounds bound n d total data := by
  refine ⟨resources.small,resources.dimension,?_,?_,resources.capacity,resources.vertices,?_,?_,resources.count⟩
  · simpa only [h.left] using h.parities
  · rw [h.left,h.right]; omega
  · rw [h.left]; have := resources.tables; omega
  · rw [h.right]; have := resources.tables; omega

 theorem GraphState.transport {n d base total : ℕ} {B : BasisData n d} {words : List (ℕ×ℕ)}
    {before after : Data} (h : GraphState B base total words before)
    (fixed : ∀ i : Fin 128, 64≤ i.val → i.val< 96 → after.1 i=before.1 i)
    (memory : after.2=before.2) : GraphState B base total words after := by
  have frame := h.frame
  obtain ⟨u,v,frame⟩ := frame
  have nextFrame : Candidate.Frame B u v after := frame.transport
    (by intro i member; apply fixed <;> simp only [Candidate.persistentHeaders,List.mem_cons,List.not_mem_nil,or_false] at member <;> rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
    (by rw [fixed _ (by decide) (by decide)])
    (by intro address below; rw [memory])
  refine ⟨⟨u,v,nextFrame⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [fixed _ (by decide) (by decide)]; exact h.vertices
  · rw [fixed _ (by decide) (by decide)]; exact h.unit
  · rw [fixed _ (by decide) (by decide)]; exact h.count
  · rw [fixed _ (by decide) (by decide)]; exact h.left
  · rw [fixed _ (by decide) (by decide)]; exact h.right
  · rw [fixed _ (by decide) (by decide)]; exact h.parities
  · rw [fixed _ (by decide) (by decide)]; exact h.tables
  · rw [fixed _ (by decide) (by decide)]; exact h.cursor
  · intro i hi; rw [memory]; exact h.endpoints i hi

end LeanTrominoes.Domino.WordRAM.Driver
