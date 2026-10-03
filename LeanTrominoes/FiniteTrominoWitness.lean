/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTrominoCompletion
import LeanTrominoes.Assignment
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card

/-! # Finite witnesses covering a prescribed cell set

Witnesses consist of whole geometric tiles, including any cells protruding
outside the set being covered. This distinction matters for finite-preplacement
completion: the bounding box need not itself be tileable.
-/
namespace LeanTrominoes.Tromino.FiniteWitness

/-- All geometric trominoes meeting a finite set. -/
def candidates (t : Tromino) (B : Finset Cell) : Finset (Finset Cell) :=
  B.biUnion fun c => (TrominoAssignment.coveringPlacements t c).image
    (Placement.cells (fun _ => t.cells))

theorem mem_candidates (t : Tromino) (B f : Finset Cell) :
    f∈candidates t B ↔ t.IsFootprint f ∧ ∃ c∈B, c∈f := by
  constructor
  · intro h
    obtain ⟨c,hc,hf⟩ := Finset.mem_biUnion.mp h
    obtain ⟨p,hp,equal⟩ := Finset.mem_image.mp hf
    refine ⟨⟨p,equal⟩,c,hc,?_⟩
    rw [← equal]
    exact (TrominoAssignment.mem_coveringPlacements_iff t c p).mp hp
  · rintro ⟨⟨p,rfl⟩,c,hc,hp⟩
    exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_image.mpr
      ⟨p,(TrominoAssignment.mem_coveringPlacements_iff t c p).mpr hp,rfl⟩⟩

/-- A finite, decidable verifier. Only tiles meeting `B` may be selected. -/
def Valid (t : Tromino) (B : Finset Cell) (prefill tiles : Finset (Finset Cell)) : Prop :=
  tiles⊆candidates t B ∧ prefill⊆tiles ∧
    (∀ f∈tiles, ∀ g∈tiles, ∀ c∈f, c∈g → f=g) ∧
    ∀ c∈B, ∃ f∈tiles, c∈f

instance (t : Tromino) (B : Finset Cell) (prefill tiles : Finset (Finset Cell)) :
    Decidable (Valid t B prefill tiles) := by unfold Valid; infer_instance

theorem Valid.partial {t : Tromino} {B : Finset Cell} {prefill tiles : Finset (Finset Cell)}
    (h : Valid t B prefill tiles) : t.IsPartialTiling Set.univ (tiles : Set (Finset Cell)) :=
  ⟨fun f hf => ⟨((mem_candidates t B f).mp (h.1 hf)).1,by simp⟩,h.2.2.1⟩

/-- A full completion restricts to a finite witness; no periodicity is used. -/
theorem of_completion (t : Tromino) (B : Finset Cell) (prefill : Finset (Finset Cell))
    (meets : ∀ f∈prefill, ∃ c∈B, c∈f)
    (completion : t.Completable Set.univ (prefill : Set (Finset Cell))) :
    ∃ tiles, Valid t B prefill tiles := by
  classical
  obtain ⟨all,tiling,retained⟩ := completion
  let tiles := (candidates t B).filter fun f => f∈all
  have member (f : Finset Cell) : f∈tiles ↔ f∈candidates t B ∧ f∈all := Finset.mem_filter
  refine ⟨tiles,?_,?_,?_,?_⟩
  · intro f hf; exact ((member f).mp hf).1
  · intro f hf
    exact (member f).mpr ⟨(mem_candidates t B f).mpr
      ⟨(tiling.tilesInside f (retained hf)).1,meets f hf⟩,retained hf⟩
  · intro f hf g hg c hc hd
    exact (tiling.partial (Set.Subset.refl all)).nonoverlap
      f ((member f).mp hf).2 g ((member g).mp hg).2 c hc hd
  · intro c hc
    obtain ⟨f,⟨hf,hfc⟩,_⟩ := tiling.uniqueCover c (Set.mem_univ c)
    exact ⟨f,(member f).mpr ⟨(mem_candidates t B f).mpr
      ⟨(tiling.tilesInside f hf).1,c,hc,hfc⟩,hf⟩,hfc⟩

/-- At most one selected tile per cell of the covered set is needed. -/
theorem Valid.card_le {t : Tromino} {B : Finset Cell} {prefill tiles : Finset (Finset Cell)}
    (h : Valid t B prefill tiles) : tiles.card ≤ B.card := by
  classical
  have meets : ∀ f : tiles, ∃ c : B, c.val∈f.val := by
    intro f
    obtain ⟨c,hc,hcf⟩ := ((mem_candidates t B f.val).mp (h.1 f.property)).2
    exact ⟨⟨c,hc⟩,hcf⟩
  let pick (f : tiles) : B := Classical.choose (meets f)
  have covers (f : tiles) : (pick f).val∈f.val := Classical.choose_spec (meets f)
  have injective : Function.Injective pick := by
    intro f g equal
    apply Subtype.ext
    exact h.2.2.1 f.val f.property g.val g.property (pick f).val (covers f)
      (by rw [equal]; exact covers g)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective pick injective

/-- Exhaustive finite search; the extension theorem determines when this
finite local condition suffices for a plane completion. -/
def check (t : Tromino) (B : Finset Cell) (prefill : Finset (Finset Cell)) : Bool :=
  decide (∃ tiles∈(candidates t B).powerset, Valid t B prefill tiles)

theorem check_correct (t : Tromino) (B : Finset Cell) (prefill : Finset (Finset Cell)) :
    check t B prefill=true ↔ ∃ tiles, Valid t B prefill tiles := by
  simp only [check,decide_eq_true_eq,Finset.mem_powerset]
  constructor
  · rintro ⟨tiles,_,h⟩; exact ⟨tiles,h⟩
  · rintro ⟨tiles,h⟩; exact ⟨tiles,h.1,h⟩

end LeanTrominoes.Tromino.FiniteWitness
