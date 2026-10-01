/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicBipartiteCore
import LeanTrominoes.PeriodicMatchingDensity
import Mathlib.Combinatorics.Hall.Finite

/-! # Hall's inequalities descend from the infinite matching

Restrict an injective adjacency-preserving map to a box of side `k`. Its
image lies in a neighbor box of side `k+2B`, where `B` bounds all offsets.
Dividing the cardinality inequality by the box volume and taking the limit
gives the finite quotient's Hall inequality. No locality hypothesis is used.
-/
namespace LeanTrominoes.PeriodicBipartite
variable {L R : Type*} {d : Nat} [Fintype L] [Fintype R]

noncomputable def neighbors (edges : List (Edge L R d)) (s : Finset L) : Finset R := by
  classical
  exact ((edges.filter (fun e => e.left ∈ s)).map Edge.right).toFinset

theorem mem_neighbors (edges : List (Edge L R d)) (s : Finset L) (r : R) :
    r ∈ neighbors edges s ↔ ∃ l ∈ s, QuotientAdj edges l r := by
  classical
  simp only [neighbors,List.mem_toFinset,List.mem_map,List.mem_filter,decide_eq_true_eq,QuotientAdj]
  constructor
  · rintro ⟨e,⟨he,hs⟩,hr⟩
    exact ⟨e.left,hs,e,he,rfl,hr⟩
  · rintro ⟨l,hl,e,he,el,er⟩
    exact ⟨e,⟨he,el ▸ hl⟩,er⟩

/-- Only injectivity, not surjectivity, is needed for one side of Hall. -/
theorem quotient_hall (edges : List (Edge L R d))
    (f : L × Lattice d → R × Lattice d) (inj : Function.Injective f)
    (adj : ∀ u, Adj edges u (f u)) (s : Finset L) :
    s.card ≤ (neighbors edges s).card := by
  classical
  apply density_le s.card (neighbors edges s).card (2*radius edges) d
  intro k
  let Source := {l // l ∈ s} × (Fin d → Fin k)
  let Target := {r // r ∈ neighbors edges s} × (Fin d → Fin (k+2*radius edges))
  let src : Source → L × Lattice d := fun x => (x.1.1,fun i => (x.2 i).val)
  have src_inj : Function.Injective src := by
    intro x y h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · funext i
      apply Fin.ext
      have eq := congrFun (congrArg Prod.snd h) i
      change ((x.2 i).val : Int)=((y.2 i).val : Int) at eq
      exact_mod_cast eq
  have member (x : Source) : (f (src x)).1 ∈ neighbors edges s := by
    obtain ⟨e,he,hl,hr,hz⟩ := adj (src x)
    exact (mem_neighbors edges s _).mpr ⟨x.1.1,x.1.2,e,he,hl,hr⟩
  have bounds (x : Source) (i : Fin d) :
      0 ≤ (f (src x)).2 i+(radius edges : Int) ∧
      (f (src x)).2 i+(radius edges : Int) < (k+2*radius edges : Nat) := by
    obtain ⟨e,he,hl,hr,hz⟩ := adj (src x)
    have bound := offset_bound edges e he i
    have upper := Int.le_natAbs (a := e.offset i)
    have lower := Int.le_natAbs (a := -e.offset i)
    rw [Int.natAbs_neg] at lower
    have inside := (x.2 i).isLt
    have coordinate := congrFun hz i
    change (f (src x)).2 i=(x.2 i).val+e.offset i at coordinate
    omega
  let boxed : Source → Target := fun x =>
    (⟨(f (src x)).1,member x⟩,fun i =>
      ⟨((f (src x)).2 i+(radius edges : Int)).toNat,by have h := bounds x i; omega⟩)
  let decode : Target → R × Lattice d := fun y =>
    (y.1.1,fun i => ((y.2 i).val : Int)-(radius edges : Int))
  have decoded (x : Source) : decode (boxed x)=f (src x) := by
    apply Prod.ext
    · rfl
    · funext i
      change (((f (src x)).2 i+(radius edges : Int)).toNat : Int)-(radius edges : Int)=(f (src x)).2 i
      rw [Int.toNat_of_nonneg (bounds x i).1]
      omega
  have boxed_inj : Function.Injective boxed := by
    intro x y h
    apply src_inj
    apply inj
    rw [← decoded x,← decoded y,h]
  have count := Fintype.card_le_of_injective boxed boxed_inj
  simpa only [Source,Target,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe] using count

/-- A perfect matching forces equal cardinalities of the two protovertex colors. -/
theorem colors_card_eq (edges : List (Edge L R d)) (h : HasPerfectMatching edges) :
    Fintype.card L=Fintype.card R := by
  classical
  have left : Fintype.card L ≤ Fintype.card R := by
    obtain ⟨f,hf⟩ := h
    have hall := quotient_hall edges f f.injective hf Finset.univ
    simp only [Finset.card_univ] at hall
    exact hall.trans (Finset.card_le_univ _)
  have right : Fintype.card R ≤ Fintype.card L := by
    obtain ⟨f,hf⟩ := perfect_reverse edges h
    have hall := quotient_hall (edges.map Edge.reverse) f f.injective hf Finset.univ
    simp only [Finset.card_univ] at hall
    exact hall.trans (Finset.card_le_univ _)
  exact Nat.le_antisymm left right

theorem perfect_to_quotient (edges : List (Edge L R d)) (h : HasPerfectMatching edges) :
    HasQuotientMatching edges := by
  classical
  obtain ⟨f,hf⟩ := h
  obtain ⟨g,inj,hg⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun l => neighbors edges {l})).mp (by
      intro s
      have equal : s.biUnion (fun l => neighbors edges {l})=neighbors edges s := by
        ext r
        simp only [Finset.mem_biUnion,mem_neighbors,Finset.mem_singleton]
        aesop
      rw [equal]
      exact quotient_hall edges f f.injective hf s)
  have bij := (Fintype.bijective_iff_injective_and_card g).mpr ⟨inj,colors_card_eq edges ⟨f,hf⟩⟩
  refine ⟨Equiv.ofBijective g bij,?_⟩
  intro l
  have member := (mem_neighbors edges {l} (g l)).mp (hg l)
  simpa using member

end LeanTrominoes.PeriodicBipartite
