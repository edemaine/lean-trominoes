/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.LatticeSaturationFrame
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Bounded lattice generators admit a bounded full-rank frame -/
namespace LeanTrominoes.ImplicationGraph
open Module Submodule
open scoped BigOperators Matrix
abbrev RationalLattice (d : Nat) := Fin d → Rat
def rationalize {d : Nat} (v : IntegralLattice d) : RationalLattice d := fun i => v i

private theorem rationalize_injective {d : Nat} : Function.Injective (@rationalize d) := by
  intro v w equal
  funext i
  have coordinate : (v i : Rat)=(w i : Rat) := congrFun equal i
  exact_mod_cast coordinate

/-- Extend a maximal independent subset of the generators using only standard unit vectors.
Every frame entry is still bounded by B, including for a rank-deficient subgroup. -/
theorem bounded_frame {d : Nat} (S : Set (IntegralLattice d)) (B : Nat) (positive : 1 ≤ B)
    (bounded : ∀ g ∈ S, ∀ i, (g i).natAbs ≤ B) :
    ∃ frame : SaturationFrame S, ∀ i j, (frame.matrix i j).natAbs ≤ B := by
  classical
  let Q := rationalize '' S
  let emptyIndependent := linearIndepOn_empty Rat (id : RationalLattice d → RationalLattice d)
  let independent := emptyIndependent.extend (Set.empty_subset Q)
  have independent_sub : independent ⊆ Q := emptyIndependent.extend_subset _
  have independent_li : LinearIndepOn Rat id independent := emptyIndependent.linearIndepOn_extend _
  have generators_span : Q ⊆ span Rat independent := emptyIndependent.subset_span_extend _
  let standard := Pi.basisFun Rat (Fin d)
  let pool := Q ∪ Set.range standard
  have inPool : independent ⊆ pool := fun v hv => Or.inl (independent_sub hv)
  have spanning : ⊤ ≤ span Rat pool := by
    rw [← standard.span_eq]
    exact span_mono Set.subset_union_right
  let original := Basis.extendLe independent_li inPool spanning
  letI := FiniteDimensional.fintypeBasisIndex original
  have card : Fintype.card (independent_li.extend inPool)=Fintype.card (Fin d) := by
    rw [← Module.finrank_eq_card_basis original]
    simp
  let indices := Fintype.equivOfCardEq card
  let basis := original.reindex indices
  have basisIn (j : Fin d) : basis j ∈ pool := by
    have member := Basis.extendLe_subset independent_li inPool spanning ⟨indices.symm j,rfl⟩
    simpa only [basis,Basis.reindex_apply,original] using member
  have contains : independent ⊆ Set.range basis := by
    intro v hv
    obtain ⟨j,hj⟩ := Basis.subset_extendLe independent_li inPool spanning hv
    exact ⟨indices j,by simpa [basis,original] using hj⟩
  have integral (j : Fin d) : ∃ v : IntegralLattice d,
      rationalize v=basis j ∧ ∀ i, (v i).natAbs ≤ B := by
    rcases basisIn j with generator | unit
    · obtain ⟨v,hv,equal⟩ := generator
      exact ⟨v,equal,bounded v hv⟩
    · obtain ⟨k,equal⟩ := unit
      refine ⟨fun i => if i=k then 1 else 0,?_,?_⟩
      · rw [← equal]
        ext i
        simp [standard,rationalize,Pi.basisFun_apply,Pi.single_apply,eq_comm]
      · intro i
        dsimp
        split_ifs <;> simp <;> omega
  choose columns columns_eq columns_bound using integral
  let A : Matrix (Fin d) (Fin d) Int := fun i j => columns j i
  let active : Finset (Fin d) := Finset.univ.filter (fun j => basis j ∈ independent)
  let f : Int →+* Rat := Int.castRingHom Rat
  have matrix_eq : f.mapMatrix A=standard.toMatrix basis := by
    ext i j
    simpa [A,Basis.toMatrix_apply,standard,Pi.basisFun_repr,rationalize] using congrFun (columns_eq j) i
  have nonzero : A.det ≠ 0 := by
    letI := standard.invertibleToMatrix basis
    have invertible := Matrix.isUnit_det_of_invertible (standard.toMatrix basis)
    intro zero
    have castZero : (f.mapMatrix A).det=0 := by rw [← f.map_det,zero]; simp
    rw [matrix_eq] at castZero
    exact invertible.ne_zero castZero
  have active_mem (j : Fin d) (hj : j ∈ active) : columns j ∈ AddSubgroup.closure S := by
    have independentMember := (Finset.mem_filter.mp hj).2
    obtain ⟨v,hv,equal⟩ := independent_sub independentMember
    have same : columns j=v := rationalize_injective ((columns_eq j).trans equal.symm)
    rw [same]
    exact AddSubgroup.subset_closure hv
  have active_image : basis '' {j | j ∈ active}=independent := by
    ext v
    constructor
    · rintro ⟨j,hj,rfl⟩
      simpa [active] using hj
    · intro hv
      obtain ⟨j,rfl⟩ := contains hv
      exact ⟨j,by simpa [active] using hv,rfl⟩
  have outside (g : IntegralLattice d) (hg : g ∈ S) (j : Fin d) (hj : j ∉ active) :
      (A.adjugate *ᵥ g) j=0 := by
    have inSpan : rationalize g ∈ span Rat (basis '' {j | j ∈ active}) := by
      rw [active_image]
      exact generators_span ⟨g,hg,rfl⟩
    have support := basis.repr_support_subset_of_mem_span {j | j ∈ active} inSpan
    have coordinate : basis.repr (rationalize g) j=0 := by
      by_contra nonzero
      exact hj (support (Finsupp.mem_support_iff.mpr nonzero))
    have reconstruct : f.mapMatrix A *ᵥ basis.repr (rationalize g)=rationalize g := by
      rw [matrix_eq]
      have one := basis.toMatrix_mulVec_repr standard (rationalize g)
      refine one.trans ?_
      ext i
      exact Pi.basisFun_repr Rat (Fin d) (rationalize g) i
    have adjugate : (f.mapMatrix A).adjugate *ᵥ rationalize g =
        (f.mapMatrix A).det • basis.repr (rationalize g) := by
      calc
        _ = (f.mapMatrix A).adjugate *ᵥ (f.mapMatrix A *ᵥ basis.repr (rationalize g)) :=
          congrArg (fun v => (f.mapMatrix A).adjugate *ᵥ v) reconstruct.symm
        _ = _ := by rw [Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec]
    have castCoordinate : f ((A.adjugate *ᵥ g) j)=0 := by
      rw [f.map_mulVec]
      change (f.mapMatrix A.adjugate *ᵥ rationalize g) j=0
      rw [f.map_adjugate]
      change ((f.mapMatrix A).adjugate *ᵥ rationalize g) j=0
      rw [adjugate,Pi.smul_apply,coordinate,smul_zero]
    change (((A.adjugate *ᵥ g) j : Int) : Rat)=0 at castCoordinate
    exact_mod_cast castCoordinate
  refine ⟨⟨A,active,nonzero,active_mem,outside⟩,?_⟩
  intro i j
  exact columns_bound j i

end LeanTrominoes.ImplicationGraph
