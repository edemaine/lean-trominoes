/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATFamilies

/-!
# Simultaneous extension of crossover families

Scoping internal variables by site makes the local crossover completeness
theorem compositional.  An assignment to all external wire variables extends
through the entire finite family exactly when the two opposite-port
equalities hold at every listed crossing.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- An external assignment extends to all site-scoped crossover internals. -/
def CrossoverFamilyExtends {Site Variable : Type*}
    (assignment : Variable → Bool)
    (sites : List Site)
    (ports : Site → CrossoverPorts Variable)
    (origin : Site → Cell) (scale : Int) : Prop :=
  ∃ internal : Site × CrossoverInternal → Bool,
    FormulaHolds (Sum.elim assignment internal)
      (crossoverFamily sites ports origin scale)

/-- Independent local crossover completeness composes over an arbitrary
finite family. -/
theorem crossoverFamilyExtends_iff
    {Site Variable : Type*}
    [DecidableEq Site] [DecidableEq Variable]
    (assignment : Variable → Bool)
    (sites : List Site)
    (ports : Site → CrossoverPorts Variable)
    (origin : Site → Cell) (scale : Int) :
    CrossoverFamilyExtends assignment sites ports origin scale ↔
      ∀ site ∈ sites,
        assignment (ports site).aLeft =
            assignment (ports site).aRight ∧
          assignment (ports site).bTop =
            assignment (ports site).bBottom := by
  constructor
  · rintro ⟨internal, holds⟩
    intro site siteMem
    simpa using crossoverFamily_boundary_eq
      (Sum.elim assignment internal) sites ports origin scale
        holds site siteMem
  · intro boundaryEq
    classical
    have siteExtends (site : Site) (siteMem : site ∈ sites) :
        CrossoverInstanceExtends assignment
          (ports site) (origin site) scale :=
      (crossoverInstanceExtends_iff
        assignment (ports site) (origin site) scale).mpr
          (boundaryEq site siteMem)
    let localInternal (site : Site) : CrossoverInternal → Bool :=
      if siteMem : site ∈ sites then
        Classical.choose (siteExtends site siteMem)
      else
        fun _ => false
    let internal : Site × CrossoverInternal → Bool :=
      fun pair => localInternal pair.1 pair.2
    refine ⟨internal,
      (crossoverFamily_holds_iff
        (Sum.elim assignment internal)
        sites ports origin scale).mpr ?_⟩
    intro site siteMem
    have localHolds :
        FormulaHolds (Sum.elim assignment (localInternal site))
          (crossoverInstance (ports site) (origin site) scale) := by
      simpa [localInternal, siteMem] using
        Classical.choose_spec (siteExtends site siteMem)
    have localCrossover :
        CrossoverHolds
          (Sum.elim assignment (localInternal site) ∘
            crossoverVariableMap (ports site)) :=
      (crossoverInstance_holds_iff
        (Sum.elim assignment (localInternal site))
        (ports site) (origin site) scale).mp localHolds
    have assignmentEq :
        Sum.elim assignment internal ∘
            scopedCrossoverVariableMap site (ports site) =
          Sum.elim assignment (localInternal site) ∘
            crossoverVariableMap (ports site) := by
      funext inputVariable
      cases inputVariable <;> rfl
    rw [assignmentEq]
    exact localCrossover

end PlanarThreeSAT
end LeanTrominoes
