import LeanTrominoes.PlanarThreeSATInstantiation

/-!
# Finite families of planar 3SAT gadgets

A periodic fundamental domain contains finitely many macro-grid sites.  This
file concatenates one positioned gadget formula per site.  Crossover internal
variables are scoped by the site key, so different copies cannot capture one
another, while their boundary variables remain caller supplied.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- Satisfaction of a concatenated family is satisfaction of every member
formula at every listed site. -/
theorem formulaHolds_flatMap_iff
    {Site Variable : Type*}
    (assignment : Variable → Bool)
    (sites : List Site)
    (formulaAt : Site → List (EmbeddedClause Variable)) :
    FormulaHolds assignment (sites.flatMap formulaAt) ↔
      ∀ site ∈ sites, FormulaHolds assignment (formulaAt site) := by
  unfold FormulaHolds
  constructor
  · intro holds site siteMem clause clauseMem
    exact holds clause
      (List.mem_flatMap.mpr ⟨site, siteMem, clauseMem⟩)
  · intro holds clause clauseMem
    rcases List.mem_flatMap.mp clauseMem with
      ⟨site, siteMem, clauseMem⟩
    exact holds site siteMem clause clauseMem

/-- Scope the nine internal variables of one crossover by its site key. -/
def scopedCrossoverVariableMap {Site Variable : Type*}
    (site : Site) (ports : CrossoverPorts Variable) :
    CrossoverVariable → Sum Variable (Site × CrossoverInternal)
  | .aLeft => .inl ports.aLeft
  | .aRight => .inl ports.aRight
  | .bTop => .inl ports.bTop
  | .bBottom => .inl ports.bBottom
  | .aInnerLeft => .inr (site, .aInnerLeft)
  | .upperLeft => .inr (site, .upperLeft)
  | .lowerLeft => .inr (site, .lowerLeft)
  | .bInnerTop => .inr (site, .bInnerTop)
  | .center => .inr (site, .center)
  | .bInnerBottom => .inr (site, .bInnerBottom)
  | .upperRight => .inr (site, .upperRight)
  | .lowerRight => .inr (site, .lowerRight)
  | .aInnerRight => .inr (site, .aInnerRight)

/-- One positioned crossover whose internal variables carry a site key. -/
def scopedCrossoverInstance {Site Variable : Type*}
    (site : Site) (ports : CrossoverPorts Variable)
    (origin : Cell) (scale : Int) :
    List (EmbeddedClause (Sum Variable (Site × CrossoverInternal))) :=
  instantiateFormula (scopedCrossoverVariableMap site ports)
    origin scale crossoverFormula

@[simp]
theorem scopedCrossoverInstance_holds_iff
    {Site Variable : Type*}
    (assignment : Sum Variable (Site × CrossoverInternal) → Bool)
    (site : Site) (ports : CrossoverPorts Variable)
    (origin : Cell) (scale : Int) :
    FormulaHolds assignment
        (scopedCrossoverInstance site ports origin scale) ↔
      CrossoverHolds
        (assignment ∘ scopedCrossoverVariableMap site ports) := by
  exact formulaHolds_instantiateFormula assignment
    (scopedCrossoverVariableMap site ports)
    origin scale crossoverFormula

/-- Concatenate one crossover copy at every listed site. -/
def crossoverFamily {Site Variable : Type*}
    (sites : List Site)
    (ports : Site → CrossoverPorts Variable)
    (origin : Site → Cell) (scale : Int) :
    List (EmbeddedClause (Sum Variable (Site × CrossoverInternal))) :=
  sites.flatMap fun site =>
    scopedCrossoverInstance site (ports site) (origin site) scale

/-- The family formula is exactly the conjunction of the independently
scoped crossover truth tables. -/
theorem crossoverFamily_holds_iff
    {Site Variable : Type*}
    (assignment : Sum Variable (Site × CrossoverInternal) → Bool)
    (sites : List Site)
    (ports : Site → CrossoverPorts Variable)
    (origin : Site → Cell) (scale : Int) :
    FormulaHolds assignment
        (crossoverFamily sites ports origin scale) ↔
      ∀ site ∈ sites,
        CrossoverHolds
          (assignment ∘ scopedCrossoverVariableMap site (ports site)) := by
  rw [crossoverFamily, formulaHolds_flatMap_iff]
  constructor
  · intro holds site siteMem
    exact (scopedCrossoverInstance_holds_iff
      assignment site (ports site) (origin site) scale).mp
        (holds site siteMem)
  · intro holds site siteMem
    exact (scopedCrossoverInstance_holds_iff
      assignment site (ports site) (origin site) scale).mpr
        (holds site siteMem)

/-- Every satisfying crossover family propagates the two signals
independently at every listed site. -/
theorem crossoverFamily_boundary_eq
    {Site Variable : Type*}
    (assignment : Sum Variable (Site × CrossoverInternal) → Bool)
    (sites : List Site)
    (ports : Site → CrossoverPorts Variable)
    (origin : Site → Cell) (scale : Int)
    (holds : FormulaHolds assignment
      (crossoverFamily sites ports origin scale)) :
    ∀ site ∈ sites,
      assignment (.inl (ports site).aLeft) =
          assignment (.inl (ports site).aRight) ∧
        assignment (.inl (ports site).bTop) =
          assignment (.inl (ports site).bBottom) := by
  intro site siteMem
  have siteHolds :=
    (crossoverFamily_holds_iff
      assignment sites ports origin scale).mp holds site siteMem
  simpa [scopedCrossoverVariableMap, Function.comp_apply] using
    crossover_boundary_eq_of_holds siteHolds

/-! ## Duplicator families -/

/-- Concatenate one renamed duplicator at every listed site. -/
def duplicatorFamily {Site Variable : Type*}
    (sites : List Site)
    (ports : Site → DuplicatorPorts Variable)
    (origin : Site → Cell) (scale : Int) :
    List (EmbeddedClause Variable) :=
  sites.flatMap fun site =>
    duplicatorInstance (ports site) (origin site) scale

/-- A duplicator family is satisfied exactly when the three ports agree with
the center at every listed site. -/
theorem duplicatorFamily_holds_iff
    {Site Variable : Type*}
    (assignment : Variable → Bool)
    (sites : List Site)
    (ports : Site → DuplicatorPorts Variable)
    (origin : Site → Cell) (scale : Int) :
    FormulaHolds assignment
        (duplicatorFamily sites ports origin scale) ↔
      ∀ site ∈ sites,
        assignment (ports site).left = assignment (ports site).center ∧
          assignment (ports site).top = assignment (ports site).center ∧
          assignment (ports site).right =
            assignment (ports site).center := by
  rw [duplicatorFamily, formulaHolds_flatMap_iff]
  constructor
  · intro holds site siteMem
    exact (duplicatorInstance_holds_iff
      assignment (ports site) (origin site) scale).mp
        (holds site siteMem)
  · intro holds site siteMem
    exact (duplicatorInstance_holds_iff
      assignment (ports site) (origin site) scale).mpr
        (holds site siteMem)

end PlanarThreeSAT
end LeanTrominoes
