import LeanTrominoes.PlanarThreeSATGadgets
import Mathlib.Data.Fintype.Pi

/-!
# Instantiating finite planar 3SAT gadgets

The Figure 8 truth tables are stated using fixed finite variable types and
coordinates.  A periodic planarizer needs renamed copies at many macro-grid
locations.  This file proves that variable renaming and affine placement do
not change satisfaction, and packages crossover copies with fresh internal
variables and caller-supplied boundary ports.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

namespace EmbeddedClause

/-- Rename the variables and transform the position of an embedded clause. -/
def map {Source Target : Type*}
    (variableMap : Source → Target) (positionMap : Cell → Cell)
    (clause : EmbeddedClause Source) : EmbeddedClause Target where
  position := positionMap clause.position
  literals := clause.literals.map fun literal =>
    (variableMap literal.1, literal.2)

/-- Rename only the variables of an embedded clause. -/
def rename {Source Target : Type*}
    (variableMap : Source → Target)
    (clause : EmbeddedClause Source) : EmbeddedClause Target :=
  clause.map variableMap id

/-- Place an embedded clause in a scaled macro-grid cell. -/
def place {Variable : Type*} (origin : Cell) (scale : Int)
    (clause : EmbeddedClause Variable) : EmbeddedClause Variable :=
  clause.map id fun position =>
    Cell.add origin (Cell.scale scale position)

end EmbeddedClause

@[simp]
theorem clauseHolds_map
    {Source Target : Type*}
    (assignment : Target → Bool)
    (variableMap : Source → Target) (positionMap : Cell → Cell)
    (clause : EmbeddedClause Source) :
    ClauseHolds assignment (clause.map variableMap positionMap) ↔
      ClauseHolds (assignment ∘ variableMap) clause := by
  unfold ClauseHolds
  constructor
  · rintro ⟨literal, literalMem, holds⟩
    rcases List.mem_map.mp literalMem with
      ⟨sourceLiteral, sourceMem, literalEq⟩
    subst literal
    exact ⟨sourceLiteral, sourceMem, holds⟩
  · rintro ⟨literal, literalMem, holds⟩
    exact ⟨(variableMap literal.1, literal.2),
      List.mem_map.mpr ⟨literal, literalMem, rfl⟩, holds⟩

@[simp]
theorem formulaHolds_map
    {Source Target : Type*}
    (assignment : Target → Bool)
    (variableMap : Source → Target) (positionMap : Cell → Cell)
    (formula : List (EmbeddedClause Source)) :
    FormulaHolds assignment
        (formula.map fun clause => clause.map variableMap positionMap) ↔
      FormulaHolds (assignment ∘ variableMap) formula := by
  unfold FormulaHolds
  constructor
  · intro holds clause clauseMem
    apply (clauseHolds_map assignment
      variableMap positionMap clause).mp
    exact holds (clause.map variableMap positionMap)
      (List.mem_map.mpr ⟨clause, clauseMem, rfl⟩)
  · intro holds mappedClause mappedMem
    rcases List.mem_map.mp mappedMem with
      ⟨clause, clauseMem, mappedEq⟩
    subst mappedClause
    apply (clauseHolds_map assignment
      variableMap positionMap clause).mpr
    exact holds clause clauseMem

/-- A renamed and geometrically placed copy of an embedded formula. -/
def instantiateFormula {Source Target : Type*}
    (variableMap : Source → Target)
    (origin : Cell) (scale : Int)
    (formula : List (EmbeddedClause Source)) :
    List (EmbeddedClause Target) :=
  formula.map fun clause =>
    (clause.rename variableMap).place origin scale

@[simp]
theorem formulaHolds_instantiateFormula
    {Source Target : Type*}
    (assignment : Target → Bool)
    (variableMap : Source → Target)
    (origin : Cell) (scale : Int)
    (formula : List (EmbeddedClause Source)) :
    FormulaHolds assignment
        (instantiateFormula variableMap origin scale formula) ↔
      FormulaHolds (assignment ∘ variableMap) formula := by
  unfold instantiateFormula FormulaHolds
  constructor
  · intro holds clause clauseMem
    have placedHolds :=
      holds ((clause.rename variableMap).place origin scale)
        (List.mem_map.mpr ⟨clause, clauseMem, rfl⟩)
    rw [EmbeddedClause.place, clauseHolds_map] at placedHolds
    simpa [EmbeddedClause.rename, Function.comp_def] using placedHolds
  · intro holds placedClause placedMem
    rcases List.mem_map.mp placedMem with
      ⟨clause, clauseMem, placedEq⟩
    subst placedClause
    rw [EmbeddedClause.place, clauseHolds_map]
    simpa [EmbeddedClause.rename, Function.comp_def] using
      holds clause clauseMem

/-! ## Crossover instances -/

/-- Caller-supplied variables attached to the four crossover ports. -/
structure CrossoverPorts (Variable : Type*) where
  aLeft : Variable
  aRight : Variable
  bTop : Variable
  bBottom : Variable
  deriving DecidableEq, Repr

/-- The nine non-boundary variables of a crossover copy. -/
inductive CrossoverInternal
  | aInnerLeft
  | upperLeft
  | lowerLeft
  | bInnerTop
  | center
  | bInnerBottom
  | upperRight
  | lowerRight
  | aInnerRight
  deriving DecidableEq, Repr, Fintype

/-- Rename the fixed crossover variables into supplied boundary variables and
fresh local internal variables. -/
def crossoverVariableMap {Variable : Type*}
    (ports : CrossoverPorts Variable) :
    CrossoverVariable → Sum Variable CrossoverInternal
  | .aLeft => .inl ports.aLeft
  | .aRight => .inl ports.aRight
  | .bTop => .inl ports.bTop
  | .bBottom => .inl ports.bBottom
  | .aInnerLeft => .inr .aInnerLeft
  | .upperLeft => .inr .upperLeft
  | .lowerLeft => .inr .lowerLeft
  | .bInnerTop => .inr .bInnerTop
  | .center => .inr .center
  | .bInnerBottom => .inr .bInnerBottom
  | .upperRight => .inr .upperRight
  | .lowerRight => .inr .lowerRight
  | .aInnerRight => .inr .aInnerRight

/-- One renamed and placed crossover formula. -/
def crossoverInstance {Variable : Type*}
    (ports : CrossoverPorts Variable)
    (origin : Cell) (scale : Int) :
    List (EmbeddedClause (Sum Variable CrossoverInternal)) :=
  instantiateFormula (crossoverVariableMap ports)
    origin scale crossoverFormula

@[simp]
theorem crossoverInstance_holds_iff
    {Variable : Type*}
    (assignment : Sum Variable CrossoverInternal → Bool)
    (ports : CrossoverPorts Variable)
    (origin : Cell) (scale : Int) :
    FormulaHolds assignment (crossoverInstance ports origin scale) ↔
      CrossoverHolds (assignment ∘ crossoverVariableMap ports) := by
  exact formulaHolds_instantiateFormula
    assignment (crossoverVariableMap ports) origin scale crossoverFormula

/-- A fixed assignment on external variables extends through a fresh
crossover copy. -/
def CrossoverInstanceExtends {Variable : Type*}
    (assignment : Variable → Bool) (ports : CrossoverPorts Variable)
    (origin : Cell) (scale : Int) : Prop :=
  ∃ internal : CrossoverInternal → Bool,
    FormulaHolds (Sum.elim assignment internal)
      (crossoverInstance ports origin scale)

instance {Variable : Type*} [DecidableEq Variable]
    (assignment : Variable → Bool) (ports : CrossoverPorts Variable)
    (origin : Cell) (scale : Int) :
    Decidable (CrossoverInstanceExtends assignment ports origin scale) := by
  unfold CrossoverInstanceExtends
  exact Fintype.decidableExistsFintype

/-- Fresh crossover instances extend exactly when opposite boundary values
agree independently. -/
theorem crossoverInstanceExtends_iff
    {Variable : Type*} [DecidableEq Variable]
    (assignment : Variable → Bool) (ports : CrossoverPorts Variable)
    (origin : Cell) (scale : Int) :
    CrossoverInstanceExtends assignment ports origin scale ↔
      assignment ports.aLeft = assignment ports.aRight ∧
        assignment ports.bTop = assignment ports.bBottom := by
  constructor
  · rintro ⟨internal, instanceHolds⟩
    have crossoverHolds :
        CrossoverHolds
          (Sum.elim assignment internal ∘ crossoverVariableMap ports) :=
      (crossoverInstance_holds_iff
        (Sum.elim assignment internal) ports origin scale).mp instanceHolds
    exact crossover_boundary_eq_of_holds crossoverHolds
  · intro boundaryEq
    have extensionExists :
        CrossoverExtends
          (assignment ports.aLeft) (assignment ports.aRight)
          (assignment ports.bTop) (assignment ports.bBottom) :=
      (crossoverExtends_iff _ _ _ _).mpr boundaryEq
    rcases extensionExists with
      ⟨aInnerLeft, upperLeft, lowerLeft, bInnerTop, center, bInnerBottom,
        upperRight, lowerRight, aInnerRight, crossoverHolds⟩
    let internal : CrossoverInternal → Bool
      | .aInnerLeft => aInnerLeft
      | .upperLeft => upperLeft
      | .lowerLeft => lowerLeft
      | .bInnerTop => bInnerTop
      | .center => center
      | .bInnerBottom => bInnerBottom
      | .upperRight => upperRight
      | .lowerRight => lowerRight
      | .aInnerRight => aInnerRight
    refine ⟨internal, ?_⟩
    apply (crossoverInstance_holds_iff
      (Sum.elim assignment internal) ports origin scale).mpr
    have assignmentEq :
        Sum.elim assignment internal ∘ crossoverVariableMap ports =
          crossoverAssignment
            (assignment ports.aLeft) (assignment ports.aRight)
            (assignment ports.bTop) (assignment ports.bBottom)
            aInnerLeft upperLeft lowerLeft bInnerTop center bInnerBottom
            upperRight lowerRight aInnerRight := by
      funext inputVariable
      cases inputVariable <;> rfl
    rw [assignmentEq]
    exact crossoverHolds

/-! ## Duplicator instances -/

/-- Caller-supplied variables attached to the center and three duplicator
ports. -/
structure DuplicatorPorts (Variable : Type*) where
  center : Variable
  left : Variable
  top : Variable
  right : Variable
  deriving DecidableEq, Repr

/-- Rename the fixed duplicator variables to caller-supplied variables. -/
def duplicatorVariableMap {Variable : Type*}
    (ports : DuplicatorPorts Variable) : DuplicatorVariable → Variable
  | .center => ports.center
  | .left => ports.left
  | .top => ports.top
  | .right => ports.right

/-- One renamed and placed duplicator formula. -/
def duplicatorInstance {Variable : Type*}
    (ports : DuplicatorPorts Variable)
    (origin : Cell) (scale : Int) :
    List (EmbeddedClause Variable) :=
  instantiateFormula (duplicatorVariableMap ports)
    origin scale duplicatorFormula

/-- A duplicator copy is satisfied exactly when its three ports agree with
its center. -/
theorem duplicatorInstance_holds_iff
    {Variable : Type*}
    (assignment : Variable → Bool)
    (ports : DuplicatorPorts Variable)
    (origin : Cell) (scale : Int) :
    FormulaHolds assignment (duplicatorInstance ports origin scale) ↔
      assignment ports.left = assignment ports.center ∧
        assignment ports.top = assignment ports.center ∧
        assignment ports.right = assignment ports.center := by
  rw [duplicatorInstance,
    formulaHolds_instantiateFormula]
  simpa [duplicatorVariableMap, Function.comp_apply] using
    duplicator_holds_iff (assignment ∘ duplicatorVariableMap ports)

end PlanarThreeSAT
end LeanTrominoes
