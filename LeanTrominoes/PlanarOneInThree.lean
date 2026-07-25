import LeanTrominoes.PeriodicOneInThreeCorrectness
import LeanTrominoes.PlanarThreeSATInstantiation

/-!
# Positioned planar 3SAT-to-1-in-3SAT gadgets

This file gives the Boolean and geometric interface for Figure 9 of the
paper.  Each embedded disjunctive clause is replaced inside a constant-size
grid box by the already verified three-clause exact-one gadget.  Auxiliary
variables retain the source-clause index, so gadgets belonging to distinct
clause occurrences are independent.

The positions recorded here are the clause-vertex positions of the refined
drawing.  Boolean correctness deliberately ignores those positions; later
geometry modules can route the incidences using the displayed local layout.
-/

namespace LeanTrominoes
namespace PlanarOneInThree

open PlanarThreeSAT
open PeriodicOneInThree

/-- Refine every source drawing cell to a `12 × 12` Figure 9 box.  The
extra room separates all clause and auxiliary-variable vertices on the
integer grid, and leaves routing lanes for the later planar incidence
certificate. -/
def gadgetScale : Int := 12

/-- Position of a generated exact-one clause inside a refined source box.
The first three positions are respectively the top, left, and right clauses
of Figure 9.  The remaining positions accommodate forced-false padding
clauses for source clauses of width below three. -/
def generatedClausePosition (sourcePosition : Cell)
    (generatedIndex : Nat) : Cell :=
  let localOffset : Cell :=
    match generatedIndex with
    | 0 => (6, 2)
    | 1 => (3, 5)
    | 2 => (9, 5)
    | 3 => (3, 10)
    | 4 => (6, 10)
    | _ => (9, 10)
  Cell.add (Cell.scale gadgetScale sourcePosition) localOffset

/-- Forget an embedded clause's drawing position and put all of its literals
at offset zero. -/
def zeroOffsetClause {Variable : Type*}
    (source : EmbeddedClause Variable) : PeriodicClause Variable :=
  source.literals.map fun literal =>
    ⟨literal.1, (0, 0), literal.2⟩

/-- Recover an embedded exact-one clause from a periodic clause.  This
operation forgets literal offsets; every clause produced from
`zeroOffsetClause` has a common zero offset. -/
def embedGeneratedClause {Variable : Type*}
    (position : Cell)
    (clause : PeriodicClause (OneInThreeVariable Variable)) :
    EmbeddedClause (OneInThreeVariable Variable) where
  position := position
  literals := clause.map fun literal => (literal.atom, literal.value)

/-- Exactly one literal occurrence of an embedded clause is true. -/
def ClauseHolds {Variable : Type*}
    (assignment : Variable → Bool)
    (clause : EmbeddedClause Variable) : Prop :=
  ExactlyOne
    (clause.literals.map fun literal =>
      assignment literal.1 == literal.2)

instance {Variable : Type*} [DecidableEq Variable]
    (assignment : Variable → Bool)
    (clause : EmbeddedClause Variable) :
    Decidable (ClauseHolds assignment clause) := by
  unfold ClauseHolds
  infer_instance

/-- Every clause in a positioned exact-one formula holds. -/
def FormulaHolds {Variable : Type*}
    (assignment : Variable → Bool)
    (formula : List (EmbeddedClause Variable)) : Prop :=
  ∀ clause ∈ formula, ClauseHolds assignment clause

instance {Variable : Type*} [DecidableEq Variable]
    (assignment : Variable → Bool)
    (formula : List (EmbeddedClause Variable)) :
    Decidable (FormulaHolds assignment formula) := by
  unfold FormulaHolds
  infer_instance

/-- Replace one positioned source clause by its local Figure 9 gadget. -/
def clauseGadget {Variable : Type*}
    (clauseIndex : Nat) (source : EmbeddedClause Variable) :
    List (EmbeddedClause (OneInThreeVariable Variable)) :=
  (PeriodicOneInThree.clauseClauses
      clauseIndex (zeroOffsetClause source)).zipIdx.map
    fun taggedClause =>
      embedGeneratedClause
        (generatedClausePosition source.position taggedClause.2)
        taggedClause.1

/-- Replace every positioned source clause, retaining its presentation index
as the scope of its fresh auxiliary variables. -/
def formula {Variable : Type*}
    (source : List (EmbeddedClause Variable)) :
    List (EmbeddedClause (OneInThreeVariable Variable)) :=
  source.zipIdx.flatMap fun taggedClause =>
    clauseGadget taggedClause.2 taggedClause.1

/-- A finite embedded disjunctive formula has a satisfying assignment. -/
def SourceSatisfiable {Variable : Type*}
    (source : List (EmbeddedClause Variable)) : Prop :=
  ∃ assignment : Variable → Bool,
    PlanarThreeSAT.FormulaHolds assignment source

/-- A finite embedded exact-one formula has a satisfying assignment. -/
def Satisfiable {Variable : Type*}
    (target : List (EmbeddedClause Variable)) : Prop :=
  ∃ assignment : Variable → Bool, FormulaHolds assignment target

/-- Evaluate a finite assignment independently of the lattice cell. -/
def constantAssignment {Variable : Type*}
    (assignment : Variable → Bool) : Variable → Cell → Bool :=
  fun atom _cell => assignment atom

/-- Restrict an exact-one assignment to the original-variable summand. -/
def restrictAssignment {Variable : Type*}
    (assignment : OneInThreeVariable Variable → Bool) :
    Variable → Bool :=
  fun atom => assignment (Sum.inl atom)

/-- The periodic source semantics at offset zero is the finite embedded
disjunction semantics. -/
theorem zeroOffsetClause_holds_iff {Variable : Type*}
    (assignment : Variable → Bool)
    (source : EmbeddedClause Variable) :
    (zeroOffsetClause source).Holds
        (constantAssignment assignment) (0, 0) ↔
      PlanarThreeSAT.ClauseHolds assignment source := by
  constructor
  · rintro ⟨literal, literalMem, literalHolds⟩
    rcases List.mem_map.mp literalMem with
      ⟨sourceLiteral, sourceLiteralMem, literalEq⟩
    subst literal
    exact ⟨sourceLiteral, sourceLiteralMem, literalHolds⟩
  · rintro ⟨sourceLiteral, sourceLiteralMem, sourceLiteralHolds⟩
    exact
      ⟨⟨sourceLiteral.1, (0, 0), sourceLiteral.2⟩,
        List.mem_map.mpr
          ⟨sourceLiteral, sourceLiteralMem, rfl⟩,
        sourceLiteralHolds⟩

/-- Forgetting a generated clause's geometry preserves exact-one
satisfaction under a cell-independent assignment. -/
theorem embedGeneratedClause_holds_iff {Variable : Type*}
    (assignment : OneInThreeVariable Variable → Bool)
    (position : Cell)
    (clause : PeriodicClause (OneInThreeVariable Variable)) :
    ClauseHolds assignment (embedGeneratedClause position clause) ↔
      PeriodicOneInThree.ClauseHolds
        (constantAssignment assignment) (0, 0) clause := by
  simp [ClauseHolds, PeriodicOneInThree.ClauseHolds,
    PeriodicOneInThree.clauseValues, embedGeneratedClause,
    constantAssignment, List.map_map, Function.comp_def]

/-- The canonical periodic auxiliary extension induces a finite assignment
for one positioned gadget family. -/
def extendAssignment {Variable : Type*}
    (assignment : Variable → Bool) :
    OneInThreeVariable Variable → Bool :=
  fun atom =>
    PeriodicOneInThree.extendAssignment
      (constantAssignment assignment) atom (0, 0)

@[simp]
theorem extendAssignment_original {Variable : Type*}
    (assignment : Variable → Bool) (atom : Variable) :
    extendAssignment assignment (Sum.inl atom) = assignment atom := by
  rfl

/-- Extending a cell-independent source assignment is again
cell-independent. -/
theorem constantAssignment_extendAssignment {Variable : Type*}
    (assignment : Variable → Bool) :
    constantAssignment (extendAssignment assignment) =
      PeriodicOneInThree.extendAssignment
        (constantAssignment assignment) := by
  funext atom cell
  cases atom with
  | inl atom =>
      rfl
  | inr auxiliary =>
      rcases auxiliary with ⟨taggedClause, kind⟩
      rcases taggedClause with ⟨clauseIndex, source⟩
      simp [extendAssignment,
        PeriodicOneInThree.extendAssignment,
        constantAssignment, PeriodicOneInThree.clauseBits,
        PeriodicOneInThree.literalTruth]

/-- Restricting a cell-independent exact-one assignment commutes with making
it periodic. -/
theorem periodic_restrict_constantAssignment {Variable : Type*}
    (assignment : OneInThreeVariable Variable → Bool) :
    PeriodicOneInThree.restrictAssignment
        (constantAssignment assignment) =
      constantAssignment (restrictAssignment assignment) := by
  rfl

/-- A satisfied width-three embedded disjunction extends to a satisfying
positioned Figure 9 gadget. -/
theorem clauseGadget_complete {Variable : Type*}
    (assignment : Variable → Bool)
    (clauseIndex : Nat) (source : EmbeddedClause Variable)
    (width : source.literals.length ≤ 3)
    (sourceHolds : PlanarThreeSAT.ClauseHolds assignment source) :
    FormulaHolds (extendAssignment assignment)
      (clauseGadget clauseIndex source) := by
  have periodicSourceHolds :
      (zeroOffsetClause source).Holds
        (constantAssignment assignment) (0, 0) :=
    (zeroOffsetClause_holds_iff assignment source).mpr sourceHolds
  have periodicWidth :
      (zeroOffsetClause source).WidthAtMost 3 := by
    simpa [zeroOffsetClause, PeriodicClause.WidthAtMost] using width
  have generatedHolds :=
    PeriodicOneInThree.clauseClauses_complete
      (constantAssignment assignment) (0, 0)
      clauseIndex (zeroOffsetClause source)
      periodicWidth periodicSourceHolds
  intro embeddedClause embeddedMem
  rcases List.mem_map.mp embeddedMem with
    ⟨taggedClause, taggedMem, embeddedEq⟩
  subst embeddedClause
  apply
    (embedGeneratedClause_holds_iff
      (extendAssignment assignment)
      (generatedClausePosition source.position taggedClause.2)
      taggedClause.1).mpr
  rw [constantAssignment_extendAssignment]
  exact generatedHolds taggedClause.1
    (List.fst_mem_of_mem_zipIdx taggedMem)

/-- Any satisfying assignment of a positioned Figure 9 gadget restricts to
a satisfying assignment of its source disjunction. -/
theorem clauseGadget_sound {Variable : Type*}
    (assignment : OneInThreeVariable Variable → Bool)
    (clauseIndex : Nat) (source : EmbeddedClause Variable)
    (width : source.literals.length ≤ 3)
    (targetHolds :
      FormulaHolds assignment (clauseGadget clauseIndex source)) :
    PlanarThreeSAT.ClauseHolds
      (restrictAssignment assignment) source := by
  have periodicWidth :
      (zeroOffsetClause source).WidthAtMost 3 := by
    simpa [zeroOffsetClause, PeriodicClause.WidthAtMost] using width
  have generatedHolds :
      ∀ clause ∈
          PeriodicOneInThree.clauseClauses
            clauseIndex (zeroOffsetClause source),
        PeriodicOneInThree.ClauseHolds
          (constantAssignment assignment) (0, 0) clause := by
    intro clause clauseMem
    have mappedMem :
        clause ∈
          (PeriodicOneInThree.clauseClauses
            clauseIndex (zeroOffsetClause source)).zipIdx.map
              Prod.fst := by
      simpa only [List.zipIdx_map_fst] using clauseMem
    rcases List.mem_map.mp mappedMem with
      ⟨taggedClause, taggedMem, clauseEq⟩
    rcases taggedClause with ⟨generatedClause, generatedIndex⟩
    change generatedClause = clause at clauseEq
    subst clause
    apply
      (embedGeneratedClause_holds_iff assignment
        (generatedClausePosition source.position generatedIndex)
        generatedClause).mp
    apply targetHolds
    exact List.mem_map.mpr
      ⟨(generatedClause, generatedIndex), taggedMem, rfl⟩
  have sourcePeriodicHolds :=
    PeriodicOneInThree.clauseClauses_sound
      (constantAssignment assignment) (0, 0)
      clauseIndex (zeroOffsetClause source)
      periodicWidth generatedHolds
  apply (zeroOffsetClause_holds_iff
    (restrictAssignment assignment) source).mp
  rw [← periodic_restrict_constantAssignment]
  exact sourcePeriodicHolds

/-- A satisfying assignment of a width-three embedded formula extends
simultaneously through every clause-local Figure 9 gadget. -/
theorem formula_complete {Variable : Type*}
    (source : List (EmbeddedClause Variable))
    (width :
      ∀ clause ∈ source, clause.literals.length ≤ 3)
    (assignment : Variable → Bool)
    (sourceHolds :
      PlanarThreeSAT.FormulaHolds assignment source) :
    FormulaHolds (extendAssignment assignment) (formula source) := by
  intro targetClause targetMem
  rcases List.mem_flatMap.mp targetMem with
    ⟨taggedSource, taggedSourceMem, targetMem⟩
  exact clauseGadget_complete assignment
    taggedSource.2 taggedSource.1
    (width taggedSource.1
      (List.fst_mem_of_mem_zipIdx taggedSourceMem))
    (sourceHolds taggedSource.1
      (List.fst_mem_of_mem_zipIdx taggedSourceMem))
    targetClause targetMem

/-- Restricting any satisfying assignment of the complete positioned
exact-one formula satisfies every original disjunction. -/
theorem formula_sound {Variable : Type*}
    (source : List (EmbeddedClause Variable))
    (width :
      ∀ clause ∈ source, clause.literals.length ≤ 3)
    (assignment : OneInThreeVariable Variable → Bool)
    (targetHolds : FormulaHolds assignment (formula source)) :
    PlanarThreeSAT.FormulaHolds
      (restrictAssignment assignment) source := by
  intro sourceClause sourceMem
  have mappedMem :
      sourceClause ∈ source.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using sourceMem
  rcases List.mem_map.mp mappedMem with
    ⟨taggedSource, taggedSourceMem, sourceEq⟩
  rcases taggedSource with ⟨taggedClause, clauseIndex⟩
  change taggedClause = sourceClause at sourceEq
  subst sourceClause
  apply clauseGadget_sound assignment clauseIndex taggedClause
    (width taggedClause
      (List.fst_mem_of_mem_zipIdx taggedSourceMem))
  intro targetClause targetMem
  exact targetHolds targetClause
    (List.mem_flatMap.mpr
      ⟨(taggedClause, clauseIndex), taggedSourceMem, targetMem⟩)

/-- Exact satisfiability preservation for the positioned planar Figure 9
replacement. -/
theorem satisfiable_iff {Variable : Type*}
    (source : List (EmbeddedClause Variable))
    (width :
      ∀ clause ∈ source, clause.literals.length ≤ 3) :
    SourceSatisfiable source ↔ Satisfiable (formula source) := by
  constructor
  · rintro ⟨assignment, sourceHolds⟩
    exact
      ⟨extendAssignment assignment,
        formula_complete source width assignment sourceHolds⟩
  · rintro ⟨assignment, targetHolds⟩
    exact
      ⟨restrictAssignment assignment,
        formula_sound source width assignment targetHolds⟩

end PlanarOneInThree
end LeanTrominoes
