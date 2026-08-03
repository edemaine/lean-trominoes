import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements

/-!
# Unit elimination under variable renaming

Unit elimination scopes each fresh variable by the index and complete
contents of its source clause.  Consequently a source-variable renaming
must also rename the clause stored in every auxiliary key.  This file
defines that induced map and proves that both the logical and positioned
unit-elimination constructions are natural under it.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnits

/-- Rename one periodic literal without changing its offset or polarity. -/
def renameLiteral {Source Target : Type*}
    (variableMap : Source → Target)
    (literal : PeriodicLiteral Source) :
    PeriodicLiteral Target :=
  ⟨variableMap literal.atom, literal.offset, literal.value⟩

/-- Rename every literal of a periodic clause. -/
def renameClause {Source Target : Type*}
    (variableMap : Source → Target)
    (clause : PeriodicClause Source) :
    PeriodicClause Target :=
  clause.map (renameLiteral variableMap)

/-- Renaming source atoms induces a renaming of unit-elimination atoms;
the source clause retained in an auxiliary key is renamed as well. -/
def renameVariable {Source Target : Type*}
    (variableMap : Source → Target) :
    OneInThreeNoUnitVariable Source →
      OneInThreeNoUnitVariable Target
  | .inl atom => .inl (variableMap atom)
  | .inr ((clauseIndex, clause), kind) =>
      .inr
        ((clauseIndex, renameClause variableMap clause), kind)

@[simp]
theorem renameLiteral_atom
    {Source Target : Type*}
    (variableMap : Source → Target)
    (literal : PeriodicLiteral Source) :
    (renameLiteral variableMap literal).atom =
      variableMap literal.atom := by
  rfl

@[simp]
theorem renameLiteral_offset
    {Source Target : Type*}
    (variableMap : Source → Target)
    (literal : PeriodicLiteral Source) :
    (renameLiteral variableMap literal).offset = literal.offset := by
  rfl

@[simp]
theorem renameLiteral_value
    {Source Target : Type*}
    (variableMap : Source → Target)
    (literal : PeriodicLiteral Source) :
    (renameLiteral variableMap literal).value = literal.value := by
  rfl

@[simp]
theorem anchor_renameClause
    {Source Target : Type*}
    (variableMap : Source → Target)
    (clause : PeriodicClause Source) :
    PeriodicOneInThree.anchor (renameClause variableMap clause) =
      PeriodicOneInThree.anchor clause := by
  cases clause <;> rfl

/-- Renaming a whole generated block is the same as first renaming its
source clause and then applying unit elimination. -/
theorem clauseClauses_rename
    {Source Target : Type*}
    (variableMap : Source → Target)
    (clauseIndex : Nat)
    (source : PeriodicClause Source) :
    (clauseClauses clauseIndex source).map
        (renameClause (renameVariable variableMap)) =
      clauseClauses clauseIndex
        (renameClause variableMap source) := by
  cases source with
  | nil =>
      simp [clauseClauses, renameClause, renameLiteral,
        renameVariable, auxiliary, PeriodicOneInThree.anchor]
  | cons first rest =>
      cases rest with
      | nil =>
          simp [clauseClauses, renameClause, renameLiteral,
            renameVariable, auxiliary, liftLiteral,
            PeriodicOneInThree.negate,
            PeriodicOneInThree.anchor]
      | cons second tail =>
          simp [clauseClauses, renameClause, renameLiteral,
            renameVariable, liftLiteral,
            List.map_map, Function.comp_def]

end PeriodicOneInThreeNoUnits

namespace PeriodicOneInThreeNoUnitsPositioned

/-- A positioned source clause renamed without changing its vertex. -/
def renameSourceClause {Source Target : Type*}
    (variableMap : Source → Target)
    (source : PositionedPeriodicClause Source) :
    PositionedPeriodicClause Target :=
  ⟨source.position,
    PeriodicOneInThreeNoUnits.renameClause
      variableMap source.literals⟩

@[simp]
theorem generatedClausePosition_renameSourceClause
    {Source Target : Type*}
    (variableMap : Source → Target)
    (source : PositionedPeriodicClause Source)
    (generatedIndex : Nat) :
    generatedClausePosition
        (renameSourceClause variableMap source) generatedIndex =
      generatedClausePosition source generatedIndex := by
  rcases source with ⟨position, literals⟩
  cases literals with
  | nil =>
      cases generatedIndex <;> rfl
  | cons first rest =>
      cases rest with
      | nil =>
          cases generatedIndex <;> rfl
      | cons second tail => rfl

/-- Renaming a positioned unit-elimination block commutes with building
that block from its renamed source clause. -/
theorem clauseGadget_rename
    {Source Target : Type*}
    (variableMap : Source → Target)
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Source) :
    (clauseGadget clauseIndex source).map
        (renameSourceClause
          (PeriodicOneInThreeNoUnits.renameVariable variableMap)) =
      clauseGadget clauseIndex
        (renameSourceClause variableMap source) := by
  have positionEq :
      ∀ generatedIndex,
        generatedClausePosition source generatedIndex =
          generatedClausePosition
            (renameSourceClause variableMap source)
            generatedIndex :=
    fun generatedIndex =>
      (generatedClausePosition_renameSourceClause
        variableMap source generatedIndex).symm
  unfold clauseGadget
  simp only [renameSourceClause] at positionEq ⊢
  rw [
    ← PeriodicOneInThreeNoUnits.clauseClauses_rename
      variableMap clauseIndex source.literals]
  rw [List.zipIdx_map]
  simp [renameSourceClause, List.map_map, Function.comp_def,
    positionEq]

/-- Positioned unit elimination commutes exactly with the induced variable
renaming. -/
theorem formula_rename
    {Source Target : Type*}
    (variableMap : Source → Target)
    (source : PositionedPeriodicCNF Source) :
    (formula source).rename
        (PeriodicOneInThreeNoUnits.renameVariable variableMap) =
      formula (source.rename variableMap) := by
  cases source with
  | mk clauses =>
      simp only [formula, PositionedPeriodicCNF.rename,
        List.zipIdx_map]
      congr 1
      rw [List.map_flatMap, List.flatMap_map]
      apply List.flatMap_congr
      intro taggedClause taggedClauseMember
      change
        (clauseGadget taggedClause.2 taggedClause.1).map
            (renameSourceClause
              (PeriodicOneInThreeNoUnits.renameVariable variableMap)) =
          clauseGadget taggedClause.2
            (renameSourceClause variableMap taggedClause.1)
      exact
        clauseGadget_rename
          variableMap taggedClause.2 taggedClause.1

@[simp]
theorem clausePosition_rename
    {Source Target : Type*}
    (variableMap : Source → Target)
    (source : PositionedPeriodicCNF Source)
    (clauseIndex : Nat) :
    (source.rename variableMap).clausePosition clauseIndex =
      source.clausePosition clauseIndex := by
  simp [PositionedPeriodicCNF.clausePosition,
    PositionedPeriodicCNF.rename, Function.comp_def]

/-- The induced unit-elimination placements have the same physical period
whenever their source placements do. -/
theorem placement_period_rename
    {Source Target : Type*}
    (variableMap : Source → Target)
    (source : PositionedPeriodicCNF Source)
    (sourcePlacement : PeriodicVariablePlacement Source)
    (targetPlacement : PeriodicVariablePlacement Target)
    (periodsMatch :
      targetPlacement.period = sourcePlacement.period) :
    (placement
        (source.rename variableMap) targetPlacement).period =
      (placement source sourcePlacement).period := by
  simp [placement, periodsMatch]

/-- The induced unit-elimination placement preserves every renamed
variable position when the source placement does. -/
theorem placement_position_rename
    {Source Target : Type*}
    (variableMap : Source → Target)
    (source : PositionedPeriodicCNF Source)
    (sourcePlacement : PeriodicVariablePlacement Source)
    (targetPlacement : PeriodicVariablePlacement Target)
    (positionsMatch :
      ∀ atom,
        targetPlacement.position (variableMap atom) =
          sourcePlacement.position atom)
    (periodsMatch :
      targetPlacement.period = sourcePlacement.period)
    (atom : OneInThreeNoUnitVariable Source) :
    (placement
        (source.rename variableMap) targetPlacement).position
        (PeriodicOneInThreeNoUnits.renameVariable
          variableMap atom) =
      (placement source sourcePlacement).position atom := by
  cases atom with
  | inl sourceAtom =>
      simp [placement,
        PeriodicOneInThreeNoUnits.renameVariable,
        positionsMatch]
  | inr auxiliary =>
      rcases auxiliary with ⟨⟨clauseIndex, clause⟩, kind⟩
      simp [placement,
        PeriodicOneInThreeNoUnits.renameVariable,
        auxiliaryOccurrencePosition,
        periodsMatch]

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
