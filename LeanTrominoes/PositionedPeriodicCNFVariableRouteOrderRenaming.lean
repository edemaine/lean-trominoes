import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanRouteOrder
import LeanTrominoes.PeriodicCNFPlanarThreeSATThreePositioned

/-!
# Variable route order under injective renaming

Position-preserving wrappers change literal atoms but leave every clause and
literal presentation index unchanged.  This file records the corresponding
transport of tagged occurrences and of clockwise variable-route order.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Apply a variable renaming to a tagged literal occurrence while retaining
its presentation indices. -/
def renameTaggedOccurrence
    {Source Target : Type*}
    (variableMap : Source → Target)
    (tagged :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence Source) :
    PeriodicOneInThreeToThreeDM.TaggedOccurrence Target :=
  (⟨variableMap tagged.1.atom,
      tagged.1.offset, tagged.1.value⟩,
    tagged.2.1, tagged.2.2)

/-- A target incidence of a renamed formula comes from the source incidence
at the same clause and literal presentation indices. -/
theorem exists_incidence_of_rename_members
    {Source Target : Type*}
    (source : PositionedPeriodicCNF Source)
    (variableMap : Source → Target)
    {targetClause : PositionedPeriodicClause Target}
    {clauseIndex : Nat}
    (targetClauseMember :
      (targetClause, clauseIndex) ∈
        (source.rename variableMap).clauses.zipIdx)
    {targetLiteral : PeriodicLiteral Target}
    {literalIndex : Nat}
    (targetLiteralMember :
      (targetLiteral, literalIndex) ∈
        targetClause.literals.zipIdx) :
    ∃ sourceClause sourceLiteral,
      (sourceClause, clauseIndex) ∈ source.clauses.zipIdx ∧
        (sourceLiteral, literalIndex) ∈
          sourceClause.literals.zipIdx ∧
        targetLiteral.atom = variableMap sourceLiteral.atom := by
  change
    (targetClause, clauseIndex) ∈
      (source.clauses.map fun clause =>
        ⟨clause.position, clause.literals.map fun literal =>
          ⟨variableMap literal.atom,
            literal.offset, literal.value⟩⟩).zipIdx
    at targetClauseMember
  rw [List.zipIdx_map] at targetClauseMember
  rcases List.mem_map.mp targetClauseMember with
    ⟨taggedSourceClause, taggedSourceClauseMember,
      targetClauseEqual⟩
  have clauseIndexEqual :
      taggedSourceClause.2 = clauseIndex :=
    congrArg Prod.snd targetClauseEqual
  have targetClauseValueEqual :
      targetClause =
        ⟨taggedSourceClause.1.position,
          taggedSourceClause.1.literals.map fun literal =>
            ⟨variableMap literal.atom,
              literal.offset, literal.value⟩⟩ := by
    exact (congrArg Prod.fst targetClauseEqual).symm
  subst clauseIndex
  subst targetClause
  change
    (targetLiteral, literalIndex) ∈
      (taggedSourceClause.1.literals.map fun literal =>
        ⟨variableMap literal.atom,
          literal.offset, literal.value⟩).zipIdx
    at targetLiteralMember
  rw [List.zipIdx_map] at targetLiteralMember
  rcases List.mem_map.mp targetLiteralMember with
    ⟨taggedSourceLiteral, taggedSourceLiteralMember,
      targetLiteralEqual⟩
  have literalIndexEqual :
      taggedSourceLiteral.2 = literalIndex :=
    congrArg Prod.snd targetLiteralEqual
  have targetLiteralAtomEqual :
      targetLiteral.atom =
        variableMap taggedSourceLiteral.1.atom := by
    exact congrArg (fun tagged => tagged.1.atom) targetLiteralEqual.symm
  subst literalIndex
  exact
    ⟨taggedSourceClause.1, taggedSourceLiteral.1,
      taggedSourceClauseMember, taggedSourceLiteralMember,
      targetLiteralAtomEqual⟩

/-- Renaming a positioned formula maps its tagged occurrence list pointwise
without changing presentation order. -/
theorem taggedLiterals_rename
    {Source Target : Type*}
    (source : PositionedPeriodicCNF Source)
    (variableMap : Source → Target) :
    PeriodicThreeSATThree.taggedLiterals
        (source.rename variableMap).erase =
      (PeriodicThreeSATThree.taggedLiterals source.erase).map
        (renameTaggedOccurrence variableMap) := by
  unfold PeriodicThreeSATThree.taggedLiterals
    PositionedPeriodicCNF.rename PositionedPeriodicCNF.erase
  rw [List.zipIdx_map, List.zipIdx_map,
    List.flatMap_map, List.flatMap_map, List.map_flatMap]
  simp only [Prod.map, id_eq]
  rw [List.zipIdx_map]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro taggedClause _taggedClauseMember
  rcases taggedClause with ⟨clause, clauseIndex⟩
  rw [List.zipIdx_map]
  simp [renameTaggedOccurrence, List.map_map,
    Function.comp_def]

/-- Injective renaming maps the ordered occurrence list of a source atom
pointwise. -/
theorem occurrencesOf_rename
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (source : PositionedPeriodicCNF Source)
    (variableMap : Source → Target)
    (injective : Function.Injective variableMap)
    (atom : Source) :
    PeriodicOneInThreeToThreeDM.occurrencesOf
        (source.rename variableMap).erase (variableMap atom) =
      (PeriodicOneInThreeToThreeDM.occurrencesOf
        source.erase atom).map
          (renameTaggedOccurrence variableMap) := by
  unfold PeriodicOneInThreeToThreeDM.occurrencesOf
  rw [taggedLiterals_rename]
  induction PeriodicThreeSATThree.taggedLiterals source.erase with
  | nil =>
      rfl
  | cons tagged rest induction =>
      by_cases atomEqual : tagged.1.atom = atom
      · simp [renameTaggedOccurrence, atomEqual, induction]
      · have mappedNotEqual :
            variableMap tagged.1.atom ≠ variableMap atom := by
          exact fun equal => atomEqual (injective equal)
        simp [renameTaggedOccurrence, atomEqual,
          mappedNotEqual, induction]

/-- Injective renaming maps every occupied occurrence slot and retains its
clause/literal indices. -/
theorem occurrenceAt_rename
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (source : PositionedPeriodicCNF Source)
    (variableMap : Source → Target)
    (injective : Function.Injective variableMap)
    (atom : Source)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot) :
    PeriodicOneInThreeToThreeDM.occurrenceAt
        (source.rename variableMap).erase
        (variableMap atom) slot =
      (PeriodicOneInThreeToThreeDM.occurrenceAt
        source.erase atom slot).map
          (renameTaggedOccurrence variableMap) := by
  unfold PeriodicOneInThreeToThreeDM.occurrenceAt
  rw [occurrencesOf_rename source variableMap injective atom]
  simp

/-- A bijective variable renaming preserves clockwise variable-route order
when the route family is indexed by the unchanged presentation positions. -/
theorem variableRoutesInOccurrenceOrder_rename
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (source : PositionedPeriodicCNF Source)
    (routes : IncidenceRoutes)
    (variableMap : Source → Target)
    (variableInverse : Target → Source)
    (leftInverse :
      Function.LeftInverse variableInverse variableMap)
    (rightInverse :
      Function.RightInverse variableInverse variableMap)
    (ordered : source.VariableRoutesInOccurrenceOrder routes) :
    (source.rename variableMap).VariableRoutesInOccurrenceOrder
      routes := by
  intro targetAtom first second third
    firstLookup secondLookup thirdLookup
  have injective : Function.Injective variableMap :=
    leftInverse.injective
  change
    PeriodicOneInThreeToThreeDM.occurrenceAt
        (source.rename variableMap).erase targetAtom .first =
      some first at firstLookup
  change
    PeriodicOneInThreeToThreeDM.occurrenceAt
        (source.rename variableMap).erase targetAtom .second =
      some second at secondLookup
  change
    PeriodicOneInThreeToThreeDM.occurrenceAt
        (source.rename variableMap).erase targetAtom .third =
      some third at thirdLookup
  rw [← rightInverse targetAtom,
    occurrenceAt_rename source variableMap injective] at firstLookup
  rw [← rightInverse targetAtom,
    occurrenceAt_rename source variableMap injective] at secondLookup
  rw [← rightInverse targetAtom,
    occurrenceAt_rename source variableMap injective] at thirdLookup
  rcases Option.map_eq_some_iff.mp firstLookup with
    ⟨sourceFirst, sourceFirstLookup, rfl⟩
  rcases Option.map_eq_some_iff.mp secondLookup with
    ⟨sourceSecond, sourceSecondLookup, rfl⟩
  rcases Option.map_eq_some_iff.mp thirdLookup with
    ⟨sourceThird, sourceThirdLookup, rfl⟩
  simpa [renameTaggedOccurrence] using
    ordered (variableInverse targetAtom)
      sourceFirst sourceSecond sourceThird
      sourceFirstLookup sourceSecondLookup sourceThirdLookup

end PositionedPeriodicCNF
end LeanTrominoes
