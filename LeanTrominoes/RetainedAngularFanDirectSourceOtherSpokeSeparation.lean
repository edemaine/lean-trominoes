import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoiceSpokePairs

/-!
# Direct source prefixes avoid other spokes at their own center

The existing finite atlas checks prefix--spoke interactions between
different direct incidences of one clause.  Mixed direct/fallback
cross-clause separation also needs the complementary diagonal entry: the
coordinated prefix of one direct incidence must avoid a different occurrence
slot's Figure 7 spoke at the same variable center.

Both objects are finite atlas routes, so all direct clause kinds, atlas
indices, and slot pairs are checked exhaustively.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Every direct atlas prefix avoids every different Figure 7 spoke at the
same local variable center. -/
def RetainedDirectClauseKind.SourceOtherFigure7SpokesSeparated
    (kind : RetainedDirectClauseKind) : Prop :=
  ∀ (index :
      Fin (retainedDirectSourcePrefixChoices kind).length),
    ∀ firstSlot secondSlot : RetainedTerminalSlot,
      firstSlot ≠ secondSlot →
        RoutesStrictlyAvoidEachOther
          (retainedDirectSourceFanCompleteRouteAt
            kind index firstSlot)
          (retainedDirectSourceFigure7SpokeAt
            kind index secondSlot)

instance (kind : RetainedDirectClauseKind) :
    Decidable kind.SourceOtherFigure7SpokesSeparated := by
  unfold
    RetainedDirectClauseKind.SourceOtherFigure7SpokesSeparated
  letI :
      ∀ index :
        Fin (retainedDirectSourcePrefixChoices kind).length,
        Decidable
          (∀ firstSlot secondSlot : RetainedTerminalSlot,
            firstSlot ≠ secondSlot →
              RoutesStrictlyAvoidEachOther
                (retainedDirectSourceFanCompleteRouteAt
                  kind index firstSlot)
                (retainedDirectSourceFigure7SpokeAt
                  kind index secondSlot)) :=
    fun _ => inferInstance
  exact Fintype.decidableForallFintype

/-- Exhaustive certificate for all same-center direct-prefix/other-spoke
interactions. -/
theorem retainedDirectSourceOtherFigure7SpokesSeparated :
    ∀ kind : RetainedDirectClauseKind,
      kind.SourceOtherFigure7SpokesSeparated := by
  native_decide

/-- Pointwise local form of the exhaustive certificate. -/
theorem
    retainedDirectSourceFanCompleteRoute_strictlyAvoid_otherFigure7Spoke
    (kind : RetainedDirectClauseKind)
    (index :
      Fin (retainedDirectSourcePrefixChoices kind).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (slotsDifferent : firstSlot ≠ secondSlot) :
    RoutesStrictlyAvoidEachOther
      (retainedDirectSourceFanCompleteRouteAt
        kind index firstSlot)
      (retainedDirectSourceFigure7SpokeAt
        kind index secondSlot) :=
  retainedDirectSourceOtherFigure7SpokesSeparated
    kind index firstSlot secondSlot slotsDifferent

/-- The same certificate after positioning a checked final choice at its
physical component origin. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoid_otherFigure7Spoke
    (choice : RetainedDirectSourceRouteChoice)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (slotsDifferent : firstSlot ≠ secondSlot) :
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute firstSlot)
      (choice.figure7Spoke secondSlot) := by
  exact
    (retainedDirectSourceFanCompleteRoute_strictlyAvoid_otherFigure7Spoke
      choice.kind choice.index firstSlot secondSlot
      slotsDifferent).map_add
        (retainedDirectSourceFanPositioningOffset choice.origin)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
