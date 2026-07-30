import LeanTrominoes.RetainedAngularTerminalDataScaling

/-!
# Distinct retained angular terminal gates

Stable angular ties retain several incidences on one ray, so direction
distinctness is deliberately too strong for the Figure 7 adapter.  The
correct finite condition is that the full `(direction, length)` terminal
data are duplicate-free.

This file proves that positive retained terminal data are represented
injectively by their radial splice points.  Consequently duplicate-free
terminal data are exactly duplicate-free centered gate coordinates, and
positive uniform refinement preserves the condition.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

/-- Positive retained direction/length pairs have distinct displacement
vectors.  The finite proof also covers the three noncompass retained
clause-ray directions. -/
theorem retainedTerminalData_eq_of_scale_primitive_eq
    {first second : RetainedTerminalData}
    (firstPositive : 0 < first.2)
    (secondPositive : 0 < second.2)
    (equal :
      Cell.scale first.2 first.1.primitive =
        Cell.scale second.2 second.1.primitive) :
    first = second := by
  rcases first with ⟨firstDirection, firstLength⟩
  rcases second with ⟨secondDirection, secondLength⟩
  cases firstDirection with
  | compass firstPort =>
      cases firstPort <;>
        cases secondDirection with
        | compass secondPort =>
            cases secondPort <;>
              simp [RetainedTerminalDirection.primitive,
                Port.unitVector, Cell.scale] at equal ⊢ <;>
              omega
        | routedClause secondArm =>
            cases secondArm <;>
              simp [RetainedTerminalDirection.primitive,
                Port.unitVector, routedClauseRayPrimitive, Cell.sub,
                Cell.scale] at equal ⊢ <;>
              omega
  | routedClause firstArm =>
      cases firstArm <;>
        cases secondDirection with
        | compass secondPort =>
            cases secondPort <;>
              simp [RetainedTerminalDirection.primitive,
                Port.unitVector, routedClauseRayPrimitive,
                Cell.sub, Cell.scale] at equal ⊢ <;>
              omega
        | routedClause secondArm =>
            cases secondArm <;>
              simp [RetainedTerminalDirection.primitive,
                routedClauseRayPrimitive, Cell.sub,
                Cell.scale] at equal ⊢ <;>
              omega

/-- At a fixed target, positive retained terminal data have distinct radial
splice points. -/
theorem retainedTerminalSplicePoint_injective_of_positive
    (target : Cell)
    {first second : RetainedTerminalData}
    (firstPositive : 0 < first.2)
    (secondPositive : 0 < second.2)
    (equal :
      retainedTerminalSplicePoint target first =
        retainedTerminalSplicePoint target second) :
    first = second := by
  apply retainedTerminalData_eq_of_scale_primitive_eq
    firstPositive secondPositive
  rcases target with ⟨targetX, targetY⟩
  exact Prod.ext
    (by
      have horizontal := congrArg Prod.fst equal
      simpa [retainedTerminalSplicePoint,
        Cell.add, Cell.scale] using horizontal)
    (by
      have vertical := congrArg Prod.snd equal
      simpa [retainedTerminalSplicePoint,
        Cell.add, Cell.scale] using vertical)

/-- Mapping positive retained terminal data to radial splice points preserves
and reflects duplicate-freeness. -/
theorem retainedTerminalSplicePoints_nodup_iff
    (target : Cell)
    (terminals : List RetainedTerminalData)
    (positive :
      ∀ terminal ∈ terminals, 0 < terminal.2) :
    (terminals.map
        (retainedTerminalSplicePoint target)).Nodup ↔
      terminals.Nodup := by
  constructor
  · intro pointsNodup
    exact pointsNodup.of_map
      (retainedTerminalSplicePoint target)
  · intro terminalsNodup
    apply terminalsNodup.map_on
    intro first firstMember second secondMember equal
    exact retainedTerminalSplicePoint_injective_of_positive
      target
      (positive first firstMember)
      (positive second secondMember)
      equal

/-- The separation condition needed by the annular adapter: stable angular
ties are allowed, but their radial lengths must select different gates. -/
def RetainedAngularTerminalProfile.GatesDistinct
    (profile : RetainedAngularTerminalProfile) : Prop :=
  profile.terminals.Nodup

/-- Gate separation can equivalently be checked on the actual centered
splice-point coordinates. -/
theorem RetainedAngularTerminalProfile.gatesDistinct_iff_splicePoints_nodup
    (profile : RetainedAngularTerminalProfile)
    (target : Cell) :
    profile.GatesDistinct ↔
      (profile.terminals.map
        (retainedTerminalSplicePoint target)).Nodup := by
  rw [retainedTerminalSplicePoints_nodup_iff
    target profile.terminals profile.lengthsPositive]
  rfl

/-- Positive uniform refinement preserves duplicate-free terminal data. -/
theorem RetainedAngularTerminalProfile.scale_gatesDistinct
    (profile : RetainedAngularTerminalProfile)
    (factor : Nat) (factorPositive : 0 < factor)
    (distinct : profile.GatesDistinct) :
    (profile.scale factor factorPositive).GatesDistinct := by
  unfold GatesDistinct at distinct ⊢
  rw [RetainedAngularTerminalProfile.scale_terminals]
  apply distinct.map_on
  intro first firstMember second secondMember equal
  rcases first with ⟨firstDirection, firstLength⟩
  rcases second with ⟨secondDirection, secondLength⟩
  simp only [scaleRetainedTerminalData, Prod.mk.injEq] at equal ⊢
  constructor
  · exact equal.1
  · exact Nat.mul_left_cancel factorPositive equal.2

end PeriodicEightOccurrenceSplit
end LeanTrominoes
