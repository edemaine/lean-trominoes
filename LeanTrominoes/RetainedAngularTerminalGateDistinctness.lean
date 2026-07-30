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
open PeriodicThreeSATThree

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

/-! ## Obtaining gate distinctness from source terminal vectors -/

/-- Membership in a per-atom occurrence list is membership in the complete
occurrence list together with the expected source atom. -/
theorem mem_occurrenceVariables_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable) :
    copy ∈ occurrenceVariables source atom ↔
      copy ∈ allOccurrenceVariables source ∧ copy.1 = atom := by
  rw [occurrenceVariables_eq_filter]
  simp

/-- Source-level geometric condition sufficient for gate separation:
genuine occurrences of one variable have different backwards terminal
vectors.  The occurrence copies themselves retain their clause/literal
presentation indices, so this condition remains meaningful when a clause
contains syntactically equal literals. -/
def RetainedOccurrenceTerminalVectorsInjective
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : Prop :=
  ∀ first,
    first ∈ allOccurrenceVariables source →
      ∀ second,
        second ∈ allOccurrenceVariables source →
          first.1 = second.1 →
          occurrenceTerminalVector routes first =
              occurrenceTerminalVector routes second →
            first = second

/-- On a retained ray, the total length-aware classifier reconstructs the
original terminal vector exactly. -/
theorem retainedTerminalVector_eq_scale_classifiedRetainedTerminalData
    {vector : Cell}
    (retained : RetainedTerminalRayVector vector) :
    vector =
      Cell.scale
        (classifiedRetainedTerminalData vector).2
        (classifiedRetainedTerminalData vector).1.primitive := by
  have classifiedSome :
      (retainedTerminalDirectionClassify vector).isSome :=
    (retainedTerminalDirectionClassify_isSome_iff vector).2
      retained
  rcases Option.isSome_iff_exists.mp classifiedSome with
    ⟨terminal, classified⟩
  have dataEq :
      classifiedRetainedTerminalData vector = terminal :=
    classifiedRetainedTerminalData_eq_of_classified
      classified
  rw [dataEq]
  exact (retainedTerminalDirectionClassify_sound classified).2

/-- Injectivity of the actual terminal vectors transfers to the total
length-aware terminal classifier on genuine occurrences. -/
theorem classifiedRetainedTerminalData_injective_on_occurrences
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (retained :
      RetainedOccurrenceTerminalCertificate source routes)
    (vectorsInjective :
      RetainedOccurrenceTerminalVectorsInjective source routes)
    (atom : Variable)
    {first second : ThreeOccurrenceVariable Variable}
    (firstMember : first ∈ occurrenceVariables source atom)
    (secondMember : second ∈ occurrenceVariables source atom)
    (dataEqual :
      classifiedRetainedTerminalData
          (occurrenceTerminalVector routes first) =
        classifiedRetainedTerminalData
          (occurrenceTerminalVector routes second)) :
    first = second := by
  apply vectorsInjective
    first
    ((mem_occurrenceVariables_iff
      source atom first).mp firstMember).1
    second
    ((mem_occurrenceVariables_iff
      source atom second).mp secondMember).1
  · exact
      ((mem_occurrenceVariables_iff
        source atom first).mp firstMember).2.trans
        ((mem_occurrenceVariables_iff
          source atom second).mp secondMember).2.symm
  rw [
    retainedTerminalVector_eq_scale_classifiedRetainedTerminalData
      (retained atom first firstMember),
    retainedTerminalVector_eq_scale_classifiedRetainedTerminalData
      (retained atom second secondMember),
    dataEqual]

/-- Stable angular sorting preserves duplicate-freeness of occurrence
copies. -/
theorem angularOccurrenceVariables_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (angularOccurrenceVariables source routes atom).Nodup := by
  exact
    (angularOccurrenceVariables_perm source routes atom).nodup_iff.mpr
      (occurrenceVariables_nodup source atom)

/-- A retained source with injective same-variable terminal vectors has
duplicate-free length-aware angular terminal data. -/
theorem angularRetainedTerminalData_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (retained :
      RetainedOccurrenceTerminalCertificate source routes)
    (vectorsInjective :
      RetainedOccurrenceTerminalVectorsInjective source routes)
    (atom : Variable) :
    (angularRetainedTerminalData source routes atom).Nodup := by
  unfold angularRetainedTerminalData
  apply (angularOccurrenceVariables_nodup source routes atom).map_on
  intro first firstMember second secondMember dataEqual
  apply classifiedRetainedTerminalData_injective_on_occurrences
    source routes retained vectorsInjective atom
  · exact
      (angularOccurrenceVariables_perm
        source routes atom).mem_iff.mp firstMember
  · exact
      (angularOccurrenceVariables_perm
        source routes atom).mem_iff.mp secondMember
  · exact dataEqual

/-- The generic length-aware profile constructor inherits gate
distinctness from source terminal-vector injectivity. -/
theorem retainedAngularTerminalProfile_gatesDistinct
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (retained :
      RetainedOccurrenceTerminalCertificate source routes)
    (vectorsInjective :
      RetainedOccurrenceTerminalVectorsInjective source routes)
    (fits :
      FitsEightSlots
        (angularOccurrenceOrder source routes))
    (atom : Variable) :
    (retainedAngularTerminalProfile
      source routes retained fits atom).GatesDistinct := by
  exact angularRetainedTerminalData_nodup
    source routes retained vectorsInjective atom

end PeriodicEightOccurrenceSplit
end LeanTrominoes
