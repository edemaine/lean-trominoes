import LeanTrominoes.RetainedAngularTerminalGateDistinctness
import LeanTrominoes.RetainedTerminalDirectionEnumeration
import Mathlib.Data.Fintype.Pi

/-!
# Finite shapes of retained angular terminal profiles

Concrete retained terminal lengths are unbounded, but an annular adapter
only needs three finite facts about them:

* which of the eight Figure 7 slots are active;
* the retained direction at each active slot; and
* for two gates on the same ray, which one is radially closer.

`RetainedAngularTerminalShape` records exactly that information in eight
fixed slots.  It is a finite type, so later executable geometry can search
all possible local inputs.  The extraction theorems below recover the exact
direction and strict radial comparison of every active pair, and show that
positive uniform refinement leaves the shape unchanged.  The angular sort's
radial tie-break further guarantees that slot order and radial order agree
inside every equal-direction block.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- One of the eight consecutive boundary slots in the Figure 7 fan. -/
abbrev RetainedTerminalSlot := Fin 8

/-- Finite data controlling one local annular adapter.

Inactive slots contain `none`.  `radialLT first second` is meaningful for
active slots of equal direction and says that the first gate is closer to
the variable center than the second. -/
@[ext]
structure RetainedAngularTerminalShape where
  direction :
    RetainedTerminalSlot →
      Option RetainedTerminalDirection
  radialLT :
    RetainedTerminalSlot →
      RetainedTerminalSlot → Bool
  deriving DecidableEq, Fintype

/-- Extract the bounded adapter shape from a concrete length-aware profile. -/
def RetainedAngularTerminalProfile.finiteShape
    (profile : RetainedAngularTerminalProfile) :
    RetainedAngularTerminalShape where
  direction := fun slot =>
    (profile.terminals[slot.val]?).map Prod.fst
  radialLT := fun first second =>
    match profile.terminals[first.val]?,
        profile.terminals[second.val]? with
    | some firstTerminal, some secondTerminal =>
        decide
          (firstTerminal.1 = secondTerminal.1 ∧
            firstTerminal.2 < secondTerminal.2)
    | _, _ => false

/-- An active slot exposes exactly the concrete terminal direction at that
list index. -/
theorem RetainedAngularTerminalProfile.finiteShape_direction_of_lt
    (profile : RetainedAngularTerminalProfile)
    (slot : RetainedTerminalSlot)
    (slotLt : slot.val < profile.terminals.length) :
    profile.finiteShape.direction slot =
      some (profile.terminals[slot.val]'slotLt).1 := by
  simp [finiteShape, List.getElem?_eq_getElem slotLt]

/-- A slot beyond the concrete terminal list is inactive. -/
theorem RetainedAngularTerminalProfile.finiteShape_direction_of_ge
    (profile : RetainedAngularTerminalProfile)
    (slot : RetainedTerminalSlot)
    (slotGe : profile.terminals.length ≤ slot.val) :
    profile.finiteShape.direction slot = none := by
  simp [finiteShape,
    List.getElem?_eq_none_iff.mpr slotGe]

/-- On active slots, the finite radial bit is precisely strict comparison of
the concrete lengths, restricted to a common retained direction. -/
theorem RetainedAngularTerminalProfile.finiteShape_radialLT_of_lt
    (profile : RetainedAngularTerminalProfile)
    (first second : RetainedTerminalSlot)
    (firstLt : first.val < profile.terminals.length)
    (secondLt : second.val < profile.terminals.length) :
    profile.finiteShape.radialLT first second =
      decide
        ((profile.terminals[first.val]'firstLt).1 =
            (profile.terminals[second.val]'secondLt).1 ∧
          (profile.terminals[first.val]'firstLt).2 <
            (profile.terminals[second.val]'secondLt).2) := by
  simp [finiteShape,
    List.getElem?_eq_getElem firstLt,
    List.getElem?_eq_getElem secondLt]

/-- A finite shape marks exactly the initial slots occupied by the concrete
terminal list. -/
theorem RetainedAngularTerminalProfile.finiteShape_direction_isSome_iff
    (profile : RetainedAngularTerminalProfile)
    (slot : RetainedTerminalSlot) :
    (profile.finiteShape.direction slot).isSome ↔
      slot.val < profile.terminals.length := by
  by_cases slotLt : slot.val < profile.terminals.length
  · rw [profile.finiteShape_direction_of_lt slot slotLt]
    simp [slotLt]
  · have slotGe :
        profile.terminals.length ≤ slot.val :=
      Nat.le_of_not_gt slotLt
    rw [profile.finiteShape_direction_of_ge slot slotGe]
    simp [slotLt]

/-- A true radial bit has exactly the two active indices, common direction,
and strict concrete length inequality advertised by the shape. -/
theorem RetainedAngularTerminalProfile.finiteShape_radialLT_eq_true_iff
    (profile : RetainedAngularTerminalProfile)
    (first second : RetainedTerminalSlot) :
    profile.finiteShape.radialLT first second = true ↔
      ∃ (firstLt :
          first.val < profile.terminals.length)
        (secondLt :
          second.val < profile.terminals.length),
        (profile.terminals[first.val]'firstLt).1 =
            (profile.terminals[second.val]'secondLt).1 ∧
          (profile.terminals[first.val]'firstLt).2 <
            (profile.terminals[second.val]'secondLt).2 := by
  by_cases firstLt : first.val < profile.terminals.length
  · by_cases secondLt : second.val < profile.terminals.length
    · rw [profile.finiteShape_radialLT_of_lt
        first second firstLt secondLt]
      constructor
      · intro radial
        refine ⟨firstLt, secondLt, ?_⟩
        simpa only [decide_eq_true_eq] using radial
      · rintro ⟨_firstLt, _secondLt, radial⟩
        simpa only [decide_eq_true_eq] using radial
    · simp [finiteShape, secondLt]
  · simp [finiteShape, firstLt]

/-- Positive uniform refinement changes physical radii but not the finite
adapter shape. -/
theorem RetainedAngularTerminalProfile.finiteShape_scale
    (profile : RetainedAngularTerminalProfile)
    (factor : Nat) (factorPositive : 0 < factor) :
    (profile.scale factor factorPositive).finiteShape =
      profile.finiteShape := by
  apply RetainedAngularTerminalShape.ext
  · funext slot
    cases slotLookup :
        profile.terminals[slot.val]? with
    | none =>
        simp [finiteShape,
          RetainedAngularTerminalProfile.scale,
          slotLookup]
    | some terminal =>
        simp [finiteShape,
          RetainedAngularTerminalProfile.scale,
          slotLookup, scaleRetainedTerminalData]
  · funext first second
    cases firstLookup :
        profile.terminals[first.val]? with
    | none =>
        simp [finiteShape,
          RetainedAngularTerminalProfile.scale,
          firstLookup]
    | some firstTerminal =>
        cases secondLookup :
            profile.terminals[second.val]? with
        | none =>
            simp [finiteShape,
              RetainedAngularTerminalProfile.scale,
              firstLookup, secondLookup]
        | some secondTerminal =>
            simp [finiteShape,
              RetainedAngularTerminalProfile.scale,
              firstLookup, secondLookup,
              scaleRetainedTerminalData,
              Nat.mul_lt_mul_left factorPositive]

/-- Distinct active gates on one ray have a strict radial order in one of
the two directions. -/
theorem RetainedAngularTerminalProfile.finiteShape_radialLT_total
    (profile : RetainedAngularTerminalProfile)
    (distinct : profile.GatesDistinct)
    (first second : RetainedTerminalSlot)
    (firstLt : first.val < profile.terminals.length)
    (secondLt : second.val < profile.terminals.length)
    (slotsNe : first ≠ second)
    (directionsEqual :
      (profile.terminals[first.val]'firstLt).1 =
        (profile.terminals[second.val]'secondLt).1) :
    profile.finiteShape.radialLT first second = true ∨
      profile.finiteShape.radialLT second first = true := by
  have terminalsNe :
      profile.terminals[first.val]'firstLt ≠
        profile.terminals[second.val]'secondLt := by
    intro terminalsEqual
    have indicesEqual :
        (⟨first.val, firstLt⟩ :
            Fin profile.terminals.length) =
          ⟨second.val, secondLt⟩ :=
      (List.nodup_iff_injective_getElem.mp distinct)
        terminalsEqual
    apply slotsNe
    have valuesEqual : first.val = second.val :=
      congrArg
        (fun index : Fin profile.terminals.length =>
          index.val)
        indicesEqual
    exact Fin.ext valuesEqual
  have lengthsNe :
      (profile.terminals[first.val]'firstLt).2 ≠
        (profile.terminals[second.val]'secondLt).2 := by
    intro lengthsEqual
    apply terminalsNe
    exact Prod.ext directionsEqual lengthsEqual
  rw [profile.finiteShape_radialLT_of_lt
      first second firstLt secondLt,
    profile.finiteShape_radialLT_of_lt
      second first secondLt firstLt]
  simp only [decide_eq_true_eq, directionsEqual,
    true_and]
  exact Nat.lt_or_gt_of_ne lengthsNe

/-- Whether a fixed shape slot contains a terminal direction. -/
def RetainedAngularTerminalShape.Active
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot) : Prop :=
  (shape.direction slot).isSome

instance (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot) :
    Decidable (shape.Active slot) := by
  unfold RetainedAngularTerminalShape.Active
  infer_instance

/-- Active slots form an initial segment. -/
def RetainedAngularTerminalShape.ActiveInitial
    (shape : RetainedAngularTerminalShape) : Prop :=
  ∀ first second,
    first.val < second.val →
    shape.Active second →
    shape.Active first

instance (shape : RetainedAngularTerminalShape) :
    Decidable shape.ActiveInitial := by
  unfold RetainedAngularTerminalShape.ActiveInitial
  infer_instance

/-- Active directions are nondecreasing in slot order. -/
def RetainedAngularTerminalShape.DirectionsSorted
    (shape : RetainedAngularTerminalShape) : Prop :=
  ∀ first second firstDirection secondDirection,
    first.val < second.val →
    shape.direction first = some firstDirection →
    shape.direction second = some secondDirection →
    firstDirection.angularRank ≤
      secondDirection.angularRank

instance (shape : RetainedAngularTerminalShape) :
    Decidable shape.DirectionsSorted := by
  unfold RetainedAngularTerminalShape.DirectionsSorted
  infer_instance

/-- A radial comparison is supported only between two slots of one retained
direction. -/
def RetainedAngularTerminalShape.RadialSupported
    (shape : RetainedAngularTerminalShape) : Prop :=
  ∀ first second,
    shape.radialLT first second = true →
    ∃ direction,
      shape.direction first = some direction ∧
        shape.direction second = some direction

instance (shape : RetainedAngularTerminalShape) :
    Decidable shape.RadialSupported := by
  unfold RetainedAngularTerminalShape.RadialSupported
  infer_instance

/-- The radial comparison has no reflexive edges. -/
def RetainedAngularTerminalShape.RadialIrreflexive
    (shape : RetainedAngularTerminalShape) : Prop :=
  ∀ slot, shape.radialLT slot slot = false

instance (shape : RetainedAngularTerminalShape) :
    Decidable shape.RadialIrreflexive := by
  unfold RetainedAngularTerminalShape.RadialIrreflexive
  infer_instance

/-- The radial comparison is transitive. -/
def RetainedAngularTerminalShape.RadialTransitive
    (shape : RetainedAngularTerminalShape) : Prop :=
  ∀ first second third,
    shape.radialLT first second = true →
    shape.radialLT second third = true →
    shape.radialLT first third = true

instance (shape : RetainedAngularTerminalShape) :
    Decidable shape.RadialTransitive := by
  unfold RetainedAngularTerminalShape.RadialTransitive
  infer_instance

/-- Distinct active slots on one ray are radially comparable. -/
def RetainedAngularTerminalShape.RadialTotalOnTies
    (shape : RetainedAngularTerminalShape) : Prop :=
  ∀ first second direction,
    shape.direction first = some direction →
    shape.direction second = some direction →
    first ≠ second →
    shape.radialLT first second = true ∨
      shape.radialLT second first = true

instance (shape : RetainedAngularTerminalShape) :
    Decidable shape.RadialTotalOnTies := by
  unfold RetainedAngularTerminalShape.RadialTotalOnTies
  infer_instance

/-- Earlier active slots on one retained ray are closer to the source
endpoint. -/
def RetainedAngularTerminalShape.RadialFollowsSlots
    (shape : RetainedAngularTerminalShape) : Prop :=
  ∀ first second direction,
    first.val < second.val →
    shape.direction first = some direction →
    shape.direction second = some direction →
    shape.radialLT first second = true

instance (shape : RetainedAngularTerminalShape) :
    Decidable shape.RadialFollowsSlots := by
  unfold RetainedAngularTerminalShape.RadialFollowsSlots
  infer_instance

/-- Exact finite invariants obeyed by a shape extracted from a sorted
duplicate-free profile.  Active slots form an initial segment, their
directions are nondecreasing, and `radialLT` is a strict total order inside
each equal-direction block, follows slot order there, and is unsupported
outside such blocks. -/
def RetainedAngularTerminalShape.IsValid
    (shape : RetainedAngularTerminalShape) : Prop :=
  shape.ActiveInitial ∧
    shape.DirectionsSorted ∧
    shape.RadialSupported ∧
    shape.RadialIrreflexive ∧
    shape.RadialTransitive ∧
    shape.RadialTotalOnTies ∧
    shape.RadialFollowsSlots

instance (shape : RetainedAngularTerminalShape) :
    Decidable shape.IsValid := by
  unfold RetainedAngularTerminalShape.IsValid
  infer_instance

/-- Every sorted profile with distinct gates extracts to the finite valid
subset consumed by the annular router. -/
theorem RetainedAngularTerminalProfile.finiteShape_isValid
    (profile : RetainedAngularTerminalProfile)
    (distinct : profile.GatesDistinct) :
    profile.finiteShape.IsValid := by
  unfold RetainedAngularTerminalShape.IsValid
    RetainedAngularTerminalShape.ActiveInitial
    RetainedAngularTerminalShape.DirectionsSorted
    RetainedAngularTerminalShape.RadialSupported
    RetainedAngularTerminalShape.RadialIrreflexive
    RetainedAngularTerminalShape.RadialTransitive
    RetainedAngularTerminalShape.RadialTotalOnTies
    RetainedAngularTerminalShape.RadialFollowsSlots
  constructor
  · intro first second before secondActive
    rw [RetainedAngularTerminalShape.Active,
      profile.finiteShape_direction_isSome_iff] at secondActive ⊢
    omega
  constructor
  · intro first second firstDirection secondDirection before
      firstDirectionEq secondDirectionEq
    have firstActive :
        profile.finiteShape.Active first := by
      rw [RetainedAngularTerminalShape.Active,
        firstDirectionEq]
      simp
    have secondActive :
        profile.finiteShape.Active second := by
      rw [RetainedAngularTerminalShape.Active,
        secondDirectionEq]
      simp
    have firstLt :
        first.val < profile.terminals.length :=
      profile.finiteShape_direction_isSome_iff
        first |>.mp firstActive
    have secondLt :
        second.val < profile.terminals.length :=
      profile.finiteShape_direction_isSome_iff
        second |>.mp secondActive
    have firstConcrete :=
      profile.finiteShape_direction_of_lt first firstLt
    have secondConcrete :=
      profile.finiteShape_direction_of_lt second secondLt
    rw [firstDirectionEq] at firstConcrete
    rw [secondDirectionEq] at secondConcrete
    have firstDirectionConcrete :
        firstDirection =
          (profile.terminals[first.val]'firstLt).1 :=
      Option.some.inj firstConcrete
    have secondDirectionConcrete :
        secondDirection =
          (profile.terminals[second.val]'secondLt).1 :=
      Option.some.inj secondConcrete
    rw [firstDirectionConcrete, secondDirectionConcrete]
    exact
      (List.pairwise_iff_getElem.mp profile.rankSorted)
        first.val second.val firstLt secondLt before
  constructor
  · intro first second radial
    rcases
        (profile.finiteShape_radialLT_eq_true_iff
          first second).mp radial with
      ⟨firstLt, secondLt, directionsEqual, _⟩
    refine
      ⟨(profile.terminals[first.val]'firstLt).1,
        profile.finiteShape_direction_of_lt first firstLt,
        ?_⟩
    rw [profile.finiteShape_direction_of_lt
      second secondLt]
    exact congrArg some directionsEqual.symm
  constructor
  · intro slot
    by_contra radial
    have radialTrue :
        profile.finiteShape.radialLT slot slot = true := by
      exact Bool.eq_true_of_not_eq_false radial
    rcases
        (profile.finiteShape_radialLT_eq_true_iff
          slot slot).mp radialTrue with
      ⟨slotLt, _slotLt, _, lengthLess⟩
    exact (Nat.lt_irrefl
      (profile.terminals[slot.val]'slotLt).2) lengthLess
  constructor
  · intro first second third firstSecond secondThird
    rcases
        (profile.finiteShape_radialLT_eq_true_iff
          first second).mp firstSecond with
      ⟨firstLt, secondLt, firstSecondDirection,
        firstSecondLength⟩
    rcases
        (profile.finiteShape_radialLT_eq_true_iff
          second third).mp secondThird with
      ⟨_secondLt, thirdLt, secondThirdDirection,
        secondThirdLength⟩
    apply
      (profile.finiteShape_radialLT_eq_true_iff
        first third).mpr
    refine
      ⟨firstLt, thirdLt,
        firstSecondDirection.trans secondThirdDirection,
        Nat.lt_trans firstSecondLength secondThirdLength⟩
  constructor
  · intro first second direction firstDirectionEq
      secondDirectionEq slotsNe
    have firstActive :
        profile.finiteShape.Active first := by
      rw [RetainedAngularTerminalShape.Active,
        firstDirectionEq]
      simp
    have secondActive :
        profile.finiteShape.Active second := by
      rw [RetainedAngularTerminalShape.Active,
        secondDirectionEq]
      simp
    have firstLt :
        first.val < profile.terminals.length :=
      profile.finiteShape_direction_isSome_iff
        first |>.mp firstActive
    have secondLt :
        second.val < profile.terminals.length :=
      profile.finiteShape_direction_isSome_iff
        second |>.mp secondActive
    have firstConcrete :=
      profile.finiteShape_direction_of_lt first firstLt
    have secondConcrete :=
      profile.finiteShape_direction_of_lt second secondLt
    rw [firstDirectionEq] at firstConcrete
    rw [secondDirectionEq] at secondConcrete
    apply profile.finiteShape_radialLT_total
      distinct first second firstLt secondLt slotsNe
    exact
      (Option.some.inj firstConcrete).symm.trans
        (Option.some.inj secondConcrete)
  · intro first second direction before firstDirectionEq
      secondDirectionEq
    have firstActive :
        profile.finiteShape.Active first := by
      rw [RetainedAngularTerminalShape.Active,
        firstDirectionEq]
      simp
    have secondActive :
        profile.finiteShape.Active second := by
      rw [RetainedAngularTerminalShape.Active,
        secondDirectionEq]
      simp
    have firstLt :
        first.val < profile.terminals.length :=
      profile.finiteShape_direction_isSome_iff
        first |>.mp firstActive
    have secondLt :
        second.val < profile.terminals.length :=
      profile.finiteShape_direction_isSome_iff
        second |>.mp secondActive
    have firstConcrete :=
      profile.finiteShape_direction_of_lt first firstLt
    have secondConcrete :=
      profile.finiteShape_direction_of_lt second secondLt
    rw [firstDirectionEq] at firstConcrete
    rw [secondDirectionEq] at secondConcrete
    have directionsEqual :
        (profile.terminals[first.val]'firstLt).1 =
          (profile.terminals[second.val]'secondLt).1 :=
      (Option.some.inj firstConcrete).symm.trans
        (Option.some.inj secondConcrete)
    apply
      (profile.finiteShape_radialLT_eq_true_iff
        first second).mpr
    exact
      ⟨firstLt, secondLt, directionsEqual,
        profile.length_lt_of_lt_of_direction_eq
          distinct first.val second.val firstLt secondLt
          before directionsEqual⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
