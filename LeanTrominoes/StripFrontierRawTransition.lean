import LeanTrominoes.StripFrontierEncoding

/-!
# Raw sparse-frontier transitions

This file expresses the strip-frontier transition predicate without the
input-dependent `WindowState` type.  All quantifiers are replaced by explicit
finite lists, and every assignment lookup goes through the uniform raw word.
For valid raw states, these definitions agree with the semantic frontier
operations exactly.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState

/-- Horizontal phase represented by one column of a raw five-column window.
The two extra periods make the subtraction nontruncating whenever the period
is positive. -/
def columnPhase (periodicStrip : PeriodicStrip) (raw : RawWindowState)
    (column : WindowColumn) : Nat :=
  (raw.phase + column.val + 2 * periodicStrip.period - 2) %
    periodicStrip.period

theorem columnPhase_toWindowState (periodicStrip : PeriodicStrip)
    (raw : RawWindowState) (valid : raw.IsValid periodicStrip)
    (column : WindowColumn) :
    raw.columnPhase periodicStrip column =
      ((raw.toWindowState periodicStrip valid).columnPhase column).val := by
  have periodPositive : 0 < periodicStrip.period :=
    Nat.zero_lt_of_lt valid.1
  unfold columnPhase WindowState.columnPhase shiftPhase toWindowState
  simp only
  rw [← Int.ofNat_inj]
  rw [Int.natCast_emod]
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  rw [Int.ofNat_sub (by omega : 2 ≤
    raw.phase + column.val + 2 * periodicStrip.period)]
  have argumentEq :
      (↑(raw.phase + column.val + 2 * periodicStrip.period) - 2 : Int) =
        ↑raw.phase + column.displacement +
          2 * (periodicStrip.period : Int) := by
    simp [WindowColumn.displacement]
    ring
  norm_num at argumentEq ⊢
  rw [argumentEq, Int.add_emod]
  simp

/-- Raw assignment value at a row of one represented window column. -/
def valueAt (periodicStrip : PeriodicStrip) (raw : RawWindowState)
    (column : WindowColumn) (row : Int) : Option SquareSymmetry :=
  raw.assignmentAtCell periodicStrip column
    ((raw.columnPhase periodicStrip column : Int), row)

theorem assignmentAtCell_eq_none_of_not_mem
    (periodicStrip : PeriodicStrip) (raw : RawWindowState)
    (valid : raw.IsValid periodicStrip)
    (column : WindowColumn) (cell : Cell)
    (notMember : cell ∉ periodicStrip.motif.toFinset) :
    raw.assignmentAtCell periodicStrip column cell = none := by
  letI : BEq (WindowColumn × Cell) := instBEqOfDecidableEq
  unfold assignmentAtCell
  have keyNotMember :
      (column, cell) ∉ assignmentKeys periodicStrip := by
    have notMotif : cell ∉ periodicStrip.motif := by
      simpa using notMember
    simp [assignmentKeys, motifCells, notMotif]
  have indexEq :
      List.idxOf (column, cell) (assignmentKeys periodicStrip) =
        (assignmentKeys periodicStrip).length :=
    List.idxOf_eq_length_iff.mpr keyNotMember
  rw [indexEq, ← valid.2]
  simp

theorem valueAt_toWindowState (periodicStrip : PeriodicStrip)
    (raw : RawWindowState) (valid : raw.IsValid periodicStrip)
    (column : WindowColumn) (row : Int) :
    raw.valueAt periodicStrip column row =
      (raw.toWindowState periodicStrip valid).valueAt column row := by
  unfold valueAt WindowState.valueAt
  rw [columnPhase_toWindowState periodicStrip raw valid column]
  by_cases member :
      ((((raw.toWindowState periodicStrip valid).columnPhase column).val : Int),
        row) ∈
        periodicStrip.motif.toFinset
  · rw [dif_pos member]
    rfl
  · rw [dif_neg member]
    exact assignmentAtCell_eq_none_of_not_mem
      periodicStrip raw valid column _ member

/-- Raw assignment on coordinates relative to the center of the window. -/
def localAssignment (periodicStrip : PeriodicStrip)
    (raw : RawWindowState) : TrominoAssignment :=
  fun offset =>
    match WindowColumn.ofDisplacement? offset.1 with
    | some column => raw.valueAt periodicStrip column offset.2
    | none => none

theorem localAssignment_toWindowState (periodicStrip : PeriodicStrip)
    (raw : RawWindowState) (valid : raw.IsValid periodicStrip) :
    raw.localAssignment periodicStrip =
      (raw.toWindowState periodicStrip valid).localAssignment := by
  funext offset
  unfold localAssignment WindowState.localAssignment
  cases displacement : WindowColumn.ofDisplacement? offset.1 with
  | none => simp
  | some selected =>
      exact valueAt_toWindowState periodicStrip raw valid selected offset.2

/-- Candidate placements covering a center-column target and selected by the
raw local assignment. -/
def activePlacementList (tromino : Tromino)
    (periodicStrip : PeriodicStrip) (raw : RawWindowState) (row : Int) :
    List (Placement Unit) :=
  (TrominoAssignment.coveringPlacementList tromino (0, row)).filter
    fun placement =>
      raw.localAssignment periodicStrip placement.offset =
        some placement.symmetry

/-- Explicit finite-list form of semantic frontier normalization. -/
def IsNormalized (periodicStrip : PeriodicStrip)
    (raw : RawWindowState) : Prop :=
  ∀ column ∈ List.finRange 5, ∀ base ∈ motifCells periodicStrip,
    base.1 = (raw.columnPhase periodicStrip column : Int) ∨
      raw.assignmentAtCell periodicStrip column base = none

/-- Explicit finite-list form of the center-column tiling constraints. -/
def IsCenterValid (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (raw : RawWindowState) : Prop :=
  (∀ base ∈ motifCells periodicStrip,
      base.1 = (raw.phase : Int) →
      ∀ symmetry ∈ TrominoAssignment.squareSymmetryList,
        raw.assignmentAtCell periodicStrip WindowState.center base =
            some symmetry →
          ∀ source ∈ TrominoAssignment.trominoCellList tromino,
            periodicStrip.contains
              (Cell.add ((raw.phase : Int), base.2)
                (symmetry.act source)) = true) ∧
    ∀ base ∈ motifCells periodicStrip,
      base.1 = (raw.phase : Int) →
      (raw.activePlacementList tromino periodicStrip base.2).length = 1

/-- Explicit finite-list form of the phase advance and four-column overlap. -/
def Overlaps (periodicStrip : PeriodicStrip)
    (current next : RawWindowState) : Prop :=
  next.phase = (current.phase + 1) % periodicStrip.period ∧
    ∀ column ∈ List.finRange 4, ∀ base ∈ motifCells periodicStrip,
      current.assignmentAtCell periodicStrip column.succ base =
        next.assignmentAtCell periodicStrip column.castSucc base

/-- A transition between two uniformly encoded sparse frontiers. -/
def Transition (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : RawWindowState) : Prop :=
  current.IsNormalized periodicStrip ∧
    current.IsCenterValid tromino periodicStrip ∧
      current.Overlaps periodicStrip next

/-- Executable normalization check over the canonical key lists. -/
def isNormalizedBool (periodicStrip : PeriodicStrip)
    (raw : RawWindowState) : Bool :=
  (List.finRange 5).all fun column =>
    (motifCells periodicStrip).all fun base =>
      decide (base.1 = (raw.columnPhase periodicStrip column : Int)) ||
        decide (raw.assignmentAtCell periodicStrip column base = none)

/-- Executable center-column constraint check over the canonical finite
candidate lists. -/
def isCenterValidBool (tromino : Tromino)
    (periodicStrip : PeriodicStrip) (raw : RawWindowState) : Bool :=
  ((motifCells periodicStrip).all fun base =>
      decide (base.1 ≠ (raw.phase : Int)) ||
        TrominoAssignment.squareSymmetryList.all fun symmetry =>
          decide (raw.assignmentAtCell periodicStrip WindowState.center base ≠
            some symmetry) ||
            (TrominoAssignment.trominoCellList tromino).all fun source =>
              periodicStrip.contains
                (Cell.add ((raw.phase : Int), base.2)
                  (symmetry.act source))) &&
    ((motifCells periodicStrip).all fun base =>
      decide (base.1 ≠ (raw.phase : Int)) ||
        decide
          ((raw.activePlacementList tromino periodicStrip base.2).length = 1))

/-- Executable phase-advance and shared-column check. -/
def overlapsBool (periodicStrip : PeriodicStrip)
    (current next : RawWindowState) : Bool :=
  decide (next.phase = (current.phase + 1) % periodicStrip.period) &&
    (List.finRange 4).all fun column =>
      (motifCells periodicStrip).all fun base =>
        decide
          (current.assignmentAtCell periodicStrip column.succ base =
            next.assignmentAtCell periodicStrip column.castSucc base)

/-- Executable raw transition check. -/
def transitionBool (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : RawWindowState) : Bool :=
  current.isNormalizedBool periodicStrip &&
    current.isCenterValidBool tromino periodicStrip &&
      current.overlapsBool periodicStrip next

/-- Guarded-disjunction form produced directly by the nested Boolean checks. -/
private def IsCenterValidGuarded (tromino : Tromino)
    (periodicStrip : PeriodicStrip) (raw : RawWindowState) : Prop :=
  (∀ base ∈ motifCells periodicStrip,
      base.1 ≠ (raw.phase : Int) ∨
        ∀ symmetry ∈ TrominoAssignment.squareSymmetryList,
          raw.assignmentAtCell periodicStrip WindowState.center base ≠
              some symmetry ∨
            ∀ source ∈ TrominoAssignment.trominoCellList tromino,
              periodicStrip.contains
                (Cell.add ((raw.phase : Int), base.2)
                  (symmetry.act source)) = true) ∧
    ∀ base ∈ motifCells periodicStrip,
      base.1 ≠ (raw.phase : Int) ∨
        (raw.activePlacementList tromino periodicStrip base.2).length = 1

theorem isNormalizedBool_eq_true_iff (periodicStrip : PeriodicStrip)
    (raw : RawWindowState) :
    raw.isNormalizedBool periodicStrip = true ↔
      raw.IsNormalized periodicStrip := by
  simp [isNormalizedBool, IsNormalized, decide_eq_true_eq]

theorem isCenterValidBool_eq_true_iff (tromino : Tromino)
    (periodicStrip : PeriodicStrip) (raw : RawWindowState) :
    raw.isCenterValidBool tromino periodicStrip = true ↔
      raw.IsCenterValid tromino periodicStrip := by
  have boolIff :
      raw.isCenterValidBool tromino periodicStrip = true ↔
        IsCenterValidGuarded tromino periodicStrip raw := by
    simp [isCenterValidBool, IsCenterValidGuarded, decide_eq_true_eq]
  rw [boolIff]
  unfold IsCenterValidGuarded IsCenterValid
  constructor
  · rintro ⟨inside, covered⟩
    constructor
    · intro base baseMember basePhase symmetry symmetryMember selected
        source sourceMember
      rcases inside base baseMember with phaseMismatch | allSymmetries
      · exact (phaseMismatch basePhase).elim
      rcases allSymmetries symmetry symmetryMember with
        selectionMismatch | allSources
      · exact (selectionMismatch selected).elim
      exact allSources source sourceMember
    · intro base baseMember basePhase
      rcases covered base baseMember with phaseMismatch | oneActive
      · exact (phaseMismatch basePhase).elim
      exact oneActive
  · rintro ⟨inside, covered⟩
    constructor
    · intro base baseMember
      by_cases basePhase : base.1 = (raw.phase : Int)
      · right
        intro symmetry symmetryMember
        by_cases selected :
            raw.assignmentAtCell periodicStrip WindowState.center base =
              some symmetry
        · right
          exact inside base baseMember basePhase symmetry symmetryMember selected
        · exact Or.inl selected
      · exact Or.inl basePhase
    · intro base baseMember
      by_cases basePhase : base.1 = (raw.phase : Int)
      · exact Or.inr (covered base baseMember basePhase)
      · exact Or.inl basePhase

theorem overlapsBool_eq_true_iff (periodicStrip : PeriodicStrip)
    (current next : RawWindowState) :
    current.overlapsBool periodicStrip next = true ↔
      current.Overlaps periodicStrip next := by
  simp [overlapsBool, Overlaps, decide_eq_true_eq]

theorem transitionBool_eq_true_iff (tromino : Tromino)
    (periodicStrip : PeriodicStrip) (current next : RawWindowState) :
    current.transitionBool tromino periodicStrip next = true ↔
      current.Transition tromino periodicStrip next := by
  simp [transitionBool, Transition,
    isNormalizedBool_eq_true_iff, isCenterValidBool_eq_true_iff,
    overlapsBool_eq_true_iff, and_assoc]

theorem isNormalized_iff_toWindowState (periodicStrip : PeriodicStrip)
    (raw : RawWindowState) (valid : raw.IsValid periodicStrip) :
    raw.IsNormalized periodicStrip ↔
      (raw.toWindowState periodicStrip valid).IsNormalized := by
  constructor
  · intro normalized column base
    have rawConstraint := normalized column (by simp)
      base.val ((mem_motifCells periodicStrip base.val).mpr base.property)
    rw [columnPhase_toWindowState periodicStrip raw valid column] at rawConstraint
    exact rawConstraint
  · intro normalized column _columnMember base baseMember
    have motifMember :
        base ∈ periodicStrip.motif.toFinset :=
      (mem_motifCells periodicStrip base).mp baseMember
    let typedBase : periodicStrip.MotifCell := ⟨base, motifMember⟩
    have semanticConstraint := normalized column typedBase
    rw [← columnPhase_toWindowState periodicStrip raw valid column]
      at semanticConstraint
    exact semanticConstraint

theorem shiftPhase_one_toWindowState (periodicStrip : PeriodicStrip)
    (raw : RawWindowState) (valid : raw.IsValid periodicStrip) :
    (shiftPhase (raw.toWindowState periodicStrip valid).phase 1).val =
      (raw.phase + 1) % periodicStrip.period := by
  have periodPositive : 0 < periodicStrip.period :=
    Nat.zero_lt_of_lt valid.1
  unfold shiftPhase toWindowState
  simp only
  rw [Int.toNat_emod (by positivity) (by positivity)]
  simp

theorem activePlacementList_length_toWindowState
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (raw : RawWindowState) (valid : raw.IsValid periodicStrip) (row : Int) :
    (raw.activePlacementList tromino periodicStrip row).length =
      ((TrominoAssignment.coveringPlacements tromino (0, row)).filter
        fun placement =>
          (raw.toWindowState periodicStrip valid).localAssignment
              placement.offset =
            some placement.symmetry).card := by
  unfold activePlacementList
  rw [localAssignment_toWindowState periodicStrip raw valid]
  exact TrominoAssignment.activeCandidateLength_eq_card tromino (0, row)
    (raw.toWindowState periodicStrip valid).localAssignment

theorem overlaps_iff_toWindowState (periodicStrip : PeriodicStrip)
    (current next : RawWindowState)
    (currentValid : current.IsValid periodicStrip)
    (nextValid : next.IsValid periodicStrip) :
    current.Overlaps periodicStrip next ↔
      (current.toWindowState periodicStrip currentValid).Overlaps
        (next.toWindowState periodicStrip nextValid) := by
  constructor
  · rintro ⟨phaseAdvance, shared⟩
    constructor
    · apply Fin.ext
      change next.phase =
        (shiftPhase
          (current.toWindowState periodicStrip currentValid).phase 1).val
      rw [shiftPhase_one_toWindowState periodicStrip current currentValid]
      exact phaseAdvance
    · intro column base
      exact shared column (by simp) base.val
        ((mem_motifCells periodicStrip base.val).mpr base.property)
  · rintro ⟨phaseAdvance, shared⟩
    constructor
    · have phaseValues := congrArg Fin.val phaseAdvance
      change next.phase =
        (shiftPhase
          (current.toWindowState periodicStrip currentValid).phase 1).val
        at phaseValues
      rw [shiftPhase_one_toWindowState periodicStrip current currentValid]
        at phaseValues
      exact phaseValues
    · intro column _columnMember base baseMember
      have motifMember :
          base ∈ periodicStrip.motif.toFinset :=
        (mem_motifCells periodicStrip base).mp baseMember
      exact shared column ⟨base, motifMember⟩

theorem isCenterValid_iff_toWindowState (tromino : Tromino)
    (periodicStrip : PeriodicStrip) (raw : RawWindowState)
    (valid : raw.IsValid periodicStrip) :
    raw.IsCenterValid tromino periodicStrip ↔
      (raw.toWindowState periodicStrip valid).IsCenterValid tromino := by
  constructor
  · rintro ⟨inside, covered⟩
    constructor
    · intro base basePhase symmetry selected cell cellMember
      obtain ⟨source, sourceMember, sourceEquality⟩ :=
        (Placement.mem_cells_iff
          (fun _ : Unit => tromino.cells)
          (Placement.mk () symmetry (0, base.val.2)) cell).mp cellMember
      have rawInside := inside base.val
        ((mem_motifCells periodicStrip base.val).mpr base.property)
        basePhase symmetry
        (TrominoAssignment.mem_squareSymmetryList symmetry)
        selected source
        ((TrominoAssignment.mem_trominoCellList_iff tromino source).mpr
          sourceMember)
      have carrierMember :=
        (periodicStrip.contains_eq_true_iff _).mp rawInside
      subst cell
      simpa [WindowState.RelativeRegion, toWindowState, Cell.add] using
        carrierMember
    · intro base basePhase
      have rawCovered := covered base.val
        ((mem_motifCells periodicStrip base.val).mpr base.property)
        basePhase
      rw [activePlacementList_length_toWindowState
        tromino periodicStrip raw valid base.val.2] at rawCovered
      exact rawCovered
  · rintro ⟨inside, covered⟩
    constructor
    · intro base baseMember basePhase symmetry _symmetryMember selected
        source sourceMember
      have motifMember :
          base ∈ periodicStrip.motif.toFinset :=
        (mem_motifCells periodicStrip base).mp baseMember
      let typedBase : periodicStrip.MotifCell := ⟨base, motifMember⟩
      have sourceInTromino :
          source ∈ tromino.cells :=
        (TrominoAssignment.mem_trominoCellList_iff tromino source).mp
          sourceMember
      have placementMember :
          Cell.add (0, base.2) (symmetry.act source) ∈
            (Placement.mk () symmetry (0, base.2)).cells
              (fun _ : Unit => tromino.cells) := by
        rw [Placement.mem_cells_iff]
        exact ⟨source, sourceInTromino, rfl⟩
      have semanticInside := inside typedBase basePhase symmetry selected
        (Cell.add (0, base.2) (symmetry.act source)) placementMember
      apply (periodicStrip.contains_eq_true_iff _).mpr
      simpa [WindowState.RelativeRegion, toWindowState, Cell.add] using
        semanticInside
    · intro base baseMember basePhase
      have motifMember :
          base ∈ periodicStrip.motif.toFinset :=
        (mem_motifCells periodicStrip base).mp baseMember
      have semanticCovered := covered
        (⟨base, motifMember⟩ : periodicStrip.MotifCell) basePhase
      rw [activePlacementList_length_toWindowState
        tromino periodicStrip raw valid base.2]
      exact semanticCovered

theorem transition_iff_toWindowState (tromino : Tromino)
    (periodicStrip : PeriodicStrip) (current next : RawWindowState)
    (currentValid : current.IsValid periodicStrip)
    (nextValid : next.IsValid periodicStrip) :
    current.Transition tromino periodicStrip next ↔
      WindowState.Transition tromino
        (current.toWindowState periodicStrip currentValid)
        (next.toWindowState periodicStrip nextValid) := by
  rw [Transition, WindowState.Transition,
    isNormalized_iff_toWindowState periodicStrip current currentValid,
    isCenterValid_iff_toWindowState tromino periodicStrip current currentValid,
    overlaps_iff_toWindowState periodicStrip current next
      currentValid nextValid]

end RawWindowState
end PeriodicStrip
end LeanTrominoes
