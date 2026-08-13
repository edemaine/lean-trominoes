/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.StripFrontierIndexComputability
import LeanTrominoes.StripFrontierRawTransition

/-!
# Computability of raw sparse-frontier transitions

The raw transition verifier uses only arithmetic, canonical finite lists, and
uniform assignment words.  This file proves those executable operations
primitive recursive, preparing the indexed Savitch decider for compilation to
the finite two-stack machine model.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState

open LeanTrominoes.Computability

private theorem listAll_primrec {α β : Type*}
    [Primcodable α] [Primcodable β]
    {items : α → List β} {predicate : α → β → Bool}
    (itemsPrimrec : Primrec items)
    (predicatePrimrec : Primrec₂ predicate) :
    Primrec fun input => (items input).all (predicate input) := by
  let step : α → β × Bool → Bool :=
    fun input state => predicate input state.1 && state.2
  have stepPrimrec : Primrec₂ step := by
    exact Primrec.and.comp₂
      (predicatePrimrec.comp₂ Primrec₂.left
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr itemsPrimrec (Primrec.const true)
    stepPrimrec).of_eq fun input => by
      induction items input with
      | nil => rfl
      | cons head tail induction =>
          simp [step, induction]

theorem WindowColumn.ofDisplacementCode?_primrec :
    Primrec WindowColumn.ofDisplacementCode? := by
  unfold WindowColumn.ofDisplacementCode?
  exact Primrec.ite
    (Primrec.eq.comp Primrec.id (Primrec.const (-2 : Int)))
    (Primrec.const (some (⟨0, by omega⟩ : WindowColumn)))
    (Primrec.ite
      (Primrec.eq.comp Primrec.id (Primrec.const (-1 : Int)))
      (Primrec.const (some (⟨1, by omega⟩ : WindowColumn)))
      (Primrec.ite
        (Primrec.eq.comp Primrec.id (Primrec.const (0 : Int)))
        (Primrec.const (some (⟨2, by omega⟩ : WindowColumn)))
        (Primrec.ite
          (Primrec.eq.comp Primrec.id (Primrec.const (1 : Int)))
          (Primrec.const (some (⟨3, by omega⟩ : WindowColumn)))
          (Primrec.ite
            (Primrec.eq.comp Primrec.id (Primrec.const (2 : Int)))
            (Primrec.const (some (⟨4, by omega⟩ : WindowColumn)))
            (Primrec.const none)))))

theorem columnPhase_primrec :
    Primrec fun input : PeriodicStrip × RawWindowState × WindowColumn =>
      input.2.1.columnPhase input.1 input.2.2 := by
  let strip : Primrec fun
      input : PeriodicStrip × RawWindowState × WindowColumn => input.1 :=
    Primrec.fst
  let raw : Primrec fun
      input : PeriodicStrip × RawWindowState × WindowColumn => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let column : Primrec fun
      input : PeriodicStrip × RawWindowState × WindowColumn => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  let phase := rawWindowState_phase_primrec.comp raw
  let columnValue := Primrec.fin_val.comp column
  let period := periodicStrip_period_primrec.comp strip
  unfold columnPhase
  exact Primrec.nat_mod.comp
    (Primrec.nat_sub.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp phase columnValue)
        (Primrec.nat_mul.comp (Primrec.const 2) period))
      (Primrec.const 2))
    period

theorem valueAt_primrec :
    Primrec fun input :
      PeriodicStrip × RawWindowState × WindowColumn × Int =>
      input.2.1.valueAt input.1 input.2.2.1 input.2.2.2 := by
  let strip : Primrec fun
      input : PeriodicStrip × RawWindowState × WindowColumn × Int =>
      input.1 :=
    Primrec.fst
  let raw : Primrec fun
      input : PeriodicStrip × RawWindowState × WindowColumn × Int =>
      input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let column : Primrec fun
      input : PeriodicStrip × RawWindowState × WindowColumn × Int =>
      input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let row : Primrec fun
      input : PeriodicStrip × RawWindowState × WindowColumn × Int =>
      input.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  let phase : Primrec fun
      input : PeriodicStrip × RawWindowState × WindowColumn × Int =>
      input.2.1.columnPhase input.1 input.2.2.1 :=
    columnPhase_primrec.comp
      (Primrec.pair strip (Primrec.pair raw column))
  unfold valueAt
  exact assignmentAtCell_primrec.comp
    (Primrec.pair strip
      (Primrec.pair raw
        (Primrec.pair column
          (Primrec.pair (int_ofNat_primrec.comp phase) row))))

theorem localAssignmentAt_primrec :
    Primrec fun input : PeriodicStrip × RawWindowState × Cell =>
      input.2.1.localAssignment input.1 input.2.2 := by
  let strip : Primrec fun
      input : PeriodicStrip × RawWindowState × Cell => input.1 :=
    Primrec.fst
  let raw : Primrec fun
      input : PeriodicStrip × RawWindowState × Cell => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let offset : Primrec fun
      input : PeriodicStrip × RawWindowState × Cell => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  let displacement : Primrec fun
      input : PeriodicStrip × RawWindowState × Cell => input.2.2.1 :=
    Primrec.fst.comp offset
  let row : Primrec fun
      input : PeriodicStrip × RawWindowState × Cell => input.2.2.2 :=
    Primrec.snd.comp offset
  unfold localAssignment
  exact (Primrec.option_casesOn
    (WindowColumn.ofDisplacementCode?_primrec.comp displacement)
    (Primrec.const none)
    (valueAt_primrec.comp₂
      (Primrec₂.pair.comp₂
        (strip.comp₂ Primrec₂.left)
        (Primrec₂.pair.comp₂
          (raw.comp₂ Primrec₂.left)
          (Primrec₂.pair.comp₂ Primrec₂.right
            (row.comp₂ Primrec₂.left)))))).of_eq fun input => by
      cases WindowColumn.ofDisplacementCode? input.2.2.1 <;> rfl

theorem activePlacementList_primrec (tromino : Tromino) :
    Primrec fun input : PeriodicStrip × RawWindowState × Int =>
      input.2.1.activePlacementList tromino input.1 input.2.2 := by
  let strip : Primrec fun
      input : PeriodicStrip × RawWindowState × Int => input.1 :=
    Primrec.fst
  let raw : Primrec fun
      input : PeriodicStrip × RawWindowState × Int => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let row : Primrec fun
      input : PeriodicStrip × RawWindowState × Int => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  have active : PrimrecRel fun (placement : Placement Unit)
      (input : PeriodicStrip × RawWindowState × Int) =>
      input.2.1.localAssignment input.1 placement.offset =
        some placement.symmetry := by
    exact Primrec.eq.comp₂
      (localAssignmentAt_primrec.comp₂
        (Primrec₂.pair.comp₂
          (strip.comp₂ Primrec₂.right)
          (Primrec₂.pair.comp₂
            (raw.comp₂ Primrec₂.right)
            (TrominoAssignment.placement_offset_primrec.comp₂
              Primrec₂.left))))
      (Primrec.option_some.comp₂
        (TrominoAssignment.placement_symmetry_primrec.comp₂ Primrec₂.left))
  unfold activePlacementList
  exact active.listFilter.comp
    ((TrominoAssignment.coveringPlacementList_primrec tromino).comp
      (Primrec.pair (Primrec.const (0 : Int)) row))
    Primrec.id

private abbrev RawContext := PeriodicStrip × RawWindowState

theorem normalizedAtBool_primrec :
    Primrec fun input :
      PeriodicStrip × RawWindowState × WindowColumn × Cell =>
      input.2.1.normalizedAtBool input.1 input.2.2.1 input.2.2.2 := by
  let phase : Primrec fun input :
      PeriodicStrip × RawWindowState × WindowColumn × Cell =>
      input.2.1.columnPhase input.1 input.2.2.1 :=
    columnPhase_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  have phaseEqual : PrimrecPred fun input :
      PeriodicStrip × RawWindowState × WindowColumn × Cell =>
      input.2.2.2.1 = (input.2.1.columnPhase input.1 input.2.2.1 : Int) :=
    Primrec.eq.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (int_ofNat_primrec.comp phase)
  have assignmentNone : PrimrecPred fun input :
      PeriodicStrip × RawWindowState × WindowColumn × Cell =>
      input.2.1.assignmentAtCell input.1 input.2.2.1 input.2.2.2 = none :=
    Primrec.eq.comp assignmentAtCell_primrec (Primrec.const none)
  unfold normalizedAtBool
  exact Primrec.or.comp phaseEqual.decide assignmentNone.decide

theorem normalizedColumnBool_primrec :
    Primrec fun input :
      PeriodicStrip × RawWindowState × WindowColumn =>
      input.2.1.normalizedColumnBool input.1 input.2.2 := by
  have predicate : Primrec₂ fun
      (input : PeriodicStrip × RawWindowState × WindowColumn) (base : Cell) =>
      input.2.1.normalizedAtBool input.1 input.2.2 base := by
    exact normalizedAtBool_primrec.comp₂
      (Primrec₂.pair.comp₂
        (Primrec.fst.comp₂ Primrec₂.left)
        (Primrec₂.pair.comp₂
          ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left)
          (Primrec₂.pair.comp₂
            ((Primrec.snd.comp Primrec.snd).comp₂ Primrec₂.left)
            Primrec₂.right)))
  unfold normalizedColumnBool
  exact listAll_primrec
    (motifCells_primrec.comp Primrec.fst) predicate

theorem isNormalizedBool_primrec :
    Primrec fun input : RawContext =>
      input.2.isNormalizedBool input.1 := by
  unfold isNormalizedBool
  exact listAll_primrec
    (Primrec.const (List.finRange 5))
    (normalizedColumnBool_primrec.comp₂
      (Primrec₂.pair.comp₂
        (Primrec.fst.comp₂ Primrec₂.left)
        (Primrec₂.pair.comp₂
          (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)))

theorem centerSourceInsideBool_primrec :
    Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry × Cell =>
      input.2.1.centerSourceInsideBool input.1 input.2.2.1
        input.2.2.2.1 input.2.2.2.2 := by
  let strip : Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry × Cell =>
      input.1 :=
    Primrec.fst
  let raw : Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry × Cell =>
      input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let base : Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry × Cell =>
      input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let symmetry : Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry × Cell =>
      input.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  let source : Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry × Cell =>
      input.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  let offset : Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry × Cell =>
      ((input.2.1.phase : Int), input.2.2.1.2) :=
    Primrec.pair
      (int_ofNat_primrec.comp (rawWindowState_phase_primrec.comp raw))
      (Primrec.snd.comp base)
  let coveredCell : Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry × Cell =>
      Cell.add ((input.2.1.phase : Int), input.2.2.1.2)
        (input.2.2.2.1.act input.2.2.2.2) :=
    cell_add_primrec.comp
      offset (squareSymmetry_act_primrec.comp symmetry source)
  unfold centerSourceInsideBool
  exact periodicStrip_contains_primrec.comp strip coveredCell

theorem centerSymmetryInsideBool_primrec (tromino : Tromino) :
    Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry =>
      input.2.1.centerSymmetryInsideBool tromino input.1
        input.2.2.1 input.2.2.2 := by
  let strip : Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry => input.1 :=
    Primrec.fst
  let raw : Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let base : Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry => input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let symmetry : Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry => input.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  let assignment : Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry =>
      input.2.1.assignmentAtCell input.1 WindowState.center input.2.2.1 :=
    assignmentAtCell_primrec.comp
      (Primrec.pair strip
        (Primrec.pair raw
          (Primrec.pair (Primrec.const WindowState.center) base)))
  have selected : PrimrecPred fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry =>
      input.2.1.assignmentAtCell input.1 WindowState.center input.2.2.1 =
        some input.2.2.2 :=
    Primrec.eq.comp assignment
      (Primrec.option_some.comp symmetry)
  have sourcePredicateOne : Primrec fun
      pair :
        (PeriodicStrip × RawWindowState × Cell × SquareSymmetry) × Cell =>
      pair.1.2.1.centerSourceInsideBool pair.1.1 pair.1.2.2.1
        pair.1.2.2.2 pair.2 := by
    let sourceInput : Primrec fun
        pair :
          (PeriodicStrip × RawWindowState × Cell × SquareSymmetry) × Cell =>
        (pair.1.1, pair.1.2.1, pair.1.2.2.1, pair.1.2.2.2, pair.2) :=
      Primrec.pair
        (strip.comp Primrec.fst)
        (Primrec.pair
          (raw.comp Primrec.fst)
          (Primrec.pair
            (base.comp Primrec.fst)
            (Primrec.pair
              (symmetry.comp Primrec.fst) Primrec.snd)))
    exact (centerSourceInsideBool_primrec.comp sourceInput).of_eq
      fun _ => rfl
  have sourcePredicate : Primrec₂ fun
      (input : PeriodicStrip × RawWindowState × Cell × SquareSymmetry)
      (source : Cell) =>
      input.2.1.centerSourceInsideBool input.1 input.2.2.1 input.2.2.2
        source :=
    sourcePredicateOne.to₂
  have sourcesInside : Primrec fun input :
      PeriodicStrip × RawWindowState × Cell × SquareSymmetry =>
      (TrominoAssignment.trominoCellList tromino).all fun source =>
        input.2.1.centerSourceInsideBool input.1 input.2.2.1 input.2.2.2
          source :=
    listAll_primrec
      (Primrec.const (TrominoAssignment.trominoCellList tromino))
      sourcePredicate
  unfold centerSymmetryInsideBool
  exact Primrec.or.comp
    selected.not.decide sourcesInside

theorem centerBaseInsideBool_primrec (tromino : Tromino) :
    Primrec fun input : PeriodicStrip × RawWindowState × Cell =>
      input.2.1.centerBaseInsideBool tromino input.1 input.2.2 := by
  let strip : Primrec fun
      input : PeriodicStrip × RawWindowState × Cell => input.1 :=
    Primrec.fst
  let raw : Primrec fun
      input : PeriodicStrip × RawWindowState × Cell => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let base : Primrec fun
      input : PeriodicStrip × RawWindowState × Cell => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  have phaseEqual : PrimrecPred fun
      input : PeriodicStrip × RawWindowState × Cell =>
      input.2.2.1 = (input.2.1.phase : Int) :=
    Primrec.eq.comp
      (Primrec.fst.comp base)
      (int_ofNat_primrec.comp (rawWindowState_phase_primrec.comp raw))
  have symmetryPredicateOne : Primrec fun
      pair : (PeriodicStrip × RawWindowState × Cell) × SquareSymmetry =>
      pair.1.2.1.centerSymmetryInsideBool tromino pair.1.1 pair.1.2.2
        pair.2 := by
    let symmetryInput : Primrec fun
        pair : (PeriodicStrip × RawWindowState × Cell) × SquareSymmetry =>
        (pair.1.1, pair.1.2.1, pair.1.2.2, pair.2) :=
      Primrec.pair
        (strip.comp Primrec.fst)
        (Primrec.pair
          (raw.comp Primrec.fst)
          (Primrec.pair (base.comp Primrec.fst) Primrec.snd))
    exact ((centerSymmetryInsideBool_primrec tromino).comp
      symmetryInput).of_eq fun _ => rfl
  have symmetryPredicate : Primrec₂ fun
      (input : PeriodicStrip × RawWindowState × Cell)
      (symmetry : SquareSymmetry) =>
      input.2.1.centerSymmetryInsideBool tromino input.1 input.2.2
        symmetry :=
    symmetryPredicateOne.to₂
  have symmetriesInside : Primrec fun
      input : PeriodicStrip × RawWindowState × Cell =>
      TrominoAssignment.squareSymmetryList.all fun symmetry =>
        input.2.1.centerSymmetryInsideBool tromino input.1 input.2.2
          symmetry :=
    listAll_primrec
      (Primrec.const TrominoAssignment.squareSymmetryList)
      symmetryPredicate
  unfold centerBaseInsideBool
  exact Primrec.or.comp
    phaseEqual.not.decide symmetriesInside

theorem centerInsideBool_primrec (tromino : Tromino) :
    Primrec fun input : RawContext =>
      input.2.centerInsideBool tromino input.1 := by
  have basePredicate : Primrec₂ fun (input : RawContext) (base : Cell) =>
      input.2.centerBaseInsideBool tromino input.1 base := by
    exact centerBaseInsideBool_primrec tromino |>.comp₂
      (Primrec₂.pair.comp₂
        (Primrec.fst.comp₂ Primrec₂.left)
        (Primrec₂.pair.comp₂
          (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right))
  unfold centerInsideBool
  exact listAll_primrec
    (motifCells_primrec.comp Primrec.fst) basePredicate

theorem centerBaseCoveredBool_primrec (tromino : Tromino) :
    Primrec fun input : PeriodicStrip × RawWindowState × Cell =>
      input.2.1.centerBaseCoveredBool tromino input.1 input.2.2 := by
  let strip : Primrec fun
      input : PeriodicStrip × RawWindowState × Cell => input.1 :=
    Primrec.fst
  let raw : Primrec fun
      input : PeriodicStrip × RawWindowState × Cell => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let base : Primrec fun
      input : PeriodicStrip × RawWindowState × Cell => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  have phaseEqual : PrimrecPred fun
      input : PeriodicStrip × RawWindowState × Cell =>
      input.2.2.1 = (input.2.1.phase : Int) :=
    Primrec.eq.comp
      (Primrec.fst.comp base)
      (int_ofNat_primrec.comp (rawWindowState_phase_primrec.comp raw))
  let active : Primrec fun
      input : PeriodicStrip × RawWindowState × Cell =>
      input.2.1.activePlacementList tromino input.1 input.2.2.2 :=
    (activePlacementList_primrec tromino).comp
      (Primrec.pair strip
        (Primrec.pair raw (Primrec.snd.comp base)))
  have oneActive : PrimrecPred fun
      input : PeriodicStrip × RawWindowState × Cell =>
      (input.2.1.activePlacementList tromino input.1 input.2.2.2).length =
        1 :=
    Primrec.eq.comp
      (Primrec.list_length.comp active) (Primrec.const 1)
  unfold centerBaseCoveredBool
  exact Primrec.or.comp
    phaseEqual.not.decide oneActive.decide

theorem centerCoveredBool_primrec (tromino : Tromino) :
    Primrec fun input : RawContext =>
      input.2.centerCoveredBool tromino input.1 := by
  have basePredicate : Primrec₂ fun (input : RawContext) (base : Cell) =>
      input.2.centerBaseCoveredBool tromino input.1 base := by
    exact centerBaseCoveredBool_primrec tromino |>.comp₂
      (Primrec₂.pair.comp₂
        (Primrec.fst.comp₂ Primrec₂.left)
        (Primrec₂.pair.comp₂
          (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right))
  unfold centerCoveredBool
  exact listAll_primrec
    (motifCells_primrec.comp Primrec.fst) basePredicate

theorem isCenterValidBool_primrec (tromino : Tromino) :
    Primrec fun input : RawContext =>
      input.2.isCenterValidBool tromino input.1 := by
  unfold isCenterValidBool
  exact Primrec.and.comp
    (centerInsideBool_primrec tromino)
    (centerCoveredBool_primrec tromino)

private abbrev TransitionContext :=
  PeriodicStrip × RawWindowState × RawWindowState

theorem overlapsAtBool_primrec :
    Primrec fun input :
      PeriodicStrip × RawWindowState × RawWindowState × Fin 4 × Cell =>
      input.2.1.overlapsAtBool input.1 input.2.2.1 input.2.2.2.1
        input.2.2.2.2 := by
  let strip : Primrec fun input :
      PeriodicStrip × RawWindowState × RawWindowState × Fin 4 × Cell =>
      input.1 :=
    Primrec.fst
  let current : Primrec fun input :
      PeriodicStrip × RawWindowState × RawWindowState × Fin 4 × Cell =>
      input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let next : Primrec fun input :
      PeriodicStrip × RawWindowState × RawWindowState × Fin 4 × Cell =>
      input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let column : Primrec fun input :
      PeriodicStrip × RawWindowState × RawWindowState × Fin 4 × Cell =>
      input.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  let base : Primrec fun input :
      PeriodicStrip × RawWindowState × RawWindowState × Fin 4 × Cell =>
      input.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have castSuccPrimrec : Primrec (Fin.castSucc : Fin 4 → WindowColumn) :=
    Primrec.fin_val_iff.mp
      (Primrec.fin_val.of_eq fun _ => rfl)
  let currentAssignment : Primrec fun input :
      PeriodicStrip × RawWindowState × RawWindowState × Fin 4 × Cell =>
      input.2.1.assignmentAtCell input.1 input.2.2.2.1.succ input.2.2.2.2 :=
    assignmentAtCell_primrec.comp
      (Primrec.pair strip
        (Primrec.pair current
          (Primrec.pair (Primrec.fin_succ.comp column) base)))
  let nextAssignment : Primrec fun input :
      PeriodicStrip × RawWindowState × RawWindowState × Fin 4 × Cell =>
      input.2.2.1.assignmentAtCell input.1 input.2.2.2.1.castSucc
        input.2.2.2.2 :=
    assignmentAtCell_primrec.comp
      (Primrec.pair strip
        (Primrec.pair next
          (Primrec.pair (castSuccPrimrec.comp column) base)))
  unfold overlapsAtBool
  exact (Primrec.eq.comp currentAssignment nextAssignment).decide

theorem overlapsColumnBool_primrec :
    Primrec fun input :
      PeriodicStrip × RawWindowState × RawWindowState × Fin 4 =>
      input.2.1.overlapsColumnBool input.1 input.2.2.1 input.2.2.2 := by
  have basePredicate : Primrec₂ fun
      (input : PeriodicStrip × RawWindowState × RawWindowState × Fin 4)
      (base : Cell) =>
      input.2.1.overlapsAtBool input.1 input.2.2.1 input.2.2.2 base := by
    exact overlapsAtBool_primrec.comp₂
      (Primrec₂.pair.comp₂
        (Primrec.fst.comp₂ Primrec₂.left)
        (Primrec₂.pair.comp₂
          ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left)
          (Primrec₂.pair.comp₂
            ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp₂
              Primrec₂.left)
            (Primrec₂.pair.comp₂
              ((Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp₂
                Primrec₂.left)
              Primrec₂.right))))
  unfold overlapsColumnBool
  exact listAll_primrec
    (motifCells_primrec.comp Primrec.fst) basePredicate

theorem overlapsBool_primrec :
    Primrec fun input : TransitionContext =>
      input.2.1.overlapsBool input.1 input.2.2 := by
  let strip : Primrec fun input : TransitionContext => input.1 :=
    Primrec.fst
  let current : Primrec fun input : TransitionContext => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let next : Primrec fun input : TransitionContext => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  have phaseAdvance : PrimrecPred fun input : TransitionContext =>
      input.2.2.phase = (input.2.1.phase + 1) % input.1.period :=
    Primrec.eq.comp
      (rawWindowState_phase_primrec.comp next)
      (Primrec.nat_mod.comp
        (Primrec.nat_add.comp
          (rawWindowState_phase_primrec.comp current)
          (Primrec.const 1))
        (periodicStrip_period_primrec.comp strip))
  have columnPredicate : Primrec₂ fun
      (input : TransitionContext) (column : Fin 4) =>
      input.2.1.overlapsColumnBool input.1 input.2.2 column := by
    exact overlapsColumnBool_primrec.comp₂
      (Primrec₂.pair.comp₂
        (Primrec.fst.comp₂ Primrec₂.left)
        (Primrec₂.pair.comp₂
          ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left)
          (Primrec₂.pair.comp₂
            ((Primrec.snd.comp Primrec.snd).comp₂ Primrec₂.left)
            Primrec₂.right)))
  have columnsOverlap : Primrec fun input : TransitionContext =>
      (List.finRange 4).all fun column =>
        input.2.1.overlapsColumnBool input.1 input.2.2 column :=
    listAll_primrec (Primrec.const (List.finRange 4)) columnPredicate
  unfold overlapsBool
  exact Primrec.and.comp phaseAdvance.decide columnsOverlap

theorem transitionBool_primrec (tromino : Tromino) :
    Primrec fun input : TransitionContext =>
      input.2.1.transitionBool tromino input.1 input.2.2 := by
  unfold transitionBool
  exact Primrec.and.comp
    (Primrec.and.comp
      (isNormalizedBool_primrec.comp
        (Primrec.pair Primrec.fst
          (Primrec.fst.comp Primrec.snd)))
      ((isCenterValidBool_primrec tromino).comp
        (Primrec.pair Primrec.fst
          (Primrec.fst.comp Primrec.snd))))
    overlapsBool_primrec

end RawWindowState
end PeriodicStrip
end LeanTrominoes
