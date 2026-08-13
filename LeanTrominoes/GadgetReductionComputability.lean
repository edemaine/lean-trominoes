/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computability
import LeanTrominoes.ComputableSearch
import LeanTrominoes.GadgetReduction
import LeanTrominoes.Theorem52

/-!
# Computability of the Figure 11/12 block substitution

The semantic substitution is written with dependent finite indices.  For
computability, this file gives an extensionally equal implementation using
ordinary natural-number ranges and proves that implementation primitive
recursive.
-/

namespace LeanTrominoes
namespace Gadget

open Computability

/-- The values of `Fin n` in enumeration order are exactly `0, …, n-1`. -/
theorem finRange_values (n : Nat) :
    (List.finRange n).map Fin.val = List.range n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ_last, List.map_append, List.map_map,
        List.range_succ]
      rw [show (Fin.val ∘ Fin.castSucc) = Fin.val by
        funext index
        rfl]
      simp only [List.map_singleton, Fin.val_last]
      rw [ih]

/-- Drawing-cell lookup using unrestricted natural indices. -/
def PeriodicOrthogonalDrawing.indexedCellType
    (drawing : PeriodicOrthogonalDrawing) (horizontal vertical : Nat) :
    OrthogonalCellType :=
  drawing.cellTypes.getD
    (vertical * drawing.horizontalPeriod + horizontal) .blank

/-- One expanded block, with its torus position represented by naturals. -/
def PeriodicOrthogonalDrawing.indexedExpandedBlockPixels
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (horizontal vertical : Nat) : List Cell :=
  (orthogonalCellPixels tromino
    (drawing.indexedCellType horizontal vertical)).map fun pixel =>
      Cell.add
        (PeriodicOrthogonalDrawing.blockOrigin horizontal vertical) pixel

/-- The expanded motif implemented with ordinary primitive-recursive
`List.range` enumeration. -/
def PeriodicOrthogonalDrawing.computableExpandedMotif
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing) : List Cell :=
  (List.range drawing.horizontalPeriod).flatMap fun horizontal =>
    (List.range drawing.verticalPeriod).flatMap fun vertical =>
      drawing.indexedExpandedBlockPixels tromino horizontal vertical

theorem PeriodicOrthogonalDrawing.indexedExpandedBlockPixels_eq
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (horizontal : Fin drawing.horizontalPeriod)
    (vertical : Fin drawing.verticalPeriod) :
    drawing.indexedExpandedBlockPixels tromino horizontal.val vertical.val =
      expandedBlockPixels tromino drawing (horizontal, vertical) := by
  rfl

/-- The natural-range implementation preserves the exact motif list, not just
its carrier. -/
theorem PeriodicOrthogonalDrawing.computableExpandedMotif_eq
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing) :
    drawing.computableExpandedMotif tromino =
      drawing.expandedMotif tromino := by
  unfold computableExpandedMotif expandedMotif
  rw [← finRange_values drawing.horizontalPeriod, List.flatMap_map]
  apply List.flatMap_congr
  intro horizontal _
  rw [← finRange_values drawing.verticalPeriod, List.flatMap_map]
  apply List.flatMap_congr
  intro vertical _
  exact drawing.indexedExpandedBlockPixels_eq tromino horizontal vertical

/-- A natural-range implementation of the full target presentation. -/
def PeriodicOrthogonalDrawing.computablePeriodicRegion
    (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : PeriodicRegion where
  motif := drawing.computableExpandedMotif tromino
  period₁ := (6 * (drawing.horizontalPeriod : Int), 0)
  period₂ := (0, 6 * (drawing.verticalPeriod : Int))

theorem PeriodicOrthogonalDrawing.computablePeriodicRegion_eq
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing) :
    drawing.computablePeriodicRegion tromino =
      drawing.periodicRegion tromino := by
  apply PeriodicRegion.equivData.injective
  simp [PeriodicRegion.equivData, computablePeriodicRegion,
    PeriodicOrthogonalDrawing.periodicRegion,
    drawing.computableExpandedMotif_eq tromino]

/-! ## Primitive-recursive implementation -/

theorem periodicOrthogonalDrawing_equivData_primrec :
    Primrec PeriodicOrthogonalDrawing.equivData := by
  exact Primrec.of_equiv

theorem periodicOrthogonalDrawing_horizontalPeriodPred_primrec :
    Primrec PeriodicOrthogonalDrawing.horizontalPeriodPred := by
  exact (Primrec.fst.comp
    periodicOrthogonalDrawing_equivData_primrec).of_eq fun _ => rfl

theorem periodicOrthogonalDrawing_verticalPeriodPred_primrec :
    Primrec PeriodicOrthogonalDrawing.verticalPeriodPred := by
  exact (Primrec.fst.comp (Primrec.snd.comp
    periodicOrthogonalDrawing_equivData_primrec)).of_eq fun _ => rfl

theorem periodicOrthogonalDrawing_cellTypes_primrec :
    Primrec PeriodicOrthogonalDrawing.cellTypes := by
  exact (Primrec.snd.comp (Primrec.snd.comp
    periodicOrthogonalDrawing_equivData_primrec)).of_eq fun _ => rfl

theorem periodicOrthogonalDrawing_horizontalPeriod_primrec :
    Primrec PeriodicOrthogonalDrawing.horizontalPeriod := by
  unfold PeriodicOrthogonalDrawing.horizontalPeriod
  exact Primrec.nat_add.comp
    periodicOrthogonalDrawing_horizontalPeriodPred_primrec
    (Primrec.const 1)

theorem periodicOrthogonalDrawing_verticalPeriod_primrec :
    Primrec PeriodicOrthogonalDrawing.verticalPeriod := by
  unfold PeriodicOrthogonalDrawing.verticalPeriod
  exact Primrec.nat_add.comp
    periodicOrthogonalDrawing_verticalPeriodPred_primrec
    (Primrec.const 1)

theorem indexedCellType_primrec :
    Primrec fun input :
        PeriodicOrthogonalDrawing × (Nat × Nat) =>
      input.1.indexedCellType input.2.1 input.2.2 := by
  unfold PeriodicOrthogonalDrawing.indexedCellType
  have index : Primrec fun input :
      PeriodicOrthogonalDrawing × (Nat × Nat) =>
      input.2.2 * input.1.horizontalPeriod + input.2.1 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp
        (Primrec.snd.comp Primrec.snd)
        (periodicOrthogonalDrawing_horizontalPeriod_primrec.comp
          Primrec.fst))
      (Primrec.fst.comp Primrec.snd)
  exact Primrec.list_getD (.blank : OrthogonalCellType) |>.comp
    (periodicOrthogonalDrawing_cellTypes_primrec.comp Primrec.fst)
    index

theorem blockOrigin_primrec :
    Primrec fun indices : Nat × Nat =>
      PeriodicOrthogonalDrawing.blockOrigin indices.1 indices.2 := by
  unfold PeriodicOrthogonalDrawing.blockOrigin
  exact Primrec.pair
    (int_multiply_primrec.comp
      (Primrec.const (6 : Int))
      (int_ofNat_primrec.comp Primrec.fst))
    (int_multiply_primrec.comp
      (Primrec.const (6 : Int))
      (int_ofNat_primrec.comp Primrec.snd))

theorem indexedExpandedBlockPixels_primrec (tromino : Tromino) :
    Primrec fun input :
        PeriodicOrthogonalDrawing × (Nat × Nat) =>
      input.1.indexedExpandedBlockPixels tromino input.2.1 input.2.2 := by
  unfold PeriodicOrthogonalDrawing.indexedExpandedBlockPixels
  have pixels : Primrec fun input :
      PeriodicOrthogonalDrawing × (Nat × Nat) =>
      orthogonalCellPixels tromino
        (input.1.indexedCellType input.2.1 input.2.2) :=
    (Primrec.dom_finite (orthogonalCellPixels tromino)).comp
      indexedCellType_primrec
  exact Primrec.list_map pixels
    (cell_add_primrec.comp₂
      (blockOrigin_primrec.comp₂
        (Primrec.snd.comp₂ Primrec₂.left))
      Primrec₂.right)

theorem computableExpandedMotif_primrec (tromino : Tromino) :
    Primrec fun drawing : PeriodicOrthogonalDrawing =>
      drawing.computableExpandedMotif tromino := by
  have horizontalRange : Primrec fun drawing : PeriodicOrthogonalDrawing =>
      List.range drawing.horizontalPeriod :=
    Primrec.list_range.comp
      periodicOrthogonalDrawing_horizontalPeriod_primrec
  have rows : Primrec₂ fun (drawing : PeriodicOrthogonalDrawing)
      (horizontal : Nat) =>
      (List.range drawing.verticalPeriod).flatMap fun vertical =>
        drawing.indexedExpandedBlockPixels tromino horizontal vertical := by
    have verticalRange :
        Primrec fun input : PeriodicOrthogonalDrawing × Nat =>
          List.range input.1.verticalPeriod :=
      Primrec.list_range.comp
        (periodicOrthogonalDrawing_verticalPeriod_primrec.comp Primrec.fst)
    have blocks : Primrec₂ fun
        (input : PeriodicOrthogonalDrawing × Nat) (vertical : Nat) =>
        input.1.indexedExpandedBlockPixels tromino input.2 vertical := by
      change Primrec fun input :
          (PeriodicOrthogonalDrawing × Nat) × Nat =>
        input.1.1.indexedExpandedBlockPixels tromino
          input.1.2 input.2
      exact indexedExpandedBlockPixels_primrec tromino |>.comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.pair
            (Primrec.snd.comp Primrec.fst) Primrec.snd))
    exact Primrec.list_flatMap verticalRange blocks
  unfold PeriodicOrthogonalDrawing.computableExpandedMotif
  exact Primrec.list_flatMap horizontalRange rows

theorem computablePeriodicRegion_primrec (tromino : Tromino) :
    Primrec fun drawing : PeriodicOrthogonalDrawing =>
      drawing.computablePeriodicRegion tromino := by
  have horizontalCoordinate :
      Primrec fun drawing : PeriodicOrthogonalDrawing =>
        (6 : Int) * drawing.horizontalPeriod :=
    int_multiply_primrec.comp
      (Primrec.const (6 : Int))
      (int_ofNat_primrec.comp
        periodicOrthogonalDrawing_horizontalPeriod_primrec)
  have verticalCoordinate :
      Primrec fun drawing : PeriodicOrthogonalDrawing =>
        (6 : Int) * drawing.verticalPeriod :=
    int_multiply_primrec.comp
      (Primrec.const (6 : Int))
      (int_ofNat_primrec.comp
        periodicOrthogonalDrawing_verticalPeriod_primrec)
  have period₁ : Primrec fun drawing : PeriodicOrthogonalDrawing =>
      ((6 : Int) * drawing.horizontalPeriod, (0 : Int)) :=
    Primrec.pair horizontalCoordinate (Primrec.const 0)
  have period₂ : Primrec fun drawing : PeriodicOrthogonalDrawing =>
      ((0 : Int), (6 : Int) * drawing.verticalPeriod) :=
    Primrec.pair (Primrec.const 0) verticalCoordinate
  have data : Primrec fun drawing : PeriodicOrthogonalDrawing =>
      (drawing.computableExpandedMotif tromino,
        ((6 : Int) * drawing.horizontalPeriod, (0 : Int)),
        ((0 : Int), (6 : Int) * drawing.verticalPeriod)) :=
    Primrec.pair (computableExpandedMotif_primrec tromino)
      (Primrec.pair period₁ period₂)
  exact (Primrec.of_equiv_symm :
    Primrec PeriodicRegion.equivData.symm).comp data

/-- The exact substitution function used by the semantic reduction is
primitive recursive. -/
theorem periodicRegion_primrec (tromino : Tromino) :
    Primrec fun drawing : PeriodicOrthogonalDrawing =>
      drawing.periodicRegion tromino :=
  (computablePeriodicRegion_primrec tromino).of_eq fun drawing =>
    drawing.computablePeriodicRegion_eq tromino

theorem periodicRegion_computable (tromino : Tromino) :
    Computable fun drawing : PeriodicOrthogonalDrawing =>
      drawing.periodicRegion tromino :=
  (periodicRegion_primrec tromino).to_comp

/-! ## Complexity-theoretic reduction interface -/

/-- A computable reduction to normalized periodic trichromatic orientation.
Keeping well-formedness and vertex separation as explicit output guarantees
lets the source-hardness construction avoid any promise-problem ambiguity. -/
structure NormalizedOrientationReduction {α : Type} [Primcodable α]
    (source : α → Prop) where
  drawing : α → PeriodicOrthogonalDrawing
  drawing_computable : Computable drawing
  wellFormed : ∀ input, (drawing input).IsWellFormed
  verticesSeparated : ∀ input, (drawing input).VerticesSeparated
  correct : ∀ input, source input ↔ (drawing input).HasOrientation

/-- The missing source theorem needed by the 2D hardness proof, isolated as a
proof-neutral interface. -/
def NormalizedOrientationCoREHard : Prop :=
  ∀ {α : Type} [Primcodable α] (source : α → Prop),
    LeanWang.CoREPred source →
      Nonempty (NormalizedOrientationReduction source)

/-- On normalized inputs, unguarded gadget substitution is already an exact
many-one reduction. -/
theorem periodicRegion_correct_of_normalized
    (tromino : Tromino)
    (behavior : OrientationBehaviorCorrect tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed)
    (separated : drawing.VerticesSeparated) :
    drawing.HasOrientation ↔
      PeriodicTrominoTiling tromino (drawing.periodicRegion tromino) := by
  constructor
  · intro hasOrientation
    have compatible := (behavior drawing separated).mp hasOrientation
    exact ⟨drawing.periodicRegion_fullRank tromino,
      (substitutionAssemblyCorrect tromino drawing).mp compatible.2⟩
  · rintro ⟨-, tileable⟩
    exact (behavior drawing separated).mpr ⟨wellFormed,
      (substitutionAssemblyCorrect tromino drawing).mpr tileable⟩

/-- Compose a normalized source reduction with either verified tromino gadget
library. -/
theorem normalizedOrientationReduction_manyOne
    {α : Type} [Primcodable α] {source : α → Prop}
    (reduction : NormalizedOrientationReduction source)
    (tromino : Tromino)
    (behavior : OrientationBehaviorCorrect tromino) :
    source ≤₀ PeriodicTrominoTiling tromino := by
  refine ⟨fun input =>
      (reduction.drawing input).periodicRegion tromino,
    (periodicRegion_computable tromino).comp
      reduction.drawing_computable, ?_⟩
  intro input
  rw [reduction.correct input]
  exact periodicRegion_correct_of_normalized tromino behavior
    (reduction.drawing input) (reduction.wellFormed input)
      (reduction.verticesSeparated input)

/-- The normalized orientation source-hardness interface implies 2D
co-r.e.-hardness for either tromino. -/
theorem periodicTrominoTiling_coREHard_of_normalizedOrientation
    (sourceHard : NormalizedOrientationCoREHard)
    (tromino : Tromino)
    (behavior : OrientationBehaviorCorrect tromino) :
    LeanWang.CoREHard (PeriodicTrominoTiling tromino) := by
  intro α _ source sourceCoRE
  obtain ⟨reduction⟩ := sourceHard source sourceCoRE
  exact normalizedOrientationReduction_manyOne reduction tromino behavior

/-- Once normalized periodic trichromatic orientation is proved co-r.e.-hard,
the already verified finite-obstruction upper bound completes the 2D half for
either tromino. -/
theorem periodicTrominoTiling_coREComplete_of_normalizedOrientation
    (sourceHard : NormalizedOrientationCoREHard)
    (tromino : Tromino)
    (behavior : OrientationBehaviorCorrect tromino) :
    LeanWang.CoREComplete (PeriodicTrominoTiling tromino) :=
  ⟨TrominoAssignment.periodicTrominoTiling_coRE tromino,
    periodicTrominoTiling_coREHard_of_normalizedOrientation
      sourceHard tromino behavior⟩

theorem lPeriodicTrominoTiling_coREComplete_of_normalizedOrientation
    (sourceHard : NormalizedOrientationCoREHard) :
    LeanWang.CoREComplete (PeriodicTrominoTiling .L) :=
  periodicTrominoTiling_coREComplete_of_normalizedOrientation
    sourceHard .L lOrientationBehaviorCorrect

theorem iPeriodicTrominoTiling_coREComplete_of_normalizedOrientation
    (sourceHard : NormalizedOrientationCoREHard) :
    LeanWang.CoREComplete (PeriodicTrominoTiling .I) :=
  periodicTrominoTiling_coREComplete_of_normalizedOrientation
    sourceHard .I iOrientationBehaviorCorrect

/-- The entire 2D conjunct of Theorem 5.2 now follows from the isolated
normalized-orientation source-hardness interface. -/
theorem theorem52_planeStatement_of_normalizedOrientation
    (sourceHard : NormalizedOrientationCoREHard) :
    Theorem52.planeStatement := by
  intro tromino
  cases tromino with
  | I =>
      exact iPeriodicTrominoTiling_coREComplete_of_normalizedOrientation
        sourceHard
  | L =>
      exact lPeriodicTrominoTiling_coREComplete_of_normalizedOrientation
        sourceHard

end Gadget
end LeanTrominoes
