/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokenParserLength

/-! # Quadratic scan bound for sparse assignment-token parsing -/

namespace LeanTrominoes

namespace GadgetSparseAssignmentTokenMachine

/-- Adding one per-token cost extends the uniform suffix bound by one input
position. -/
theorem add_cost_le_next_bound (rest cost tailLength limit : Nat)
    (restLe : rest ≤ 256 * (tailLength + 1) * (limit + 1))
    (costLe : cost ≤ 256 * (limit + 1)) :
    rest + cost ≤ 256 * (tailLength + 2) * (limit + 1) := by
  calc
    rest + cost ≤
        256 * (tailLength + 1) * (limit + 1) +
          256 * (limit + 1) := Nat.add_le_add restLe costLe
    _ = 256 * (tailLength + 2) * (limit + 1) := by ring

/-- The full fixed-mask processing cost fits one uniform per-token budget. -/
theorem cell_cost_le (tromino : Tromino)
    (cellType : Gadget.OrthogonalCellType)
    (horizontal vertical limit : Nat) (coordinateLe : horizontal + vertical ≤ limit) :
    1 + pixelsTime horizontal vertical (boundedPixels tromino cellType) +
        (horizontal + vertical + 2) + 1 ≤
      256 * (limit + 1) := by
  have lengthBound := boundedPixels_length_le tromino cellType
  have productBound := Nat.mul_le_mul_right (pixelTime horizontal vertical)
    lengthBound
  have pixelsBound :
      pixelsTime horizontal vertical (boundedPixels tromino cellType) ≤
        36 * pixelTime horizontal vertical + 1 := by
    rw [pixelsTime_eq]
    omega
  unfold pixelTime at pixelsBound
  omega

/-- With a fixed mass limit, every remaining token consumes at most one
uniform budget unit. -/
theorem scanTime_le_of_mass (tromino : Tromino) (phase : Phase)
    (horizontal vertical : Nat) (tokens : List InputToken) (limit : Nat)
    (massLe : horizontal + phaseVertical phase vertical + tokens.length ≤ limit) :
    scanTime tromino phase horizontal vertical tokens ≤
      256 * (tokens.length + 1) * (limit + 1) := by
  induction tokens generalizing phase horizontal vertical with
  | nil =>
      cases phase with
      | horizontal =>
          simp [phaseVertical] at massLe
          simp [scanTime]
          omega
      | vertical =>
          simp [phaseVertical] at massLe
          simp [scanTime]
          omega
  | cons token tokens induction =>
      cases phase with
      | horizontal =>
          cases token with
          | coordinateUnit =>
              have rest := induction .horizontal (horizontal + 1) 0 (by
                simp [phaseVertical] at massLe ⊢
                omega)
              have combined := add_cost_le_next_bound
                (scanTime tromino .horizontal (horizontal + 1) 0 tokens) 1
                tokens.length limit rest (by omega)
              simpa [scanTime] using combined
          | fieldEnd =>
              have rest := induction .vertical horizontal 0 (by
                simp [phaseVertical] at massLe ⊢
                omega)
              have combined := add_cost_le_next_bound
                (scanTime tromino .vertical horizontal 0 tokens) 1
                tokens.length limit rest (by omega)
              simpa [scanTime] using combined
          | cellType cellType =>
              have rest := induction .horizontal 0 0 (by
                simp [phaseVertical] at massLe ⊢
                omega)
              have costLe : horizontal + 2 + 1 ≤ 256 * (limit + 1) := by
                simp [phaseVertical] at massLe
                omega
              have combined := add_cost_le_next_bound
                (scanTime tromino .horizontal 0 0 tokens)
                (horizontal + 2 + 1) tokens.length limit rest costLe
              simpa [scanTime] using combined
      | vertical =>
          cases token with
          | coordinateUnit =>
              have rest := induction .vertical horizontal (vertical + 1) (by
                simp [phaseVertical] at massLe ⊢
                omega)
              have combined := add_cost_le_next_bound
                (scanTime tromino .vertical horizontal (vertical + 1) tokens) 1
                tokens.length limit rest (by omega)
              simpa [scanTime] using combined
          | fieldEnd =>
              have rest := induction .horizontal 0 0 (by
                simp [phaseVertical] at massLe ⊢
                omega)
              have costLe :
                  horizontal + vertical + 2 + 1 ≤ 256 * (limit + 1) := by
                simp [phaseVertical] at massLe
                omega
              have combined := add_cost_le_next_bound
                (scanTime tromino .horizontal 0 0 tokens)
                (horizontal + vertical + 2 + 1) tokens.length limit rest costLe
              simpa [scanTime] using combined
          | cellType cellType =>
              have rest := induction .horizontal 0 0 (by
                simp [phaseVertical] at massLe ⊢
                omega)
              have coordinatesLe : horizontal + vertical ≤ limit := by
                simp [phaseVertical] at massLe
                omega
              have costLe := cell_cost_le tromino cellType horizontal vertical
                limit coordinatesLe
              have combined := add_cost_le_next_bound
                (scanTime tromino .horizontal 0 0 tokens)
                (1 + pixelsTime horizontal vertical
                    (boundedPixels tromino cellType) +
                  (horizontal + vertical + 2) + 1)
                tokens.length limit rest costLe
              simpa [scanTime] using combined

/-- Starting from empty counters, parsing is bounded by a quadratic in input
length. -/
theorem scanTime_start_le (tromino : Tromino) (tokens : List InputToken) :
    scanTime tromino .horizontal 0 0 tokens ≤
      256 * (tokens.length + 1) ^ 2 := by
  have bound := scanTime_le_of_mass tromino .horizontal 0 0 tokens
    tokens.length (by simp [phaseVertical])
  convert bound using 1
  ring

end GadgetSparseAssignmentTokenMachine
end LeanTrominoes
