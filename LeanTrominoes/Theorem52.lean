import LeanTrominoes.Complexity
import LeanTrominoes.Periodic
import LeanWang.Final

/-!
# Theorem 5.2 target

This file records the exact proposition to be proved and deliberately contains
only definitions, not a proof of any part of the target.
-/

namespace LeanTrominoes.Theorem52

/-- The 2D assertion of Theorem 5.2, separately for each tromino. -/
def planeStatement : Prop :=
  ∀ tromino : Tromino, LeanWang.CoREComplete (PeriodicTrominoTiling tromino)

/-- The 1.5D assertion of Theorem 5.2, separately for each tromino. -/
def stripStatement : Prop :=
  ∀ tromino : Tromino,
    Complexity.PSPACEComplete
      (Complexity.primcodableFinEncoding PeriodicStripSpec)
      (PeriodicStripTrominoTiling tromino)

/-- The complete formal target corresponding to Theorem 5.2. -/
def statement : Prop :=
  planeStatement ∧ stripStatement

end LeanTrominoes.Theorem52
