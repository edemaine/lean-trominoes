import LeanTrominoes.PositionedPeriodicCNFRebasedRouteRadiusBounds
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalizationDrawing

/-!
# Variable-radius bounds through incidence-anchor normalization

Anchor normalization subtracts the clause anchor from every stored route
point and literal offset.  The later variable-side rebase adds back exactly
the complementary translation, so distance from the displayed physical
literal endpoint becomes distance from its variable prototype.
-/

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit

namespace PositionedPeriodicCNF

/-- A point bounded around a physical literal occurrence remains bounded
around the variable prototype after route normalization and the reverse
incidence rebase. -/
theorem withinCoordinateRadius_normalize_rebase
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (literal : PeriodicLiteral Variable)
    (anchor : Cell)
    {radius : Nat} {rawPoint : Cell}
    (bounded :
      WithinCoordinateRadius radius
        (placement.literalPosition literal) rawPoint) :
    WithinCoordinateRadius radius
      (placement.position literal.atom)
      (Cell.add
        (placement.translation
          (Cell.sub (0, 0)
            (literal.anchorNormalize anchor).offset))
        (Cell.sub rawPoint (placement.translation anchor))) := by
  have translated := bounded.translate
    (Cell.scale (-1) (placement.translation literal.offset))
  simpa [PeriodicVariablePlacement.literalPosition,
    PeriodicVariablePlacement.translation,
    PeriodicLiteral.anchorNormalize,
    Cell.add, Cell.sub, Cell.scale,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using translated

end PositionedPeriodicCNF
end LeanTrominoes
