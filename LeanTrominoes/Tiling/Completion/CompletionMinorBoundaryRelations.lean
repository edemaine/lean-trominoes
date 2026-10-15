/- Generated boundary-profile consequences; masks list top-left, top-right, bottom-left, bottom-right. -/
import LeanTrominoes.Tiling.Completion.CompletionIEqBoundary
import LeanTrominoes.Tiling.Completion.CompletionINegBoundary
import LeanTrominoes.Tiling.Completion.CompletionIPlugTopBoundary
import LeanTrominoes.Tiling.Completion.CompletionIPlugBotBoundary
import LeanTrominoes.Tiling.Completion.CompletionIFillBoundary
import LeanTrominoes.Tiling.Completion.CompletionLEqBoundary
import LeanTrominoes.Tiling.Completion.CompletionLNegBoundary
import LeanTrominoes.Tiling.Completion.CompletionLPlugTopBoundary
import LeanTrominoes.Tiling.Completion.CompletionLPlugBotBoundary
import LeanTrominoes.Tiling.Completion.CompletionLFillBoundary

namespace LeanTrominoes.CompletionPattern

theorem i_eq_boundary (i : Fin 16) :
    IEqBoundary.pattern.Completable (IEqBoundary.outside i) ↔ i = 3 ∨ i = 6 ∨ i = 9 ∨ i = 12 := by
  rw [IEqBoundary.completable_iff]
  revert i
  decide +kernel

theorem i_neg_boundary (i : Fin 16) :
    INegBoundary.pattern.Completable (INegBoundary.outside i) ↔ i = 5 ∨ i = 10 := by
  rw [INegBoundary.completable_iff]
  revert i
  decide +kernel

theorem i_plugtop_boundary (i : Fin 16) :
    IPlugTopBoundary.pattern.Completable (IPlugTopBoundary.outside i) ↔ i = 9 ∨ i = 10 := by
  rw [IPlugTopBoundary.completable_iff]
  revert i
  decide +kernel

theorem i_plugbot_boundary (i : Fin 16) :
    IPlugBotBoundary.pattern.Completable (IPlugBotBoundary.outside i) ↔ i = 5 ∨ i = 9 := by
  rw [IPlugBotBoundary.completable_iff]
  revert i
  decide +kernel

theorem i_fill_boundary (i : Fin 16) :
    IFillBoundary.pattern.Completable (IFillBoundary.outside i) ↔ i = 9 := by
  rw [IFillBoundary.completable_iff]
  revert i
  decide +kernel

theorem l_eq_boundary (i : Fin 16) :
    LEqBoundary.pattern.Completable (LEqBoundary.outside i) ↔ i = 3 ∨ i = 6 ∨ i = 9 ∨ i = 12 := by
  rw [LEqBoundary.completable_iff]
  revert i
  decide +kernel

theorem l_neg_boundary (i : Fin 16) :
    LNegBoundary.pattern.Completable (LNegBoundary.outside i) ↔ i = 5 ∨ i = 10 := by
  rw [LNegBoundary.completable_iff]
  revert i
  decide +kernel

theorem l_plugtop_boundary (i : Fin 16) :
    LPlugTopBoundary.pattern.Completable (LPlugTopBoundary.outside i) ↔ i = 9 ∨ i = 10 := by
  rw [LPlugTopBoundary.completable_iff]
  revert i
  decide +kernel

theorem l_plugbot_boundary (i : Fin 16) :
    LPlugBotBoundary.pattern.Completable (LPlugBotBoundary.outside i) ↔ i = 5 ∨ i = 9 := by
  rw [LPlugBotBoundary.completable_iff]
  revert i
  decide +kernel

theorem l_fill_boundary (i : Fin 16) :
    LFillBoundary.pattern.Completable (LFillBoundary.outside i) ↔ i = 9 := by
  rw [LFillBoundary.completable_iff]
  revert i
  decide +kernel

end LeanTrominoes.CompletionPattern
