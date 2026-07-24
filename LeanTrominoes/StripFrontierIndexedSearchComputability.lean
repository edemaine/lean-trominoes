import LeanTrominoes.StripFrontierIndexedSearch
import LeanTrominoes.StripFrontierRawTransitionComputability

/-!
# Computability of indexed strip transitions

This file closes the compiler-facing transition layer: arithmetic state
indices are range-checked, decoded on demand, and passed to the
primitive-recursive raw frontier verifier.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState

theorem indexedTransitionRawBool_primrec (tromino : Tromino) :
    Primrec fun input : PeriodicStrip × Nat × Nat =>
      indexedTransitionRawBool tromino input.1 input.2.1 input.2.2 := by
  let strip : Primrec fun input : PeriodicStrip × Nat × Nat => input.1 :=
    Primrec.fst
  let first : Primrec fun input : PeriodicStrip × Nat × Nat => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let last : Primrec fun input : PeriodicStrip × Nat × Nat => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  let stateCount : Primrec fun input : PeriodicStrip × Nat × Nat =>
      indexCount input.1 :=
    indexCount_primrec.comp strip
  have firstBound : PrimrecPred fun input : PeriodicStrip × Nat × Nat =>
      input.2.1 < indexCount input.1 :=
    Primrec.nat_lt.comp first stateCount
  have lastBound : PrimrecPred fun input : PeriodicStrip × Nat × Nat =>
      input.2.2 < indexCount input.1 :=
    Primrec.nat_lt.comp last stateCount
  let firstState : Primrec fun input : PeriodicStrip × Nat × Nat =>
      ofIndex input.1 input.2.1 :=
    ofIndex_primrec.comp strip first
  let lastState : Primrec fun input : PeriodicStrip × Nat × Nat =>
      ofIndex input.1 input.2.2 :=
    ofIndex_primrec.comp strip last
  let transition : Primrec fun input : PeriodicStrip × Nat × Nat =>
      (ofIndex input.1 input.2.1).transitionBool tromino input.1
        (ofIndex input.1 input.2.2) :=
    (transitionBool_primrec tromino).comp
      (Primrec.pair strip
        (Primrec.pair firstState lastState))
  unfold indexedTransitionRawBool
  exact Primrec.ite firstBound
    (Primrec.ite lastBound transition (Primrec.const false))
    (Primrec.const false)

theorem indexedTransitionBool_primrec (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period) :
    Primrec₂ (indexedTransitionBool tromino periodicStrip periodPositive) := by
  change Primrec fun input : Nat × Nat =>
    indexedTransitionBool tromino periodicStrip periodPositive input.1 input.2
  unfold indexedTransitionBool
  exact (indexedTransitionRawBool_primrec tromino).comp
    (Primrec.pair (Primrec.const periodicStrip)
      (Primrec.pair Primrec.fst Primrec.snd))

end RawWindowState
end PeriodicStrip
end LeanTrominoes
