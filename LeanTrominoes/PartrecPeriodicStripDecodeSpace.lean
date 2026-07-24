import LeanTrominoes.PartrecPeriodicStripDecode
import LeanTrominoes.PartrecUnpairSpace

/-!
# Evaluator-space certificate for periodic-strip header decoding

The certificate follows the two standard unpairing operations in the strip
encoding and preserves the decoded width with the direct list `prepend`
combinator.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def periodicStripHeaderTailCost (width rest : Nat) : Nat :=
  unpairCost rest + getCost 1 [width, rest]

theorem periodicStripHeaderTail
    (width rest : Nat) :
    EvaluatorCodeFits
      (Code.unpairCode.comp (Code.get 1))
      [width, rest] [rest.unpair.1, rest.unpair.2]
      (periodicStripHeaderTailCost width rest) := by
  simpa [periodicStripHeaderTailCost] using
    comp (unpair rest) (get 1 [width, rest])

def periodicStripHeaderRestCost
    (width period motifCode : Nat) : Nat :=
  prependCost
    [width, Nat.pair period motifCode] [width]
    [period, motifCode]
    (getCost 0 [width, Nat.pair period motifCode])
    (periodicStripHeaderTailCost width
      (Nat.pair period motifCode))

theorem periodicStripHeaderRest
    (width period motifCode : Nat) :
    EvaluatorCodeFits Code.periodicStripHeaderRestCode
      [width, Nat.pair period motifCode]
      [width, period, motifCode]
      (periodicStripHeaderRestCost width period motifCode) := by
  simpa [Code.periodicStripHeaderRestCode,
    periodicStripHeaderRestCost, prependCost] using
    prepend
      (get 0 [width, Nat.pair period motifCode])
      (periodicStripHeaderTail width
        (Nat.pair period motifCode))

def periodicStripHeaderCost
    (periodicStrip : PeriodicStrip) : Nat :=
  periodicStripHeaderRestCost periodicStrip.width
      periodicStrip.period
      (Encodable.encode periodicStrip.motif) +
    unpairCost (Encodable.encode periodicStrip)

theorem periodicStripHeader
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits Code.periodicStripHeaderCode
      [Encodable.encode periodicStrip]
      [periodicStrip.width, periodicStrip.period,
        Encodable.encode periodicStrip.motif]
      (periodicStripHeaderCost periodicStrip) := by
  have outer :
      EvaluatorCodeFits Code.unpairCode
        [Nat.pair periodicStrip.width
          (Nat.pair periodicStrip.period
            (Encodable.encode periodicStrip.motif))]
        [periodicStrip.width,
          Nat.pair periodicStrip.period
            (Encodable.encode periodicStrip.motif)]
        (unpairCost
          (Nat.pair periodicStrip.width
            (Nat.pair periodicStrip.period
              (Encodable.encode periodicStrip.motif)))) := by
    simpa using
      unpair
        (Nat.pair periodicStrip.width
          (Nat.pair periodicStrip.period
            (Encodable.encode periodicStrip.motif)))
  simpa [Code.periodicStripHeaderCode,
    periodicStripHeaderCost,
    PeriodicStrip.encode_eq_pair] using
    comp
      (periodicStripHeaderRest periodicStrip.width
        periodicStrip.period
        (Encodable.encode periodicStrip.motif))
      outer

end EvaluatorCodeFits

end PartrecToTM2
end Turing
