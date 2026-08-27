/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierBendRouteTailRecordData
import LeanTrominoes.PeriodicOrthocrossingCarrierSpanRouteDirectionDecoderData

/-! # Formatting four complete binary-clause routes as flat tail records -/

namespace LeanTrominoes
namespace BinaryRouteTailRecordFormatter

open PeriodicCNF
open PeriodicCNFStripReduction

abbrev SourceToken :=
  PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken

abbrev Token := HorizontalRoutedRouteTailRecord.Token

inductive Control
  | firstHead
  | firstTail
  | secondHead
  | secondTail
  | thirdHead
  | thirdTail
  | fourthHead
  | fourthTail
  | done
  deriving DecidableEq, Fintype, Inhabited

/-- Delete the first direction of each complete route, tag the remaining
directions by binary source slot, and insert the two clause profiles and
boundaries. -/
def transition
    (firstProfile secondProfile :
      FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    Control → SourceToken → Control × List Token
  | .firstHead, .direction _ =>
      (.firstTail, [.profile firstProfile])
  | .firstHead, .routeEnd =>
      (.secondHead, [.profile firstProfile])
  | .firstTail, .direction direction =>
      (.firstTail, [.direction .first direction])
  | .firstTail, .routeEnd => (.secondHead, [])
  | .secondHead, .direction _ => (.secondTail, [])
  | .secondHead, .routeEnd => (.thirdHead, [.clauseEnd])
  | .secondTail, .direction direction =>
      (.secondTail, [.direction .second direction])
  | .secondTail, .routeEnd => (.thirdHead, [.clauseEnd])
  | .thirdHead, .direction _ =>
      (.thirdTail, [.profile secondProfile])
  | .thirdHead, .routeEnd =>
      (.fourthHead, [.profile secondProfile])
  | .thirdTail, .direction direction =>
      (.thirdTail, [.direction .first direction])
  | .thirdTail, .routeEnd => (.fourthHead, [])
  | .fourthHead, .direction _ => (.fourthTail, [])
  | .fourthHead, .routeEnd => (.done, [.clauseEnd])
  | .fourthTail, .direction direction =>
      (.fourthTail, [.direction .second direction])
  | .fourthTail, .routeEnd => (.done, [.clauseEnd])
  | .done, _ => (.done, [])

def finish (_ : Control) : List Token := []

def output
    (firstProfile secondProfile :
      FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (input : List SourceToken) : List Token :=
  FiniteStateTransducer.output .firstHead
    (transition firstProfile secondProfile) finish input

end BinaryRouteTailRecordFormatter
end LeanTrominoes
