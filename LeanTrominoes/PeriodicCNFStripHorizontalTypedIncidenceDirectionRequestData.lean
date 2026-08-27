/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceDirectionRequestSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceDirectionBlock

/-! # Compact requests for complete horizontal typed incidences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open HorizontalOccurrenceDirectionRequest
open PlanarThreeDM

/-- Finite query selecting the local prefix of one variable incidence. -/
def horizontalVariableIncidencePrefixDirectionQuery
    (input : HorizontalVariableIncidencePrefixInput) :
    HorizontalFiniteIncidenceDirectionQuery :=
  .variable
    (horizontalVariableIncidenceLocalRouteInputComputed input).1
    (horizontalVariableIncidenceLocalRouteInputComputed input).2.1
    (horizontalVariableIncidenceLocalRouteInputComputed input).2.2

/-- Finite query selecting one clause-core incidence. -/
def horizontalClauseIncidenceDirectionQuery
    (input : X3CClauseSet × Gadget.WireColor) :
    HorizontalFiniteIncidenceDirectionQuery :=
  .clause input.1 input.2

namespace HorizontalTypedIncidenceDirectionBlock

/-- Compact request consumed by the fixed occurrence transducer.  A local
variable incidence contains only its finite prefix; a routed one appends the
complete compact occurrence request; a clause incidence is one finite query. -/
def requestTokens : HorizontalTypedIncidenceDirectionBlock →
    List HorizontalOccurrenceDirectionRequest.Token
  | .variable input .local =>
      [.finite (horizontalVariableIncidencePrefixDirectionQuery
        (horizontalVariableRoutePrefixQueryComputed input))]
  | .variable input (.routed occurrence) =>
      .finite (horizontalVariableIncidencePrefixDirectionQuery
          (horizontalVariableRoutePrefixQueryComputed input)) ::
        horizontalOccurrenceDirectionRequestTokens
          (horizontalVariableOccurrenceRouteQueryComputed input)
          occurrence
  | .clause input =>
      [.finite (horizontalClauseIncidenceDirectionQuery input)]

/-- Interpreting a compact typed-incidence request gives exactly the direction
word of its classified semantic block. -/
@[simp] theorem output_requestTokens
    (block : HorizontalTypedIncidenceDirectionBlock) :
    HorizontalOccurrenceDirectionRequest.output block.requestTokens =
      block.directions := by
  cases block with
  | «variable» input block =>
      cases block with
      | «local» =>
          rw [requestTokens, output_finite_cons]
          simp only [HorizontalOccurrenceDirectionRequest.output,
            FiniteStateTransducer.output, FiniteStateTransducer.scan,
            HorizontalOccurrenceDirectionRequest.finish, List.append_nil]
          exact
            HorizontalFiniteIncidenceDirectionQuery.directions_variable_input
              (horizontalVariableRoutePrefixQueryComputed input)
      | routed occurrence =>
          rw [requestTokens, output_finite_cons,
            output_horizontalOccurrenceDirectionRequestTokens]
          change
            (horizontalVariableIncidencePrefixDirectionQuery
                (horizontalVariableRoutePrefixQueryComputed input)).directions ++
                horizontalOccurrenceCoordinatedDirections
                  (horizontalVariableOccurrenceRouteQueryComputed input)
                  occurrence =
              horizontalVariableIncidencePrefixDirections
                  (horizontalVariableRoutePrefixQueryComputed input) ++
                horizontalOccurrenceCoordinatedDirections
                  (horizontalVariableOccurrenceRouteQueryComputed input)
                  occurrence
          unfold horizontalVariableIncidencePrefixDirectionQuery
          rw [HorizontalFiniteIncidenceDirectionQuery.directions_variable_input]
  | clause input =>
      rw [requestTokens, output_finite_cons]
      simp only [HorizontalOccurrenceDirectionRequest.output,
        FiniteStateTransducer.output, FiniteStateTransducer.scan,
        HorizontalOccurrenceDirectionRequest.finish, List.append_nil]
      exact
        HorizontalFiniteIncidenceDirectionQuery.directions_clause_input input

end HorizontalTypedIncidenceDirectionBlock

end PeriodicCNFStripReduction
end LeanTrominoes

end
