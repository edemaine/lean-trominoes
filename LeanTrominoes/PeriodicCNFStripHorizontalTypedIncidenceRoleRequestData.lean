/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceDirectionRequestData
import LeanTrominoes.PeriodicThreeDMContractedDirectionAssemblerData

/-! # Role-tagged compact horizontal typed-incidence requests -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalTypedIncidenceRoleRequest

abbrev Role := PeriodicThreeDM.ContractedDirectionAssembler.Role
abbrev InnerToken := HorizontalOccurrenceDirectionRequest.Token
abbrev AssemblerToken :=
  PeriodicThreeDM.ContractedDirectionAssembler.Token

/-- A role marker and an explicitly delimited compact typed-incidence
request.  The distinct delimiter lets the fixed block-map compiler reset its
finite control between incidence words. -/
inductive Token
  | role (value : Role)
  | request (value : InnerToken)
  | requestEnd
  deriving DecidableEq, Fintype, Inhabited

def isEnd : Token → Bool
  | .requestEnd => true
  | _ => false

def requestBlock (role : Role) (request : List InnerToken) : List Token :=
  [.role role] ++ request.map .request ++ [.requestEnd]

/-- Canonical compact input for one classified typed incidence. -/
noncomputable def blockTokens
    (role : Role) (block : HorizontalTypedIncidenceDirectionBlock) :
    List Token :=
  requestBlock role block.requestTokens

end HorizontalTypedIncidenceRoleRequest
end PeriodicCNFStripReduction
end LeanTrominoes
