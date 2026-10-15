/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computation.Encoding.Binary.BinaryRouteTailRecordProfileFramingData
import LeanTrominoes.Computation.Encoding.Delimited.DelimitedRouteJoinTime
import LeanTrominoes.Complexity.FiniteStateTransducerTime
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Compiler for profile-framed aligned four-route streams -/

noncomputable section

namespace LeanTrominoes
namespace BinaryRouteTailRecordProfileFraming

open Computability Turing

noncomputable def profilePrefixesComputableInPolyTime :
    TM2ComputableInPolyTime id id prefixOutput :=
  FiniteStateTransducer.computableInPolyTime
    PrefixControl.empty prefixTransition prefixFinish

noncomputable def decodeOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id decodeOutput :=
  FiniteStateTransducer.computableInPolyTime
    decodeInitial decodeTransition decodeFinish

noncomputable def recordProfilesComputableInPolyTime :
    TM2ComputableInPolyTime id id recordProfiles :=
  FiniteBlockTransducer.computableInPolyTime recordProfileBlock

/-- Two same-input compilers, one for the finite clause profiles and one for
four-route direction blocks, can be framed in polynomial time. -/
noncomputable def framedComputableInPolyTimeOf
    {Source SourceSymbol : Type}
    [Fintype SourceSymbol] [Inhabited SourceSymbol]
    (encodeSource : Source → List SourceSymbol)
    (profiles : Source → List Profile)
    (routes : Source → List RouteToken)
    (profileCompiler : TM2ComputableInPolyTime
      encodeSource id profiles)
    (routeCompiler : TM2ComputableInPolyTime
      encodeSource id routes) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => framed (profiles source) (routes source)) := by
  let prefixes := TM2CompositionMachine.computableInPolyTime
    profileCompiler profilePrefixesComputableInPolyTime
  let joined := DelimitedRouteJoin.joinedComputableInPolyTimeOf
    encodeSource
    (fun source => prefixOutput (profiles source))
    routes prefixes routeCompiler
  exact TM2CompositionMachine.computableInPolyTime
    joined decodeOutputComputableInPolyTime

end BinaryRouteTailRecordProfileFraming
end LeanTrominoes

end
