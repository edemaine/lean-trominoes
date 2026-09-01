/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookupSemantics
import LeanTrominoes.PeriodicCNFStripKeyedContractedIncidenceCompiler

/-! # Semantics of keyed contracted-incidence assembly -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace KeyedContractedIncidence

open PeriodicThreeDM

@[simp] theorem roleTokens_eq_blocks
    (roles : List ContractedDirectionAssembler.Role) :
    roleTokens roles =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (roles.map fun role => [.role role]) := by
  unfold roleTokens FiniteAlphabetDelimitedBlockJoin.blocks
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro role _
  rfl

@[simp] theorem directionTokens_blocks
    (directions : List (List AxisDirection)) :
    directionTokens
        (FiniteAlphabetDelimitedBlockJoin.blocks directions) =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (directions.map fun word =>
          word.map ContractedDirectionAssembler.Token.direction) := by
  unfold directionTokens FiniteAlphabetDelimitedBlockJoin.blocks
  rw [List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro word _
  unfold FiniteAlphabetDelimitedBlockJoin.block
  simp only [List.flatMap_append, List.flatMap_map,
    List.flatMap_cons, List.flatMap_nil, directionBlock,
    List.append_nil]
  rw [← List.map_eq_flatMap]
  simp [List.map_map, Function.comp_def]

@[simp] theorem assemblerTokens_blocks
    (bodies : List (List ContractedDirectionAssembler.Token)) :
    assemblerTokens
        (FiniteAlphabetDelimitedBlockJoin.blocks bodies) =
      bodies.flatMap fun body => body ++ [.incidenceEnd] := by
  unfold assemblerTokens FiniteAlphabetDelimitedBlockJoin.blocks
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro body _
  unfold FiniteAlphabetDelimitedBlockJoin.block
  simp [assemblerBlock, List.flatMap_map]

private theorem map_fst_zip_of_length_eq
    {First Second : Type} (firsts : List First) (seconds : List Second)
    (lengthEq : firsts.length = seconds.length) :
    (firsts.zip seconds).map Prod.fst = firsts := by
  exact List.map_fst_zip (by omega)

private theorem map_snd_zip_of_length_eq
    {First Second : Type} (firsts : List First) (seconds : List Second)
    (lengthEq : firsts.length = seconds.length) :
    (firsts.zip seconds).map Prod.snd = seconds := by
  exact List.map_snd_zip (by omega)

/-- Pointwise block joining prepends each aligned role to its selected
incidence word and preserves one incidence delimiter. -/
theorem inputTokens_of_selected_blocks
    (queries blockKeys : List Nat)
    (incidences : List DirectionToken)
    (roles : List ContractedDirectionAssembler.Role)
    (directions : List (List AxisDirection))
    (selected :
      FiniteAlphabetKeyedDelimitedBlockLookup.selected
          queries blockKeys incidences =
        FiniteAlphabetDelimitedBlockJoin.blocks directions)
    (aligned : roles.length = directions.length) :
    inputTokens queries roles blockKeys incidences =
      (roles.zip directions).flatMap fun pair =>
        ContractedDirectionAssembler.roleBlock pair.1 pair.2 := by
  unfold inputTokens
  rw [selected, roleTokens_eq_blocks,
    directionTokens_blocks]
  let pairs := roles.zip directions
  have firsts : pairs.map Prod.fst = roles :=
    map_fst_zip_of_length_eq roles directions aligned
  have seconds : pairs.map Prod.snd = directions :=
    map_snd_zip_of_length_eq roles directions aligned
  let blockPairs := pairs.map fun pair =>
    ([ContractedDirectionAssembler.Token.role pair.1],
      pair.2.map ContractedDirectionAssembler.Token.direction)
  have joined :=
    FiniteAlphabetDelimitedBlockJoin.joined_pairedBlocks
      (Alphabet := ContractedDirectionAssembler.Token)
      blockPairs
  have joined' :
      FiniteAlphabetDelimitedBlockJoin.joined
          (FiniteAlphabetDelimitedBlockJoin.blocks
            (roles.map fun role => [.role role]))
          (FiniteAlphabetDelimitedBlockJoin.blocks
            (directions.map fun word =>
              word.map ContractedDirectionAssembler.Token.direction)) =
        FiniteAlphabetDelimitedBlockJoin.blocks
          (pairs.map fun pair =>
            [ContractedDirectionAssembler.Token.role pair.1] ++
              pair.2.map ContractedDirectionAssembler.Token.direction) := by
    rw [← firsts, ← seconds]
    simpa [blockPairs, List.map_map, Function.comp_def] using joined
  rw [joined', assemblerTokens_blocks]
  change
    (pairs.map fun pair =>
      [ContractedDirectionAssembler.Token.role pair.1] ++
        pair.2.map ContractedDirectionAssembler.Token.direction).flatMap
        (fun body => body ++ [.incidenceEnd]) =
      pairs.flatMap fun pair =>
        ContractedDirectionAssembler.roleBlock pair.1 pair.2
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro pair _
  simp [ContractedDirectionAssembler.roleBlock]

/-- Under exact keyed block selection, the compiler is precisely the
established contracted assembler on the requested role/direction pairs. -/
theorem output_of_selected_blocks
    (queries blockKeys : List Nat)
    (incidences : List DirectionToken)
    (roles : List ContractedDirectionAssembler.Role)
    (directions : List (List AxisDirection))
    (selected :
      FiniteAlphabetKeyedDelimitedBlockLookup.selected
          queries blockKeys incidences =
        FiniteAlphabetDelimitedBlockJoin.blocks directions)
    (aligned : roles.length = directions.length) :
    output queries roles blockKeys incidences =
      ContractedDirectionAssembler.output
        ((roles.zip directions).flatMap fun pair =>
          ContractedDirectionAssembler.roleBlock pair.1 pair.2) := by
  unfold output
  rw [inputTokens_of_selected_blocks queries blockKeys incidences
    roles directions selected aligned]

end KeyedContractedIncidence
end PeriodicCNFStripReduction
end LeanTrominoes

end
