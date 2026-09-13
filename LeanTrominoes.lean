import LeanTrominoes.Theorem52Proof
import LeanTrominoes.PeriodicCNFPolySpaceHardness
import LeanTrominoes.Theorem55Proof
import LeanTrominoes.TwoConnectedPolycubesSlabProof

/-!
# Main theorem interface

`Theorem52.proved` proves the complete plane and strip result, and
`Theorem52.stripProved` exposes strip PSPACE completeness. Import
`LeanTrominoes.Theorem52` separately to read only the target statements.
See README.md for the main declarations and PROOF_FRONTIER.md for the
completed construction and validation.

`Theorem55.planeProved` proves co-r.e. completeness of plane tiling by a fixed
connected 15-omino and an input disconnected polyomino, allowing rotations
and reflections. The strip assertion remains open. See THEOREM55_FRONTIER.md
for the construction and validation.

`TwoConnectedPolycubes.slabTwoProved` proves co-r.e. completeness of tiling
the height-two slab with a fixed connected 15-voxel polycube and an input
connected polycube, allowing all cube rotations and reflections. Full-space
hardness remains open; see POLYCUBE_FRONTIER.md.

This module is the public result interface. Lake's `LeanTrominoes.*` glob
checks every construction module independently of this import list.
-/
