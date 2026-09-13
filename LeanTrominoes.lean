import LeanTrominoes.Theorem52Proof
import LeanTrominoes.PeriodicCNFPolySpaceHardness
import LeanTrominoes.Theorem55Proof
import LeanTrominoes.Theorem55StripProof
import LeanTrominoes.ThreeTranslationProof
import LeanTrominoes.TwoConnectedPolycubesSlabProof
import LeanTrominoes.TwoConnectedPolycubesSpaceProof
import LeanTrominoes.TwoConnectedPolycubesSlabsProof

/-!
# Main theorem interface

`Theorem52.proved` proves the complete plane and strip result, and
`Theorem52.stripProved` exposes strip PSPACE completeness. Import
`LeanTrominoes.Theorem52` separately to read only the target statements.
See README.md for the main declarations and PROOF_FRONTIER.md for the
completed construction and validation.

`Theorem55.planeProved` proves co-r.e. completeness of plane tiling by a fixed
connected 15-omino and an input disconnected polyomino, allowing rotations
and reflections. `Theorem55.stripProved` proves PSPACE completeness of the
corresponding strip problem under its original unary encoding. See
THEOREM55_FRONTIER.md for the construction and validation.

`ThreeTranslationPolyominoes.proved` proves Corollary 5.6: tiling by translations
of two fixed connected 15-ominoes and an input disconnected Q is co-r.e. complete
in the plane and PSPACE complete in strips. See TRANSLATION_FRONTIER.md.

`TwoConnectedPolycubes.slabTwoProved` proves co-r.e. completeness of tiling
the height-two slab with a fixed connected 15-voxel polycube and an input
connected polycube. `TwoConnectedPolycubes.spaceProved` proves full-space
co-r.e. completeness with a fixed connected 45-voxel polycube and an input
connected polycube. Both allow all cube rotations and reflections. See
POLYCUBE_FRONTIER.md.

`TwoConnectedPolycubes.slabsProved` proves co-r.e. completeness for every
fixed slab height greater than one. The fixed connected tile has at most
45 voxels, independently of the height.

This module is the public result interface. Lake's `LeanTrominoes.*` glob
checks every construction module independently of this import list.
-/
