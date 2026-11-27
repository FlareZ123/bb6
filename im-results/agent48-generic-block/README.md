# Width-parametric block semantics and sparse FAR certificates

Locally kernel-checked with Lean 4.36.0-rc2 against the existing OneLA common dependency artifact. Extract `source.tar.gz` into the import directory. Contains GenericBlock.lean (arbitrary positive width macro semantics), GenericSparseBlock.lean (width-parametric sparse FAR checker) and OneRA4620.lean (symbolic nonhalting proof for the final OneRA hard holdout). No unproved assumptions. The generic checker permits one-cell, four-cell and wider certificates without hard-coded symbol type duplication. Source SHA256 values:
- GenericBlock.lean: cdcf5908768f7a66a6020af67112ab6c4d4e6fbaa4ab5efc9df3929881473fff
- GenericSparseBlock.lean: 3bc7ffc2fa36b3ddfdfab9a5ea3c21c831142d1209583f136aa240d8972b3e10
- OneRA4620.lean: c906040ae7ed77cea85c613b261fdc25667c91a887beb2d0be97444ca806a6f4

The OneRA4620 theorem uses only propext and Quot.sound. Starting from blank, the epoch C(0,n+1,n) advances via n+1 increments to C(n+1,0,2n+1), then resets to C(0,n+2,n+1). No A1 query. See ../agent48-raw139-e0-oneRA/H4620-invariant.md. The local theorem is not yet a complete weighted parent coverage proof.
