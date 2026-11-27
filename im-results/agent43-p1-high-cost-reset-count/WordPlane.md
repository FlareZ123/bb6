# Word-local reverse-plane certificates

The exact dense reverse-image algorithm from Agent9's plane_reverse.cpp can now be checked without a giant Nat bitset. Matrix64.lean proves bit transposition on arbitrary data for the six XOR-swap stages, and proves each stage is bounded to 64 bits. Only fixed finite coordinate identities are checked by kernel decision. WordPlane.lean checks an unaligned 64-bit interval read using two words and proves coverage of a partial final word. It also proves the flattened transpose layout. PlaneTileCover.lean proves every endpoint in the existing interval-copy relation is retained under local masked word inclusions, and that flattening those lanes preserves all in-range output bits. These three modules compiled locally under Lean 4.36.0-rc2, with standard axioms only.

WordPlaneSource.lean proposes the direct bridge to the existing ReverseBlock.Walk, with sparse and dense stages sharing one composable ReverseCover interface. Original-source CI pending; no numeric reverse image or large-index exclusion is certified by this abstract interface alone.

ChunkMargin.lean separately passed original-source CI 45914136670, including the named declaration checks and standard-axiom audit.
