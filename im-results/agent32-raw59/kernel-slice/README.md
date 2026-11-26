# Kernel-declaration slicing across incompatible width-two implementations

The existing Raw59 1LB source certificate (artifact 15082588050) and the accepted Raw119 parent (artifact 15087741037) use different BlockMacro2 kernel declarations. Raw119 has legacy BlockMacro2 hash 6b37811404cf84e22543a793d750d8b2222b8e9be1ba3840ff3edb1b315b16fb, matching the canonical environment; Raw59 uses 96741c90f72d33271b4cbd7ad7dc8e39de04ded8fcf3d62300d3c64c057c8274. A native Lean utility extracts only the constants needed for an existing proof, preserving identical base declarations and relocating differing declarations and their reverse-dependent proof terms. It replays the transformed declarations in the trust-level-zero kernel and exports checked additions. A separate ordinary Lean consumer verifies the exact literal machine table and proves the intended NeverHalts proposition. This is kernel replay of source-certified proof terms, not source re-elaboration.

## Actual pilot, Lean 4.36.0-rc2

- Producer: accepted Raw59 1LB ZIP artifact 15082588050, SHA256 45a1fcc14767df503e0e5fc6cfe43a02aa51530a6c9d3773831888e482379ff4.
- Base: accepted Raw119 ZIP artifact 15087741037, SHA256 b6997b8b530e59357bf8deabbc295f51f03b85567b99773b2fa91248ca3be235.
- 123 producer modules, 15,951 declarations indexed, 589 reached, 233 relocated/replayed.
- Native replay: 4.55 s wall, maximum RSS 1,469,512 KiB. Output SHA256 128b952f7ef64418be7b261580f706f0c804838ae61c2e1ed2c86aa0ded7724d.
- BridgeConsumer.lean: checked the literal partial machine 1RB1LB_1RC0LB_0RD0RF_1LD1RE_1RD1LA_---1RA against the relocated proof of nonhalting for every compatible completion, with the original legacy BlockFAR2 also imported. 1.12 s; maximum RSS 1,624,692 KiB. Axioms exact_table: propext, Quot.sound. Axioms never: propext, Classical.choice, Quot.sound.
- The full Raw119 test was deliberately stopped after identifying 28,983 declarations to relocate; it is not a completed proof. Full Raw59 1LB replay is in progress at this checkpoint. This pilot repairs portability of a previously accepted leaf and does not close a new machine or reduce the canonical roster.

Run reproduce.sh with the two exact ZIPs and the pinned Lean toolchain on PATH. The full parent Raw59 proof is the next acceptance target. The utility refuses new axioms, unsafe or partial dependencies, unsupported split modules, incompatible duplicate producer declarations and missing nonstandard dependencies. The downstream literal-table equality and weighted Cover theorem are mandatory gates.
