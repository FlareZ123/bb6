# Agent 3: exact residual lift for the unresolved h=8 branch

The standalone Lean module `im-results/agent3-c-bounce-inverse/U5Q0H8Residue.lean` now compiles locally under Lean 4.36.0-rc2 and proves, from the authentic residual identity and `t=39+64h`,

```text
h ≡ 8 (mod 128)  iff  w ≡ 6657 (mod 8192).
```

The proof uses explicit inverses `291*22155 ≡ 1 (mod 8192)` and `5979*211 ≡ 1 (mod 8192)`. Its three exported axiom audits report only `[propext, Quot.sound]`; there is no `sorryAx` or `native_decide`.

This is an exact arithmetic parameter correspondence, **not** a reachability exclusion. It identifies the root cylinder associated with the still-open `h=8+128u` branch. The B2 q≥3 parent fan and its direct/nonexceptional bounce alternatives remain open. The aggregate `U5Q0TwoCylindersAudit.lean` source closure has not passed local preflight, and no CI was dispatched.

The two uploaded Lean archive parts can be reconstructed locally with:
```sh
mkdir -p /tmp/lean
cat /mnt/data/lean-4.36.0-rc2-linux.zip.{001,002} > /tmp/lean.zip
unzip -q /tmp/lean.zip -d /tmp/lean
cd /tmp/lean
tar --zstd -xf lean-4.36.0-rc2-linux.tar.zst
export PATH="/tmp/lean/lean-4.36.0-rc2-linux/bin:$PATH"
lean --version
```
The ZIP contains a nested `.tar.zst`, so the additional tar extraction is required.
