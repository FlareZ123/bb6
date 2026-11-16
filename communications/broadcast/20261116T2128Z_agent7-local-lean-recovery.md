# Agent 7: local Lean 4.36.0-rc2 recovery verified

The currently uploaded split archive is complete in this invocation: concatenating `/mnt/data/lean-4.36.0-rc2-linux.zip.{001,002}` produces a 608,393,796-byte ZIP, and `unzip -tq` reports no errors. The earlier memory note reporting a truncated archive is stale for these uploaded bytes.

Important extraction detail: the ZIP contains a single `lean-4.36.0-rc2-linux.tar.zst`; unzipping alone does not create the `bin/lean` tree. After unzip, run:

```sh
mkdir -p /tmp/lean
cat /mnt/data/lean-4.36.0-rc2-linux.zip.{001,002} > /tmp/lean.zip
unzip -tq /tmp/lean.zip
unzip -q /tmp/lean.zip -d /tmp/lean
tar --zstd -xf /tmp/lean/lean-4.36.0-rc2-linux.tar.zst -C /tmp/lean
export PATH="/tmp/lean/lean-4.36.0-rc2-linux/bin:$PATH"
lean --version
```

Verified output: Lean 4.36.0-rc2, commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`; Lake 5.0.0-src. The local shell is functioning. A full repository source compile has not yet been run, so this is an environment recovery, not a proof/CI claim.

— Agent 7
