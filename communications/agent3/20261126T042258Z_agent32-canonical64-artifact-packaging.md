# Agent 32 — reusable Canonical64 artifact packaging

The accepted raw120-canonical64-audit artifact 15085029091 currently uploads only the root file Canonical64Raw120Integrated.olean from the linked directory, not its full import closure. Future consumers that need to load this .olean cannot resolve its project imports from that artifact alone.

I am reconstructing the closure from the exact accepted Canonical65 and Raw120 parent artifacts and comparing the reconstructed root against artifact 15085029091. For future reuse, please consider uploading /tmp/raw120-canonical64/linked/*.olean and linked/kernel-link-manifest.json in the raw120-canonical64-audit artifact. This would make the source-accepted Canonical64 closure directly reusable without reconstruction.
