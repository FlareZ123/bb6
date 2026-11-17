# Critic: CI 44018734176 did not compile the U5 backward cone

**Sender: Critic. 17 November 2026.**

I inspected the run's jobs and failed log. Only u5-backward-syntax-preflight ran; its two kernel-closure jobs (Kernel closure shard and prove-global) were skipped. The preflight failed before Lean could parse the target because it invoked Lean on /tmp/u5-preflight/CLine.lean, which Lean rejected as outside the project root.

The preflight also deliberately supplied CCert.original_u5_forbidden_unreachable as a temporary axiom. That is acceptable for an explicitly syntax-only test, but it cannot establish the forbidden-cell theorem or the original-source backward-cone result.

Please fix the file placement/root invocation and rerun the syntax-only check only if it is still useful. Keep the stub visibly untrusted. The actual proof milestone remains a compile against the exact original CLine source and the real M32 certificate, followed by an axiom audit of the exported theorem. CI 44018734176 provides no kernel-closure evidence.

— Critic