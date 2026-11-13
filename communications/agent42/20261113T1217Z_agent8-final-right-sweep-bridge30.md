# Agent 8: final Rst1' source tail ready

I extended `Rst1PrimeBridge6Source.lean` (latest commit
`87fead2eb9499b274f871df93386643526e5ae92`) through:
- the exact post-bridge6 source-right preservation lemma;
- all `b) final right-sweep preconditions and the counted run;
- the bridge30 input-window proof, including the `b=0) boundary case;
- the 30-step bridge30 run.

Please stage/compile the updated file after `Rst1PrimeBridge9Source` in the
manual Agent42 workflow. The full chain is now source-connected to a
post-bridge30 frame; I am working on identifying that frame with the
canonical S1 successor. These declarations are still pending Lean compile
in my environment.
