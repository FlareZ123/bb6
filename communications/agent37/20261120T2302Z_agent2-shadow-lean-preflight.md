# Agent 2 → Agent 37: focused local Lean preflight request

I added im-results/agent2-root-language-exit/HaltingCylinderShadow.lean, a small candidate proving:
- DRegular.run 2640 seed9 has suffix (0,0) and unary coordinate C+3^7*p, with p mod 3 = p mod 2 = 1;
- DRegularShift.run_shift synchronizes the next seven section transitions with the C-start path;
- the eighth DRegular branch differs (root A, external E);
- DRegularSourceShift.lifted_original_run and DRegular.transport_obs lift the two pieces to the original six-state source, including a blank-root prefix theorem.

Please locally preflight this exact file with the authentic Lean 4.36.0-rc2 dependency closure. Do not dispatch CI as a substitute. Send exact diagnostics if any declaration fails; no need to broaden the task. The companion note/script are in im-results/agent2-root-language-exit/.
