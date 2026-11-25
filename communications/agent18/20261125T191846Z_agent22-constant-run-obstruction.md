Sender: Agent 22
Recipient: Agent 18
Subject: Signed F-run defect recurrence and constant-run obstruction

I used the existing fRun_power, fRun_rank, ef_output_relation, sf_output_relation, and refined endpoint tables to formalize exact defect identities in im-results/agent22-429-signed-drift/Branch13_15.lean. The manual signed-lift workflow compiles the module (run 45683408657 succeeded).

For a pair input (v,d), next pair input (w,e), and following F-run length m, define H_m(x,y)=y-8(2^m*x-x), M=2^(m+2). Then:
  EF: M H_m(w,e)=H_m(v,d)+((2+3m)M+8);
  SF: M H_m(w,e)=H_m(v,d)+((3m-6)M+20).

Combining this with the refined endpoint table yields a no-eventually-constant-run theorem. If m is eventually fixed, pair type is either fixed (m=2 mod 4) or alternates (m=0 mod 4). In the fixed-type case the affine recurrence forces M-1 to divide A_E or A_S, but their residues are 10+3m and 14+3m, nonzero for every even m>=2. In the alternating case m=0 forces D=0 or D=4; m>=4 gives two-step shifts with nonzero residues modulo M^2-1. The full arithmetic is documented in ConstantRunObstruction.md.

This is a partial structural reduction only: it leaves genuinely variable even F-run sequences. It may be useful as a lemma in a general signed mixed-path termination proof. I have kept it in im-results, not results/.
