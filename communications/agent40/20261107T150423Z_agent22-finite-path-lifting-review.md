# Agent 22 review of finite-path lifting and exact-k cylinders

**Verdict:** I do not find a mathematical counterexample in the two requested lifting cases. The finite-path construction is sound as stated, conditional on the prior all-p inverse-letter and CRT-realizability results. I checked the valuation inequalities and the precision bookkeeping directly against the displayed formulas.

## 1. Physical odd-block length h0 larger than the truncated h*

Let the quotient precision be t, let a=v2(r)<t, and put h*=min(h0,t-a-1), c=a+h*+1. If h0>h*, then c=t. From the exact first-section identity,

`2(F(x)-1)=(1+2^{a+1})u+2a-3=2^{h0+1}v_0`.

Since h0+1>=h*+2, the right side vanishes modulo 2^{h*+1}. Thus the source residue modulo 2^t is independent of the target residue and equals the saturated inverse-letter residue T[t,a,h*](y). This is exactly the case where the suffix precision t-c is zero, so the claimed target cylinder is all even residues. Canonical-word uniqueness then identifies h* as the first letter at precision t.

For the *lifted physical path*, the chosen letter is deliberately h*, rather than the original witness's h0. This is legitimate: the reverse construction uses q_i=p+sum_{j>=i}c_j, so q_i>=p+c_i>=c_i+1. Hence q_i-a_i>=h_i+2, and the inverse gate forces the exact physical valuation h_i. The output is fixed modulo q_i-c_i>=p. Thus the new representative realizes the same quotient edge with a possibly shorter exact odd block. I see no gap here.

## 2. Zero-source letter (a,h)=(p,0)

Here c=p+1 and q_i>=p+c_i=2p+1. The inverse parent T[q_i,p,0](z_{i+1}) has exact valuation p: its bracket is odd. The first-section identity then forces v2(F(x_i)-1)=0, and the successor agrees with z_{i+1} modulo q_i-c_i>=p. The source projects to zero modulo 2^p, with no restriction on the even target. This case is also sound.

## 3. Reverse-walk precision and arithmetic progression

The recursion q_i=q_{i+1}+c_i leaves every target precision q_{i+1}>=p>=1. Thus the even target is always nontrivial at the gate step and exact h_i is forced at each physical return. Starting from x=z_0+2^P t with P=p+C, the finitely many odd-cofactor guards hold for all sufficiently large t because every fixed-branch return has slope

`3^{h_i}(1+2^{a_i+1})/2^{c_i}=(3/2)^{h_i}(1+2^{-a_i-1})>1`.

The product slope times 2^P is exactly A*2^p, with A odd, so the stated final arithmetic progression is consistent.

## 4. Small clarity improvement for the exact-k cylinder proof

In the one-edge converse in the metric README, the sentence “choose x=T[p,a,h](y)” is a residue-level statement. When c=t (the saturated case), T[t,a,h] alone does not force an exact physical h on an arbitrary representative, because one needs one additional precision bit. The subsequent CRT-realizability premise supplies that lift. I recommend making the precision explicit there: lift y to an even target at q>=c+1, use T[q,a,h], and then project the resulting genuine witness back to precision t. The finite-path theorem already does this correctly via q_i>=c_i+1.

## Scope

This review concerns the generic quotient and freely selected starts. It does not imply anything about the authentic fixed Sheep entry 10. The finite random-path verifier is useful regression evidence, while the paper proof and a future source-importing Lean theorem remain the relevant all-parameter evidence.
