# Community #746 (historical row 618): independent dyadic-cone derivation

Machine: `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA` (row 618 of the dated 663-machine roster).

For the exact high-level transition in [upstream Cryptids](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean), the blank-root arithmetic orbit halts iff a section value (N_j=4\cdot2^j-j-1) is reachable, where the section starts at (n=5). The independent theorem excludes all j congruent to 0,1,2,3 modulo 6, and all j<=6. Thus only j>=10 with j congruent to 4 or 5 modulo 6 remain.

## Exact section recurrence

At physical b=1 put n=a+3. There are unique t,k satisfying n+2+t=4*2^t+k and 1<=k<4*2^t. Following the high sweeps gives a=4*2^t-2 and b=2k. If k=1, this is a terminal state. For odd k>=3 the next section is m=6*2^t+(k+1)/2. For even k>=2, enter drain state with m0=6*2^t+k/2. The drain repeatedly replaces even m by 3m/2, then odd m by (3m+1)/2 and returns. Every section return increases n and is unique. Every drain output is 2 modulo 3.

## Uniform backward cone

Fix j>=7 with j%6<=3. Put P=2^j. Use the cone

    2P < m <= 4P,
    m + 2^i(2j+3) = 4P+j+2 for some i>=0.

The terminal N_j belongs to it with i=0. By the parity of i and j modulo 6, every m in this cone avoids residue 2 modulo 3. Hence every predecessor is direct. Direct output bands [6*2^t+2,8*2^t] force t=j-1, and substituting the inverse formula increments i by one.

The lower boundary must be justified: the parent p is at least 2P-j+2. If p<=2P, the cone equation for p gives 2^(i+1)(2j+3)=2P+e, with j+2<=e<=2j. The exponent i+1 is at most j+1 by size, so 2^(i+1) divides e, hence <=2j. But 2j(2j+3)<2P for j>=7, contradiction. The upper boundary follows from strict growth. This proves backward closure; root 5 cannot belong to the cone. The small terminal indices are eliminated using the unique increasing prefix 5→8→14→38→54→62→221→545.

## Formal verification

[Source package](Row618.lean.xz.b64), with standalone Lean 4.36.0-rc2 verification:

    base64 -d Row618.lean.xz.b64 | xz -d > Row618.lean
    lean Row618.lean

Uncompressed git blob SHA-1 af51f89d88e718bd6f434f559423735eb11a7300. The declarations cone_closed, terminal_excluded, root_halts_iff and restricted_root_halts_iff compiled with only propext, Classical.choice, Quot.sound. The file copies the exact upstream highLevelNext (b encoded as physical b-1) and proves the section/return/halting correspondence, including finite drain, directly in Lean. The upstream TM-to-high-level equivalence is the separately published theorem isHalt_iff_highLevel_acceleration; that upstream import was not recompiled here.

This is an independent derivation of an existing uniform elimination, not new machine coverage. Agent 10 and collaborators already have an original-source theorem excluding these four classes and a stronger finite cutoff of 50,000: see [the canonical #746 dossier](../agent10-cascade/README.md). The historical row 618 label masked the community #746 identity during initial investigation. The proof is retained as an intermediate alternative scalar presentation, not as a new academic result. The residual two classes require a genuinely new argument (underflow inverse branches can occur).
