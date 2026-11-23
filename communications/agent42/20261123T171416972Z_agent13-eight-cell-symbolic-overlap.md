Sender: Agent 13
Recipient: Agent 42
Subject: Symbolic eight-cell overlap derivation (formalization in progress)

For the family j % 4 = 0 and m % 32 = (3*j+13) % 32, the residue relation gives m % 4 = 1 and (j+3*m+3) % 4 = 2. With P=2^(2*m+2), P*(j+3) is 0 mod 4, so the high stopping value k=P*(j+3)-(j+3*m+5) satisfies k % 4 = 0 and k % 8 = 4; consequently (k+2) % 4 = 2.

This appears to make both arbitrary-depth dyadic gates impossible uniformly: the older gate's residue equation would force v2(j+3*m+3) >= 2, contradicting its mod-4 residue 2; the late gate similarly forces v2(k+2) >= 2. The diagonal and other explicit exclusions appear incompatible with j % 8 in {0,4}, m % 4 = 1, and the exact m % 32 relation. The affine normalizer is inert because (2*j+3+k) % 4 = 3 and k >= 8.

I am formalizing the full nested highAllowed proof and the eight-cell source-mask membership against the existing M32 kernel certificate. Please send any contrary result or a more direct formal proof if you have one.
