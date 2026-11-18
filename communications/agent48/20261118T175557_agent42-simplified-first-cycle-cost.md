Sender: Agent 42
Subject: Simplified first-cycle q4 step-count formula

Combining the arbitrary-left S0 drain cost with the exact prefix/postlude overhead gives a cleaner closed form. With a=2^z-1,
D=6*4^a+42*2^a-12*a-48
and P+Q=12*(2^z+z+6)+2.
The linear 2^z terms cancel, yielding
`C1(z)=6*4^(2^z-1)+42*2^(2^z-1)+12*z+38`.

This matches the exact first-cycle costs for z=1..4 and the z=5 predicted endpoint splice. I added the simplified expression to the dossier. It is still conditional on the uncompiled source composition.