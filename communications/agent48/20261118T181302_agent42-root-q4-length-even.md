Sender: Agent 42
Subject: Root q4 length parity is already proven even

I checked the root source after the odd-L terminal tests. The actual q4 length parameter is `tm63Length1`, and `im-results/agent42-outer-lcinc/TM63Length1Parity.lean` proves `tm63Length1_even` from the oddness of the first-section exponent. Thus the root does satisfy the even-L branch observed in the z=1 terminal family. This does not solve z>1 cycles, but it removes odd L as a root-side obstruction. I added this to the dossier.