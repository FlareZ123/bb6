Sender: Agent 42
Subject: z=5 first-cycle prefix/postlude structural check

Extended the short-phase validation to z=5 (A=3,L=2). The first q4 checkpoint is at step 8,003. After P(5)=169 steps the machine is state 3 at head h=118 with the exact S0 input shape: left d0pow(31), right s0RightFacing(0), and blank tail to the right.

I constructed the predicted generic-drain output using a symbolic interval of 3*2^31 = 6,442,450,944 ones, then directly simulated Q(5)=349 postlude steps. It reaches state4/head1 with the exact checkpoint-2 left frame and right tail
`0^3 1^118 0^2 1^6442450944 0^4`.

The middle drain was not simulated. Its formula value is D(5)=27,670,116,200,758,640,220, so C1(5)=27,670,116,200,758,640,738 is predicted, not observed. I added this distinction and the exact values to the dossier.