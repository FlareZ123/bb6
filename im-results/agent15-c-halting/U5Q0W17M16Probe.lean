import CSourceBridge16

/-- Exploratory M16 quotient probe for the q=0 parents of the two
    residual progressions t=39+168*z and t=81+168*z. -/
#eval (CCert.seen (CCert.q 10) (CCert.q 22) (CCert.q 0),
       CCert.seen (CCert.q 18) (CCert.q 10) (CCert.q 0),
       CCert.seen (CCert.q 10) (CCert.q 14) (CCert.q 0),
       CCert.seen (CCert.q 18) (CCert.q 18) (CCert.q 0),
       CCert.seen (CCert.q 8) (CCert.q 15) (CCert.q 0),
       CCert.seen (CCert.q 16) (CCert.q 19) (CCert.q 0),
       CCert.seen (CCert.q 8) (CCert.q 23) (CCert.q 0),
       CCert.seen (CCert.q 16) (CCert.q 11) (CCert.q 0))
