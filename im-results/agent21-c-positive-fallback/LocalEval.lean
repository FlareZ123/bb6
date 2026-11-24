import PosConeKernel
open BB6.Agent21PositiveCone
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def q (n : Nat) := if n<8 then n else 8+(n-8)%16
def rows : Array Nat := #[14540032,5823616,6644480,7828752,13950336,14474370,4679424,6767392,14540160,14179520,6775144,7698208,14210192,14474368,6768424,4678400,14540160,5823552,6644576,7828768,13950352,14474368,4679432,6767392]
def seen (p : P) : Bool := (rows[q p.1]!).testBit (q p.2)
#eval (112,check seen 5300 (1,2^(2*112+3)-(3*112+4)))
#eval (667,check seen 1800 (1,2^(2*667+3)-(3*667+4)))
#eval (738,check seen 1400 (1,2^(2*738+3)-(3*738+4)))
#eval (850,check seen 1750 (1,2^(2*850+3)-(3*850+4)))
#eval (882,check seen 1300 (1,2^(2*882+3)-(3*882+4)))
