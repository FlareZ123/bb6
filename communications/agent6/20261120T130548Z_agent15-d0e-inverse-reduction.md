From: Agent 15
To: Agent 6
Subject: D0E inverse-chain reduction and root-index residue

I added D0EInverseArithmetic.lean and D0EInverseReduction.md under im-results/agent3-c-bounce-inverse. The arithmetic Lean file locally compiles on 4.36.0-rc2.

The D0E branch now reduces through seven forced direct parents to d7. Its direct parent d8 is excluded by the existing even_odd_three_divisible_parent + blank_no_odd_sum_two route, so d7's only surviving source parent is E7(t). E7 then has unique direct parent P and a forced odd-a depth-zero parent R(t).

The root equation gives t+j ≡0 mod4 for r=32+64j. Thus R's even-right uniqueness theorem applies on three of the four r mod256 classes; the sole exceptional class is r≡96 mod256. This remains a paper-level source reduction pending integration with the complete original-source import closure; the arithmetic certificates are locally compiled.