# Agent 21: Machine C certified source bridge and section calculus

Status: intermediate mathematical results, with Machine C's blank-tape halting still open. No exact BB(6) value is claimed.

Target machine: 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC. Pinned Cryptids commit: ced8f9f44f67a167d5ecc03e687b048c67926371. Blank-entry accelerated state: (5,0,1).

## Machine-level bridge

CSourceBridge.lean proves branch-by-branch equality between Agent 11's standalone nextC map and the Cryptids source accelerator, transports its original-machine simulation contract, and proves:

    IsHalt(original machine) iff exists j, Reach(nextC, (0,2j,4j+10)).

CReachBridge.lean connects inductively defined Reach to finite iteration of Option.bind. Verification: successful manual GitHub Actions run https://github.com/FlareZ123/bb6/actions/runs/41389979481, with standard Lean axioms and no sorryAx.

## Universal accelerated section identities

Notation (a,k,c) ->[N] (a',k',c') denotes exactly N accelerated transitions.

Long, for k>=1:
    (2k+r,k,0) ->[2k+1] (r,2k+2,0).

Middle odd, r+s=2m+3:
    (2m+3,m+r+3,0) ->[2m+2r+5] (2s,2r+5,0).

Middle even, r+s=2m+1:
    (2m+2,m+r+2,0) ->[2m+2r+6] (2s+1,2r+5,0).

Far even, t+s=4m+6:
    (2m+2,3m+t+4,0) ->[6m+2t+11] (2s,2t+4,0).

Far odd, t+s=4m+8:
    (2m+3,3m+t+8,0) ->[6m+2t+13] (2s+1,2t+6,0).

Critical halt, for all m:
    runN (6m+11) (some(2m+3,3m+7,0)) = none.

Proof sources: CSection.lean, CReturn.lean, CFarReturn.lean, CGatewayTime.lean. All these formulas were checked locally under Lean 4.36.0-rc2 without sorryAx. They describe arbitrary synthetic starts and do not prove critical resets are reachable from the blank tape.

## All-input positive-counter termination

CPhaseRank.lean proves the strict decrease, for c>0 and successful nextC transition, of:

    phaseRank(a,k,c)=2c+(if a=0 then 1 else 0).

Strong induction gives a uniform bound on every excursion. For all a,k some 1<=n<=4k+5 witnesses either stopping or a return to some (a',k',0). This bound is independent of the initial a. It does not imply that repeated zero-counter excursions eventually stop.

CStrongBridge.lean aims to attach Agent 11's stronger modulo-eight gateway theorem directly to the raw machine, after SHA-256-verifying its compressed proof sources. Consult the latest manual CI run for proof status.

## Reproduction and next question

The manual-only workflow .github/workflows/agent21-c-source-bridge.yml checks the pinned upstream source and locally developed Lean modules. The central open problem remains proving or refuting blank-entry reachability of the residual reset and side gateways. All results belong under im-results/ pending a substantive original holdout classification.
