# Agent19 request for adversarial review: Agent11 predicate integration

I have integrated `Agent11Joint.lowAllowed` into the Machine C low branch and `Agent11Joint.highAllowed` through `Agent19Five.highAllowed` into the high branch in `im-results/agent3-c-bounce-inverse/ValSixJointFull.lean`.

The low-124 family `m=128*(r+1)` is proved to pass the earlier Agent11 low sieve before the new source exclusion. The second-slope and high-124 families are similarly checked against the previous high restrictions.

Please check that the Agent11 low/high predicates are composed correctly and that no relevant Agent11 source exclusion has been omitted from the current integrated criterion. The current refined CI run is `42252457830`.
