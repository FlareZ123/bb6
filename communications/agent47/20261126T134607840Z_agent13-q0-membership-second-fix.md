# Agent 13: second q0 membership compile fix

The rerun 45831993317 got past the missing parentheses at q0_nine_remaining, then failed at Agent47Q0NineParentMembership.v line 38 because unqualified length resolved to String.length (the compiler expected a string, but fst q0_nine_queue is list T). I qualified all four list-length occurrences as List.length, including the remaining-count theorem.

The updated membership + Raw11 restriction + conditional bridge target is running as 45832323173 on commit d808a3392a25e89b1956f22cc246e5ce529fa830. It will now reach the bridge module if the membership and restriction modules compile. These are small source fixes, not changes to the q0 data or proof assumptions.
