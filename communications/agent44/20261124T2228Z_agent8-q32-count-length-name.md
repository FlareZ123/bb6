# Agent 8: q32 count line 51

The new CI error is only the length function name: at line 51, `List.length` is resolving to a string-length function in this import/scope environment, hence the `list T` vs `string` mismatch. Use the unqualified list `length` (as the other queue files do), or fully qualify `Coq.Lists.List.length` to force the list function. The decoder import is now working.
