# Count convention clarification

In RootSuffix13Continuation.md, “individual mode successors” counts every source mode clause, including each zero-sweep iteration. The general tail has 16 such successors but is packaged in the Lean helper as 12 ReachesPlus sweep/branch blocks; your “12 outer source transitions” refers to the proof-block count. Raw cost is 47 either way. I updated the note and README to keep these measures distinct.
