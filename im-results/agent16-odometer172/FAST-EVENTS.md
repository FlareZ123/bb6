# Exact event acceleration, extension to 600,000 events

The C++ implementation uses arbitrary-precision integer arithmetic (Boost cpp_int). It reproduces the previously recorded 200,000-event state and continues to 600,000. This is finite trajectory evidence, not a nonhalting certificate.

Let p_i=3^i, D_i=sum_{h<i}(2-s_h)p_h. The distance to the next attempted L-to-H transition with exhausted following gap is

    D_i + 3 p_i g_{i+1} + p_i o(s_i),  o=(1,0,2).

This follows by subtracting V from the original deadline formula. Because D_i is monotone, once it reaches the current minimum, later deadlines cannot win. The carry count for a jump by delta follows directly from ternary addition: floor(delta/3^(i+1)) + carry-out + [new digit=2] - [old digit=2]. No division by huge powers is needed.

At 600,000 events: 514 particles, b=1, trailing gap 81,781,565. Counts (birth,wrap,pair collision,boundary pair collision,drain) = (240101,240103,119789,0,7). Sole non-1 charge at index 300, charge 2, originating at event 124075 (protected). No unsupported interaction was observed. Exact high-level time:

    50344313650146701173369609749586300447422113532480307023742632491559482890324329556276523381563623635787881086124017066349409622859892333948725348364968594835765910178299395837672040730437933472459780969454104083330196406014282157306668810212928153

Build: g++ -O3 -std=c++17 events_fast.cpp -o events_fast
Run from scratch: ./events_fast 600000
Resume: ./events_fast 1000000 odometer172-checkpoint.txt new-checkpoint.txt

The implementation stops on an unprotected exceptional birth, unsupported particle interaction, or empty terminal representation. The stop categories are diagnoses, not conclusions about machine halting. The previous local scratch checkpoint was overwritten by a separate diagnostic replay; the complete initial state and deterministic code are preserved for reproduction.
