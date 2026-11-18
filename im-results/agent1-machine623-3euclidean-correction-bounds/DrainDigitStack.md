# Ternary digit-stack normal form for the #623 evaluator

**Status:** exact derivation from the source definition of `evalA`; not yet source-CI packaged. Intermediate result in `im-results/`.

Write the ternary expansion of k from least significant digit upward. Let r be the number of consecutive low ternary digits equal to 1 before the first digit different from 1. If k is a string of r ones with no further ternary digit, take the terminal digit to be 0. Let epsilon be that first non-1 digit, so epsilon is 0 or 2.

For `evalA a k m`, the recursive source equations give the following exact first/second-coordinate normal form:

* If epsilon=2, the evaluator succeeds and returns first counter `a+1`; the new second counter is k divided by 3^(r+1).
* If epsilon=0 and a>r, the evaluator succeeds and returns first counter `a-r-1`; the new second counter is k divided by 3^(r+1).
* If epsilon=0 and a<=r, the evaluator returns `none`.

The proof is direct induction through the r digit-1 branches. Each digit 1 executes the recursive branch with first counter decremented by one and second counter divided by 3. The terminal digit 2 executes the immediate success branch, while terminal digit 0 executes the decrement branch; at first counter zero the terminal 0 branch is exactly `none`.

This is a useful strengthening of the existing ternary-cylinder criterion: it identifies not only when `evalA` fails, but the exact first-counter loss/gain and the amount of ternary input consumed.

## Consequence for the two boundary families

The complementary affine-buffer reduction isolates two one-parameter exceptional section families:

1. Even gap-two: `D(d+2,d)` with even d, whose next step is `drainB 0 (d+2) 2`.
2. Odd offset-three: `D(d+3,d)` with odd d, whose next step is `drainB 1 (d+2) 3`.

For the odd offset-three family, the first drain evaluator is
`evalA 1 (d+1) (2*d+10)`. By the normal form, this first evaluator fails exactly when the low ternary digits of `d+1` begin with a 1 followed by 0 (or when d+1=1), equivalently

`d+1 ≡ 1 (mod 9)`, i.e. `d ≡ 0 (mod 9)`.

So every odd offset-three state with d divisible by 9 is an immediate halt, independently of the third coordinate. Other d enter a recursively smaller ternary block, with the first counter determined exactly by the first non-1 ternary digit.

For the even gap-two family, the first evaluator is `evalA 0 (d+1) (...)`. It fails immediately exactly when d+1 has low ternary digit 0, i.e. d ≡ 2 (mod 3). Otherwise the same digit-stack normal form reduces the problem to a smaller ternary suffix and a small first-counter state.

## Research value

The remaining root-specific problem is therefore not an opaque simulation of the boundary lines. Their survival is a deterministic ternary digit-stack process with an explicit first-counter balance. A future proof can attack reachability of these lines by combining the root's arithmetic predecessor constraints with this digit-stack normal form, rather than treating each boundary state as an unrelated machine configuration.
