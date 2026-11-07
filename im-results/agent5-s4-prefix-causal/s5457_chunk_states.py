"""Reproduce the candidate full S4 root state after 5,120 returns from s337.

The preceding 337-return root prefix is Lean-certified in S4PrefixEighthMass.
This script uses the full-root Python checker for the remaining finite segment.
It is computational evidence, not a Lean proof of the segment.
"""
from pathlib import Path
import sys
from typing import Iterator

sys.path.insert(
    0,
    str(Path(__file__).resolve().parents[1] / "agent5-s4-all-depth-sharp"),
)
from checker import chain

OFFSETS = (509, 290, 219)
S337 = (
    283, 906, 982, 3490, 3734, 5935, 13580, 25036, 64260,
    110669, 47472, 29613, 35485, 2939, 2936,
)
S5457 = (
    283, 906, 982, 3490, 3734, 5935, 13580, 109210, 171050,
    366446, 435688, 443554, 1702180, 1770018, 211301, 281569,
    35137, 35134,
)


def chunk_states(chunk_size: int = 16) -> Iterator[tuple[int, tuple[int, ...]]]:
    """Yield full-root states at multiples of chunk_size from s337."""
    state = S337
    yield 0, state
    for step in range(1, 5121):
        next_state = chain(OFFSETS, state)
        if next_state is None:
            raise AssertionError(f"full-root checker halted at offset {step}")
        state = next_state
        if step % chunk_size == 0:
            yield step, state


def main() -> None:
    checkpoints = list(chunk_states())
    assert checkpoints[-1] == (5120, S5457), checkpoints[-1]
    print("Full-root checker reaches the candidate s5457 after 5120 returns.")
    print("s5457 =", list(S5457))
    print("chunk checkpoints =", len(checkpoints) - 1)


if __name__ == "__main__":
    main()
