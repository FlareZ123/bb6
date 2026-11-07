"""Generate a kernel-checkable 5,120-return S4 root certificate.

The generator uses the source-shaped checker to produce full-stack states
every 16 returns. The generated Lean file proves each 16-return segment
against the original S4 source definitions imported by the manual CI job.
"""

from argparse import ArgumentParser
from pathlib import Path

from s5457_chunk_states import S337, S5457, chunk_states


def lean_list(values: tuple[int, ...]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def render() -> str:
    checkpoints = list(chunk_states())
    assert len(checkpoints) == 321
    assert checkpoints[0] == (0, S337)
    assert checkpoints[-1] == (5120, S5457)

    lines = [
        "import S4PrefixEighthCycle",
        "import Lean.Elab.Tactic.Omega",
        "",
        "namespace S4Prefix5457",
        "",
        "open S4Power S4Octet S4Toggle S4PrefixCausal S4PrefixEighthMass S4PrefixEighthCycle",
        "",
        "set_option maxRecDepth 250000",
        "set_option maxHeartbeats 0",
        "",
    ]

    for step, state in checkpoints[1:]:
        lines.append(f"def s{337 + step} : List Nat := {lean_list(state)}")

    lines.append("")
    for index in range(320):
        start = 337 + 16 * index
        end = start + 16
        start_name = "s337" if index == 0 else f"s{start}"
        end_name = f"s{end}"
        lines.append(
            f"theorem chunk_{start}_{end} : prun 16 {start_name} = some {end_name} := by\n"
            f"  simp [prun, P, G, H.eq_1, H.eq_2, {start_name}, {end_name}]"
        )

    lines.extend([
        "",
        "private theorem prun_add_local (m n : Nat) (xs : List Nat) :",
        "    prun (m+n) xs = (prun m xs).bind (prun n) := by",
        "  induction n with",
        "  | zero => simp [prun]",
        "  | succ n ih =>",
        "      rw [Nat.add_succ]",
        "      simp only [prun, ih]",
        "      cases h : prun m xs with",
        "      | none => simp [h]",
        "      | some U => simp [h, prun]",
        "",
        "private theorem prun_compose {m n : Nat} {T U V : List Nat}",
        "    (h1 : prun m T = some U) (h2 : prun n U = some V) :",
        "    prun (m+n) T = some V := by",
        "  rw [prun_add_local, h1]",
        "  simpa using h2",
        "",
        "theorem seed5457 : prun 5457 seed = some s5457 := by",
        "  have h0 := seed337",
    ])

    for index in range(320):
        lines.append(
            f"  have h{index + 1} := prun_compose h{index} "
            f"chunk_{337 + 16 * index}_{353 + 16 * index}"
        )

    lines.extend([
        "  exact h320",
        "",
        "def cycle9Start : List Nat := cycle8PeriodicStart ++ [171050]",
        "",
        "theorem seed5457_prefix9 : s5457.take 9 = cycle9Start := by rfl",
        "",
        "theorem seed5457_mass : stackMass s5457 = 2247 + 1024*5457 := by decide",
        "",
        "#print axioms seed5457",
        "#print axioms seed5457_prefix9",
        "#print axioms seed5457_mass",
        "",
        "end S4Prefix5457",
        "",
    ])
    return "\n".join(lines)


def main() -> None:
    parser = ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.write_text(render(), encoding="utf-8")


if __name__ == "__main__":
    main()
