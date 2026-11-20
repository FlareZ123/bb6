#!/usr/bin/env python3
"""Independent replay of the 107 external A_step2 macros for Cryptid D."""
import json
from pathlib import Path

DELTA = {
    (0,0):(1, 1,1), (0,1):(0, 1,4),
    (1,0):(1,-1,2), (1,1):(0, 1,0),
    (2,0):(1,-1,0), (2,1):(1,-1,3),
    (3,0):(1,-1,2), (3,1):(1,-1,5),
    (4,0):(0,-1,2), (4,1):(0,-1,1),
    (5,0):(1,-1,4), (5,1):None,
}

ARGS = [
    13,21,5,5,21,5,17,21,5,27,
    35,21,5,5,21,5,5,31,21,5,
    5,21,5,17,21,5,5,21,5,5,
    21,21,21,5,5,21,5,5,21,5,
    5,31,21,5,5,21,21,21,5,5,
    21,5,27,39,21,5,5,21,5,5,
    31,21,5,5,21,5,17,21,5,5,
    21,5,5,21,21,21,5,5,21,5,
    5,21,5,5,31,21,5,5,21,5,
    17,21,5,5,21,5,5,21,21,21,
    5,5,21,5,5,21,5,
]

CHECKPOINTS = {
    10: (35925965576050291197954676646168812866911688985763244505, [0,1,0,1,0,1,0,1,1]),
    20: (653274599173389056319717515476765122857837155218448003942322, [0,1,0,1,1,1,0,1,0,1,0,1,1,1]),
    30: (11879087870908968104360314522392758770461111276045783640742261386, [0,1,1,1,0,1,0,1,1,1]),
    40: (216008289352335720339610602524813115320952275950623503089297980541682, [0,1,0,1,1,0,1,1,1]),
    50: (3927875740627220359664132971002588353805172690412603331883223229967369354, [0,1,1,1,1,1,1,1,1,0,1,0]),
    60: (71424147101329785314496471805836819044114607618056461822634921267834080686730, [0,1,1,0,1,1,1,1,1,1,1,1]),
    70: (1298770410781319861625359536628288369435308900216028055554241136144906066587587722, [0,1,1,1,1,1,1,0,1,0,1,1,1,1,1]),
    80: (23616726952692910182205306669292505610517611280824263889413609179834777358573759023858, [0,1,0,1,1,1,1,1,0,1,1,1,1,1]),
    90: (429444486360386240087203819295254784395458238425633310167425409595064063059982219052239602, [0,1,0,0,1,0,1,0,1,1]),
    100:(7808980780222260203826248505306665087325883016528076661998155848237077485933315200811517542561, [0,1,0,1,0,1,1,1,1,1,1,1,1,0,1,1]),
    107:(7488166283129708930486796847462680979065226437987146331898837006603604720521272903526417758309106, [0,1,0,1,1,0,1,1]),
}

def dregular_suffix(q, b):
    return [x for _ in range(q) for x in (0,1)] + [1]*b

def parse_regular_suffix(r):
    # A trailing zero is a represented blank and is ignored by the ListBlank section map.
    while r and r[-1] == 0:
        r = r[:-1]
    for q in range(len(r)//2 + 1):
        prefix = [x for _ in range(q) for x in (0,1)]
        if r[:len(prefix)] == prefix and all(x == 1 for x in r[len(prefix):]):
            b = len(r) - len(prefix)
            if q > 0 or b == 0:
                return q, b
    return None

def dregular_next(n, q, b):
    # Arithmetic next table from DRegular.lean; None is the E,b=1 regular-language exit.
    if n % 3 == 2:
        k = n // 3
        if q == 0:
            return (8*k+9, 0, 0), "B0"
        if q == 1:
            return (8*k+10+b, 0, 0), "B1"
        return (8*k+10, q-1, b), "Bq"
    if n % 3 == 0:
        k = n // 3 - 1
        if q == 0:
            return (8*k+11, 0, 0), "A0"
        r = (b+1)//3
        d = (q-1) + 4*r
        if (b+1)%3 == 0:
            return (8*k+11+2*d, 0, 0), "A0s"
        if (b+1)%3 == 1:
            return (8*k+13+2*d, 0, 0), "A1s"
        return (8*k+7+2*d, 1, 5), "A2s"
    k = n // 3 - 1
    if q == 0:
        return (8*k+5, 1, 5), "E0"
    if b == 0:
        return (8*k+5, 1, 2*q+5), "Eempty"
    if b == 1:
        return None, "EX"
    if b == 2:
        return (8*k+9, q+1, 0), "E2"
    return (8*k+9, q+2, b-3), "Ege3"

def replay_macro(n, suffix, m):
    branch = n % 3
    N = 4*(n//3)-1 if branch in (0,1) else 4*(n//3)+3
    end = {0:-2, 1:-3, 2:-1}[branch]
    start = end - 2*N + 1
    state = {0:0, 1:4, 2:1}[branch]

    # Sparse overrides over a huge alternating block. ListBlank append reverses [1,0]^N,
    # so the cell nearest the head is 1, then 0, then 1 as one moves left.
    overrides = {start-2:1, start-1:1}
    if branch == 0:
        overrides[-1] = 0
    elif branch == 1:
        overrides[-2] = 0
        overrides[-1] = 0
    for i, bit in enumerate(suffix):
        overrides[i] = bit

    def read(pos):
        if pos in overrides:
            return overrides[pos]
        if start <= pos <= end:
            return 1 if (end-pos) % 2 == 0 else 0
        return 0

    head = 0
    max_extent = len(suffix)-1
    for raw_step in range(m):
        max_extent = max(max_extent, head)
        ins = DELTA[(state, read(head))]
        if ins is None:
            raise AssertionError(f"halted inside A_step2 prefix at {raw_step}")
        write, move, state = ins
        overrides[head] = write
        head += move
        max_extent = max(max_extent, head)

    # Exact precondition for step_01C_C11: C on the rightmost 1 of an alternating block,
    # with the two leading context ones immediately before that block.
    assert state == 2
    assert read(head) == 1
    assert head >= start and (head-start+1) % 2 == 0
    K = (head-start+1)//2
    assert K > 0
    assert read(start-2) == 1 and read(start-1) == 1
    for pos, bit in overrides.items():
        if start <= pos <= head:
            assert bit == (1 if (head-pos) % 2 == 0 else 0)
    for i in range(min(100, 2*K)):
        assert read(head-i) == (1 if i % 2 == 0 else 0)

    # Preserve represented extent, including trailing zeros in the suffix list.
    one_positions = [p for p,v in overrides.items() if v == 1 and p > head]
    if end > head:
        one_positions.append(end)
    last_nonzero = max(one_positions, default=head)
    last = max(last_nonzero, max_extent)
    right = [read(p) for p in range(head+1, last+1)]
    leading = 0
    while leading < len(right) and right[leading] == 1:
        leading += 1

    # step_01C_C11 sweeps K pairs into 2K ones; the final C,D steps add two more.
    out_n = 2*K + 2 + leading
    out_suffix = right[leading:]
    info = {
        "branch": {0:"A", 1:"E", 2:"B"}[branch],
        "N": str(N), "K": str(K), "head": str(head),
        "right_after_prefix": right, "leading_ones": leading,
    }
    return out_n, out_suffix, info

def main():
    n = 1975700577069254261393123959451562008800234946348086
    suffix = []
    branches = []
    trace = []
    for i, m in enumerate(ARGS, 1):
        before_n, before_suffix = n, suffix.copy()
        canonical = parse_regular_suffix(before_suffix)
        dregular = None
        if canonical is not None:
            q, b = canonical
            dnext, label = dregular_next(before_n, q, b)
            dregular = {"q":q, "b":b, "branch":label, "next_defined":dnext is not None}
        n, suffix, info = replay_macro(n, suffix, m)
        branches.append(info["branch"])
        dmatch = None
        if dregular is not None and dregular["next_defined"]:
            dn, label = dregular_next(before_n, dregular["q"], dregular["b"])
            dmatch = (n, parse_regular_suffix(suffix)) == (dn[0], (dn[1],dn[2]))
        elif dregular is not None:
            dmatch = False
        record = {
            "step":i, "a_step2_argument":m, "branch":info["branch"],
            "input_n":str(before_n), "input_n_mod3":before_n%3,
            "input_suffix":before_suffix, "dregular":dregular,
            "dregular_next_matches":dmatch,
            "intermediate_block_pairs":info["N"], "sweep_block_pairs":info["K"],
            "prefix_head":info["head"], "right_after_prefix":info["right_after_prefix"],
            "leading_ones_absorbed":info["leading_ones"],
            "output_n":str(n), "output_suffix":suffix,
            "affine_offset_c":str(n-8*(before_n//3)),
        }
        if i in CHECKPOINTS:
            expected_n, expected_suffix = CHECKPOINTS[i]
            record["checkpoint_matches_external_proof"] = (n == expected_n and suffix == expected_suffix)
            assert record["checkpoint_matches_external_proof"], (i,n,suffix,expected_n,expected_suffix)
            print(f"checkpoint {i:3d}: exact match; suffix={suffix}")
        trace.append(record)

    counts = {x:branches.count(x) for x in "AEB"}
    assert len(ARGS) == 107
    assert counts == {"A":0,"E":52,"B":55}
    assert n % 3 == 1
    assert all(x["dregular_next_matches"] is True for x in trace[:10])
    assert trace[10]["dregular_next_matches"] is False

    offset_counts = {}
    argument_counts = {}
    for item in trace:
        key = item["branch"] + ":" + item["affine_offset_c"]
        offset_counts[key] = offset_counts.get(key, 0) + 1
        mkey = str(item["a_step2_argument"])
        argument_counts[mkey] = argument_counts.get(mkey, 0) + 1
    unique_inputs = len({tuple(item["input_suffix"]) for item in trace})
    unique_outputs = len({tuple(item["output_suffix"]) for item in trace})
    input_lengths = [len(item["input_suffix"]) for item in trace]
    output_lengths = [len(item["output_suffix"]) for item in trace]
    result = {
        "external_source_commit":"1929f57df4dd7afcc11c3f458e20526fd1f991e0",
        "external_source_file":"BusyLean/Individual/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.lean",
        "initial":{"n":"1975700577069254261393123959451562008800234946348086","suffix":[]},
        "a_step2_count":107, "checkpoint_steps":sorted(CHECKPOINTS),
        "branch_counts":counts,
        "affine_offset_distribution":offset_counts,
        "argument_distribution":argument_counts,
        "unique_input_suffixes":unique_inputs,"unique_output_suffixes":unique_outputs,
        "input_suffix_length_range":[min(input_lengths),max(input_lengths)],
        "output_suffix_length_range":[min(output_lengths),max(output_lengths)],
        "total_branch_counts_including_finish":{"A":0,"E":53,"B":55},
        "final_before_finish":{"n":str(n),"suffix":suffix,"n_mod3":n%3},
        "steps":trace,
    }
    path = Path(__file__).with_name("macro_trace.json")
    path.write_text(json.dumps(result, indent=2) + "\n")
    print("ALL 11 CHECKPOINTS MATCH")
    print("A_step2 branch counts:", counts)
    print("Including final finish:", result["total_branch_counts_including_finish"])
    print("Affine offsets:", offset_counts)
    print("Unique input/output suffixes:", unique_inputs, unique_outputs)
    print("Final pre-finish section:", result["final_before_finish"])
    print("Trace written:", path)

if __name__ == "__main__":
    main()
