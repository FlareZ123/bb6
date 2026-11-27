"""Generate compressed F421 source certificates. Lean checks every edge."""
from argparse import ArgumentParser
from dataclasses import dataclass
from pathlib import Path

from frontier_map import RULES

Pieces = list[tuple[str, int]]


def append(word: Pieces, token: str, count: int = 1) -> None:
    if count:
        if len(token) == 2 and word and word[-1][0] == token:
            word[-1] = token, word[-1][1] + count
        else:
            word.append((token, count))


def from_right(word: Pieces) -> Pieces:
    """Canonical list of pair runs, with at most one unmatched initial bit."""
    tail: Pieces = []
    lead = ""
    for token, n in reversed(word):
        if not n:
            continue
        if len(token) == 1:
            if lead:
                append(tail, token + lead)
                lead = ""
            else:
                lead = token
        elif lead:
            append(tail, token[1] + lead)
            append(tail, token[::-1], n - 1)
            lead = token[0]
        else:
            append(tail, token, n)
    if lead:
        tail.append((lead, 1))
    return tail[::-1]


def reverse(word: Pieces) -> Pieces:
    return [(token[::-1], n) for token, n in reversed(word)]


def from_left(word: Pieces) -> Pieces:
    return reverse(from_right(reverse(word)))


def split(word: Pieces, n: int) -> tuple[str, Pieces]:
    """Consume a short literal prefix from a compressed word."""
    head = ""
    for i, (token, count) in enumerate(word):
        width = len(token)
        q, r = divmod(n, width)
        if q >= count:
            head += token * count
            n -= width * count
        else:
            head += token * q + token[:r]
            stub = [(token[r:], 1)] if r else []
            return head, stub + [(token, count - q - bool(r))] + word[i + 1:]
    return head, []


def bits(token: str) -> Pieces:
    return [(b, 1) for b in token]


@dataclass
class Return:
    left: list[int | str]
    turn: str
    right: Pieces
    odd: bool
    suffix: Pieces
    cost: int

    def lean(self) -> str:
        left = [f".manyA {x}" if isinstance(x, int) else f".one .{x}" for x in self.left]
        codes = {"10": ".z1", "11": ".o1", "01": ".o0"}
        right = lean_list([f"({codes[p]}, {n})" for p, n in self.right])
        return f".single ⟨{lean_list(left)}, .{self.turn}, {right}, {lean_bool(self.odd)}, {lean_pieces(self.suffix)}⟩"


def single(word: Pieces) -> tuple[Pieces, Return]:
    left: list[int | str] = []
    stream = bits("1")
    length = 0
    remainder = word
    while True:
        remainder = from_left(remainder)
        if remainder[0][0] == "10":
            n = remainder[0][1]
            left.append(n)
            append(stream, "01", n)
            length += 2 * n
            remainder = remainder[1:]
            continue
        token, rest = split(remainder, 3)
        if token.startswith("00"):
            _, remainder = split(remainder, 2)
            turn, finish = "d", "1"
            break
        if token == "011":
            remainder, turn, finish = rest, "e", "10"
            break
        left.append({"110": "b", "010": "c"}[token])
        stream.extend(bits(RULES[token]))
        length += 3
        remainder = rest

    scan = from_right(stream + bits(finish))
    odd = scan[0] == ("1", 1)
    if odd:
        scan = scan[1:]
    end, end_count = scan[-1]
    assert end == ("11" if turn == "d" else "10")
    right = scan[:-1] + ([(end, end_count - 1)] if end_count > 1 else [])
    suffix = from_right(remainder)
    out = [("00" if odd else "10", 1)]
    out += [("00" if p == "11" else p, n) for p, n in right]
    out += [("01" if turn == "d" else "10", 1)] + suffix
    cost = length + (2 if turn == "d" else 3) + 4 + sum((6 if p == "01" else 2) * n for p, n in right)
    return from_left(out), Return(left, turn, right, odd, suffix, cost)


Row = tuple[int, int, bool]


def row_pieces(rows: list[Row]) -> Pieces:
    word: Pieces = []
    for p, q, mark in rows:
        append(word, "10", p)
        if mark:
            append(word, "00")
        append(word, "01", q)
    return word


@dataclass
class Drain:
    a: int
    b: int
    rows: list[Row]
    suffix: Pieces
    count: int

    def lean(self) -> str:
        rows = lean_list([f"⟨{p}, {q}, {lean_bool(f)}⟩" for p, q, f in reversed(self.rows)])
        return f".drain ⟨{self.a}, {self.b}, {rows}, {lean_pieces(self.suffix)}⟩"


def drain(word: Pieces) -> tuple[Pieces, Drain] | None:
    """Choose the longest safe near prefix containing at least one marker."""
    if len(word) < 2 or [p for p, _ in word[:2]] != ["10", "01"] or word[1][1] < 2:
        return None
    a, b = word[0][1], word[1][1]
    rows: list[Row] = []
    ends: list[int] = []
    pos = 2
    while pos < len(word) and word[pos][0] == "10":
        qpos = pos + 1
        mark = qpos < len(word) and word[qpos] == ("00", 1)
        qpos += mark
        if qpos >= len(word) or word[qpos][0] != "01" or word[qpos][1] < 2:
            break
        rows.append((word[pos][1], word[qpos][1], mark))
        pos = qpos + 1
        ends.append(pos)
    for size in range(len(rows), 0, -1):
        total = 0
        final = []
        for p, q, mark in reversed(rows[:size]):
            bound = 2 * total + int(mark)
            if p <= bound and p % 2 != int(mark):
                break
            visits = min(p, bound)
            hits = (visits + int(mark)) // 2
            final.append((p - visits, q + hits, False))
            total += hits
        else:
            if total:
                suffix = word[ends[size - 1]:]
                nxt = [("10", a + 2 * total), ("01", b + total)] + row_pieces(final[::-1]) + suffix
                return from_left(nxt), Drain(a, b, rows[:size], suffix, total)
    return None


def matches_seed(word: Pieces) -> bool:
    # The first secondary shape begins with leading P=2047, Q=3071.
    return word[:3] == [("10", 2047), ("01", 3071), ("10", 2048)]


def generate() -> tuple[list[Pieces], list[Return | Drain]]:
    words = [[("10", 1), ("01", 3), ("00", 1024)]]
    edges: list[Return | Drain] = []
    odd_count = 0
    while not (odd_count == 190 and matches_seed(words[-1])):
        step = drain(words[-1])
        if step is None:
            word, first = single(words[-1])
            words.append(word)
            edges.append(first)
            word, second = single(word)
            assert not second.odd and second.turn == "d"
            words.append(word)
            edges.append(second)
            odd_count += first.odd
        else:
            word, edge = step
            words.append(word)
            edges.append(edge)
        assert odd_count <= 190
    return words, edges


def lean_bool(p: bool) -> str:
    return "true" if p else "false"


def lean_bits(token: str) -> str:
    return f"⟨{lean_bool(token[0] == '1')}, {lean_bool(token[1] == '1')}⟩"


def lean_list(items: list[str]) -> str:
    return "[" + ", ".join(items) + "]"


def lean_pieces(word: Pieces) -> str:
    return lean_list([f".bit {lean_bool(token == '1')}" if len(token) == 1
                      else f".run {lean_bits(token)} {n}" for token, n in word])


def lean_packed(word: Pieces) -> str:
    word = from_right(word)
    lead = "none"
    if word and len(word[0][0]) == 1:
        lead, word = f"(some {lean_bool(word[0][0] == '1')})", word[1:]
    runs = lean_list([f"({lean_bits(token)}, {n})" for token, n in word])
    return f"⟨{lead}, {runs}⟩"


def write_lean(path: Path, words: list[Pieces], edges: list[Return | Drain]) -> None:
    with path.open("w") as out:
        print("import F421CompressedTrace\n", file=out)
        print("namespace BB6Coverage.Agent41F421.Compressed", file=out)
        print("open EpochWords\n", file=out)
        print("set_option maxRecDepth 4096\n", file=out)
        print(f"def seed0 : Packed := {lean_packed(words[0])}\n", file=out)
        batch = 12
        names: list[str] = []
        for i in range(0, len(edges), batch):
            j, index = min(i+batch, len(edges)), len(names) + 1
            events = edges[i:j]
            bound = sum(e.cost if isinstance(e, Return) else e.count for e in events)
            start, end = f"seed{index-1}", f"seed{index}"
            name = f"segment{index}"
            names.append(name)
            print(f"def {end} : Packed := {lean_packed(words[j])}", file=out)
            print(f"def edges{index} : List Edge := [", file=out)
            print(",\n".join("  " + e.lean() for e in events), file=out)
            print("]", file=out)
            print(f"theorem {name} : reaches {bound} {start}.word {end}.word :=", file=out)
            print(f"  traceSound (u := {start}) (v := {end}) (k := 0) (l := {bound}) (es := edges{index}) rfl\n", file=out)
        total = sum(e.cost if isinstance(e, Return) else e.count for e in edges)
        def conjoin(seq: list[str]) -> str:
            if len(seq) == 1:
                return seq[0]
            mid = len(seq)//2
            return f"(reachesTrans {conjoin(seq[:mid])} {conjoin(seq[mid:])})"
        print(f"theorem seedTrace : reaches {total} seed0.word seed{len(names)}.word :=", file=out)
        print(f"  {conjoin(names)}\n", file=out)
        print(f"abbrev firstSeed := seed{len(names)}", file=out)
        print(f"abbrev seedBound : Nat := {total}\n", file=out)
        print("#print axioms seedTrace", file=out)
        print("end BB6Coverage.Agent41F421.Compressed", file=out)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    opts = parser.parse_args()
    states, steps = generate()
    write_lean(opts.output, states, steps)
    print(f"{len(steps)} edges, {sum(isinstance(e, Drain) for e in steps)} drains")
