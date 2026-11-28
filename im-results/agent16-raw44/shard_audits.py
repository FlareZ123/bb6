"""Split generated 24-way Lean audit definitions into bounded kernel reductions."""
import argparse
import re
from pathlib import Path


def shard(src: Path, dest: Path, limit: int):
    text = src.read_text()
    name = re.search(r'^def (kid\d+) : Audit :=\n', text, re.M)
    if not name:
        raise ValueError(f'no kid definition: {src}')
    kid = name[1]
    theorem = re.search(r'^theorem '+kid+r'_checked : zipCheck (\d+) (.+) '+kid+r' = true := by decide \+kernel$', text, re.M)
    if not theorem:
        raise ValueError(f'no checked theorem: {src}')
    bound, root = theorem.groups()
    header = text[:name.start()].replace('set_option maxRecDepth', 'import Raw44FastZipCheck\nset_option maxRecDepth')
    header += 'open BB6.Agent16Raw44FastZip\n'
    ns = re.search(r'^namespace (.+)$', header, re.M)[1]
    lines = iter(text[name.end():theorem.start()].splitlines())
    def parse():
        line = next(lines).strip().rstrip(',')
        split = re.fullmatch(r'\.split (\d+) (\(\d+, (?:true|false)\)) \(byMove \[', line)
        if split:
            children = [parse() for _ in range(24)]
            assert next(lines).strip().rstrip(',') == '])'
            return (line, split.groups(), children, 1 + sum(c[3] for c in children))
        assert line.startswith(('.cycle ', '.last ', '.proven ', '.far ')), line
        return (line, None, [], 1)
    tree = parse()
    assert not list(lines)
    output = []
    index = 0
    def move(i):
        return f'⟨{str(i>=12).lower()},{str(i%12>=6).lower()},{i%6}⟩'
    def render(t):
        return t[0] if not t[2] else t[0]+'\n'+',\n'.join(render(c) for c in t[2])+'\n])'
    def emit(t, p, label):
        nonlocal index
        if t[3] <= limit:
            output.append(f'def {label} : Audit :=\n{render(t)}\ntheorem {label}_checked : zipCheck {bound} {p} {label} = true :=\n  fastCheck_sound (show fastCheck {bound} {p} {label} = true by decide +kernel)\n')
            return
        n,s = t[1]
        ids = []
        for i,c in enumerate(t[2]):
            index += 1
            child = f'{kid}_chunk{index}'
            ids.append(child)
            emit(c, f'(refine {p} {s} (some {move(i)}))', child)
        proof_order = [q + offset for q in range(6) for offset in (0,6,12,18)]
        output.append(f'def {label}_kids : Move → Audit := byMove [{",".join(ids)}]\ndef {label} : Audit := .split {n} {s} {label}_kids\ntheorem {label}_each (mv : Move) :\n  zipCheck {bound} (refine {p} {s} (some mv)) ({label}_kids mv) = true := by\n  rcases mv with ⟨w,r,q⟩\n  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega\n  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl\n  all_goals cases w <;> cases r\n'+''.join(f'  · exact {ids[i]}_checked\n' for i in proof_order)+f'theorem {label}_checked : zipCheck {bound} {p} {label} = true := by\n  change (zipQueryOK {bound} {p} {n} {s} && allMoves (fun mv => zipCheck {bound} (refine {p} {s} (some mv)) ({label}_kids mv))) = true\n  simp only [Bool.and_eq_true]\n  exact ⟨by decide +kernel, allMoves_of _ {label}_each⟩\n')
    emit(tree, root, kid)
    dest.write_text(header+'\n'.join(output)+f'\n#print axioms {kid}_checked\nend {ns}\n')
    print(src.name, tree[3], 'nodes', len(output), 'proofs')


if __name__ == '__main__':
    p=argparse.ArgumentParser()
    p.add_argument('source',type=Path)
    p.add_argument('dest',type=Path)
    p.add_argument('--limit',type=int,default=97)
    a=p.parse_args()
    if a.limit<1: p.error('positive limit required')
    shard(a.source,a.dest,a.limit)
