"""Repair the archived exact 39446-transition first-hole replay.

Retain all original checkpoints and certify every segment using the same
zipper semantics. The cheap parent is independent of replay.
"""
import re
from pathlib import Path


def repair(directory, update_base=True):
    directory = Path(directory)
    late = directory / 'Raw54OneRALate.lean'
    source = late.read_text()
    parent_module = 'Raw54OneRAParent'
    if not source.startswith('import ' + parent_module + '\n'):
        ns = 'BB6.Agent8Raw54.OneRALate'
        source = source.replace('BB6Coverage.Agent50Zipper BB6.Agent48PrefixAudit',
                                'BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6.Agent48PrefixAudit')
        assert 'BB6Coverage.Agent31Pump' in source
        header, body = source.split('namespace M39447\n', 1)
        (directory / (parent_module + '.lean')).write_text(header + 'end ' + ns + '\n')
        options = header[header.index('set_option'):header.index('namespace ')]
        opens = next(l for l in header.splitlines() if l.startswith('open '))
        def prefix(imports):
            return ''.join('import ' + m + '\n' for m in imports) + options + 'set_option autoImplicit false\nset_option Elab.async false\nnamespace ' + ns + '\n' + opens + '\nnamespace M39447\n'
        end = 'end M39447\nend ' + ns + '\n'
        defs, replay = body.split('theorem accum0', 1)
        replay, tail = replay.split('theorem query :', 1)
        literal = '''def literalTable : PartialMachine := fun s => match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem literal_eq : literalTable = table := by
  funext s
  obtain ⟨q,a⟩ := s
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases a <;> decide
'''
        defs = defs.replace('def bits ', literal + 'def bits ', 1)
        cfgs = re.findall(r'^def z(\d+) : Z := .*$', replay, re.M)
        assert cfgs == [str(i) for i in range(1, 80)]
        config_lines = re.findall(r'^def z\d+ : Z := .*$', replay, re.M)
        segs = re.findall(r'^theorem seg(\d+) : zrun table (\d+) (\w+) = some (z\d+) := by rfl$', replay, re.M)
        assert len(segs) == 79
        assert sum(int(n) for _, n, _, _ in segs) == 39446
        cfg_module = 'Raw54OneRALateConfigs'
        (directory / (cfg_module + '.lean')).write_text(prefix([parent_module]) + defs + '\n'.join(config_lines) + '\n' + end)
        imports = []
        for j in range(0, 79, 10):
            module = f'Raw54OneRALateSegment{j // 10}'
            imports.append(module)
            lines = []
            for i, n, a, b in segs[j:j+10]:
                assert b == f'z{i}' and a == ('start' if i == '1' else f'z{int(i)-1}')
                lines.append(f'theorem seg{i} : zrun literalTable {n} {a} = some {b} := by rfl')
            (directory / (module + '.lean')).write_text(prefix([cfg_module]) + '\n'.join(lines) + '\n' + end)
        accum = ['theorem accum0 : zrun literalTable 0 start = some start := rfl']
        t = 0
        for i, n, _, b in segs:
            t += int(n)
            accum.append(f'theorem accum{i} : zrun literalTable {t} start = some {b} := join accum{int(i)-1} seg{i}')
        accum.append('''theorem accum79_table : zrun table 39446 start = some z79 :=
  (congrArg (fun p => zrun p 39446 start) literal_eq).symm.trans accum79
theorem query : zipQueryOK 39447 table 39446 (0,true) = true := by
  have h : queryAt 39447 table 39446 (0,true) z79 = true := by decide
  exact (queryAt_eq 39447 table 39446 (0,true) z79 accum79_table).symm.trans h''')
        _, tail = tail.split('theorem rest :', 1)
        tail = 'theorem rest :' + tail
        before, after = tail.split('theorem witness_halts :', 1)
        _, after = after.split('theorem witness_delay :', 1)
        witness = '''theorem witness_halts : HaltsAfter witness 39446 := by
  have hr : knownRun table 39446 = some (embed z79) :=
    (knownRun_zip table 39446).trans (congrArg (Option.map embed) accum79_table)
  have hs : readSlot (embed z79) = (0,true) :=
    (read_embed z79).trans (by decide)
  apply first_hole_halts table 39446 (embed z79) hr
  · rw [hs]
    decide
  · rw [hs]
    exact weightedTNFDefaultCompletion_compatible _
'''
        late.write_text(prefix([parent_module] + imports) + '\n'.join(accum) + '\n' + before + witness + 'theorem witness_delay :' + after)
    if update_base:
        base = directory / 'Raw54OneRABase.lean'
        text = base.read_text()
        assert text.startswith(('import Raw54OneRALate\n', 'import Raw54OneRAParent\n'))
        base.write_text(text.replace('import Raw54OneRALate\n', 'import Raw54OneRAParent\n', 1))


if __name__ == '__main__':
    import sys
    repair(sys.argv[1])
