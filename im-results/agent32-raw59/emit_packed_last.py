"""Generate independent, kernel-checked exact last-hole certificates.

The Python simulator and sweep miner are only witness producers. Lean checks
all framed rules, packed checkpoints, exact primitive costs, final hole,
and weighted margin against the original PartialAudit semantics.
"""
from mine_packed_sweeps import value, parse_table
from mine_bridges import compress_bridges

MIN_STEPS = 5000
GROUP_ACTIONS = 16
NS = 'BB6.Agent32Raw59PackedQuery'
PUMP = 'BB6Coverage.Agent31Pump'


def word(n, bits):
    return f'⟨{n},0x{bits:x}⟩'


def encode_word(xs):
    return word(len(xs), value(xs))


def encode_state(z):
    q,ll,lb,rl,rb=z
    return f'⟨{q},{word(ll,lb)},{word(rl,rb)}⟩'


def emit_certificate(module: str, table: str, steps: int, hole: int,
                     bound: int) -> tuple[str, str, str]:
    assert steps >= MIN_STEPS and steps + 6 <= bound
    moves = parse_table(table)
    assert moves.count(None) == 1 and moves[hole] is None
    rules, bridges, actions, final = compress_bridges(table, steps)
    q,ll,lb,_,_=final
    assert 2*q+(lb&1 if ll else 0) == hole
    print('packed',module,steps,'rules',len(rules),'actions',len(actions),
          'bridges',len(bridges),'raw',sum(n for typ,r,n,_ in actions if typ=='raw'),flush=True)
    namespace = 'BB6.Agent32' + module
    end = NS + '.startB'
    slot = f'({hole//2},{str(bool(hole%2)).lower()})'
    out = ['import Raw59PackedMacro\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n',
           f'namespace {namespace}\nopen BB6.Agent47PartialAudit\n',
           'def table : BB6Coverage.PartialMachine := fun s => match s.1.val, s.2 with\n']
    for i,mv in enumerate(moves):
        rhs = ('none' if mv is None else
               f'some (some ⟨{str(bool(mv[0])).lower()},{str(mv[1]).lower()},{mv[2]}⟩)')
        out.append(f'  | {i//2},{str(bool(i%2)).lower()} => {rhs}\n')
    out.append('  | _,_ => none\n')
    for j,r in enumerate(rules):
        rn = f'rule_{j}'
        words = ','.join(map(encode_word,(r.lp,r.rp,r.inp,r.out)))
        out.append(f'def {rn} : {NS}.Rule := ⟨{r.q},{str(r.right).lower()},{words},{r.cost}⟩\n')
        out.append(f'theorem {rn}_valid : {rn}.Valid table := by intro L R; rfl\n')
    for j,b in enumerate(bridges):
        bn = f'bridge_{j}'
        words = ','.join(map(encode_word,(b.li,b.ri,b.lo,b.ro)))
        out.append(f'def {bn} : {NS}.Bridge := ⟨{b.q},{b.next},{words},{str(b.ls).lower()},{str(b.rs).lower()},{b.cost}⟩\n')
        out.append(f'theorem {bn}_valid : {bn}.Valid table := by intro L R; rfl\n')
    total=0
    for i in range(0,len(actions),GROUP_ACTIONS):
        group=actions[i:i+GROUP_ACTIONS];j=i//GROUP_ACTIONS
        start,end=end,f'end_{j}'
        amount=sum(rules[r].cost*n if typ=='sweep' else n for typ,r,n,_ in group)
        previous=total;total+=amount
        cert,check,seg,path=(f'{k}_{j}' for k in ('actions','check','seg','path'))
        out.append(f'def {end} : {NS}.BZ := {encode_state(group[-1][-1])}\n')
        terms=[f'.raw {n}' if typ=='raw' else f'.bridge bridge_{r} bridge_{r}_valid' if typ=='bridge' else f'.sweep rule_{r} rule_{r}_valid {n}' for typ,r,n,_ in group]
        out.append(f'def {cert} : List ({NS}.Action table) := [\n'+',\n'.join(terms)+'\n]\n')
        out.append(f'theorem {check} : {NS}.traceRun {cert} {start} = some {end} := by decide +kernel\n')
        out.append(f'''theorem {seg} : {PUMP}.run0 table {amount} {start}.decode = some {end}.decode := by
  have h := {NS}.trace_sound {cert} {start} {end} {check}
  have hc : {NS}.traceCost {cert} = {amount} := by rfl
  rw [hc] at h
  exact h
''')
        goal=f'theorem {path} : {PUMP}.run0 table {total} {NS}.startB.decode = some {end}.decode'
        if j==0:
            out.append(goal+f' := {seg}\n')
        else:
            out.append(goal+f''' := by
  have h := {PUMP}.join0 path_{j-1} {seg}
  have hc : {previous}+{amount}={total} := by rfl
  rw [hc] at h
  exact h
''')
    assert total == steps
    out.append(f'''theorem read_eq : BB6Coverage.Agent10ZipAudit.zipRead table {steps} = some {slot} :=
  {NS}.read_of_run table {steps} {end} {slot} {path} (by decide)
theorem last_ok : partialCheck {bound} table (.closed (.last {steps} {slot})) = true :=
  {NS}.last_of_query {bound} table {steps} {slot}
    ({NS}.query_of_read {bound} table {steps} {slot} read_eq (by decide) (by decide)) (by decide)
#print axioms last_ok
end {namespace}
''')
    return ''.join(out),namespace+'.table',namespace+'.last_ok'
