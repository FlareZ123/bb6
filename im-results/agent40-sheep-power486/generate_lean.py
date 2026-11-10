"""Generate the complete Lean arithmetic certificate from the checked row table.

Requires sibling agent40-sheep-648-parents/SheepPower648Core.lean and the
certificate.py in this directory. Outputs are atomically replaced under lock.
"""
from pathlib import Path
import os
import tempfile
from certificate import Q, SURVIVORS

HERE = Path(__file__).resolve().parent
CORE = HERE.parent / 'agent40-sheep-648-parents' / 'SheepPower648Core.lean'


def make_rows():
    lines = ['import SheepPower486Core', 'set_option maxRecDepth 4096',
             'set_option maxHeartbeats 0', 'namespace SheepPower486', '']
    for h, qs in enumerate(Q):
        d = 3**h
        for a, q in enumerate(qs, 1):
            m, c, b, shift = d*(2**(a+1)+1), 2*a*d+2**(h+1), h+1, 3*d
            good = SURVIVORS.get((h,a))
            name = f'{"only" if good else "no"}_h{h}_a{a}'
            claim = f't%{q}={good[1]}' if good else 'False'
            lines += [f'theorem {name} (t v : Nat)',
                      f'    (heq : {m}*v+{c}=2^({b}+486*t)+{shift}) : {claim} := by',
                      f'  exact {"only_class" if good else "no_generic"} {m} {b} {shift} {c} {q} '
                      + (f'{good[1]} ' if good else '') + 't v',
                      '    (by decide) (by decide)',
                      '    (by rw [←Nat.powMod_def]; decide)',
                      '    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using',
                      f'      (show ∀ x : Fin {q},',
                      f'        (Nat.powMod 2 ({b}+486*x.val) {m}+{shift})%{m}'
                      + (f' = {c}%{m} → x.val={good[1]}' if good else f' ≠ {c}%{m}')
                      + ' from by decide))', '    heq', '']
    lines += ['#print axioms no_h6_a14', '#print axioms only_h6_a2',
              'end SheepPower486', '']
    return '\n'.join(lines)


def make_all():
    clauses = [f'(h={h} ∧ a={a} ∧ t%{q}={r})'
               for (h,a),(q,r) in SURVIVORS.items()]
    lines = ['import SheepPower486Rows', 'set_option maxRecDepth 4096',
             'set_option maxHeartbeats 0',
             'set_option linter.unusedSimpArgs false', 'namespace SheepPower486', '',
             'theorem all_generic_gates (h a t v : Nat)',
             '    (hh : h ≤ 6) (ha : 1 ≤ a)',
             '    (hzero : h=0 → a=1)',
             '    (hpos : 0<h → a ≤ 2*h+2)',
             '    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)',
             '      = 2^(486*t+h+1)+3*3^h) :',
             '    '+' ∨\n    '.join(clauses)+' := by',
             '  rcases (show '+' ∨ '.join(f'h={h}' for h in range(7))
             +' from by omega) with '+'|'.join(f'h{h}' for h in range(7))]
    for h, qs in enumerate(Q):
        lines.append('  · subst h')
        if h == 0:
            lines += ['    have : a=1 := hzero rfl', '    subst a',
                      '    exfalso', '    apply no_h0_a1 t v',
                      '    have hexp : 486*t+0+1 = 1+486*t := by omega',
                      '    rw [hexp] at heq',
                      '    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq',
                      '    omega']
            continue
        lines += ['    rcases (show '+' ∨ '.join(f'a={a}' for a in range(1,len(qs)+1))
                  +' from by omega) with '+'|'.join(f'a{a}' for a in range(1,len(qs)+1))]
        for a,q in enumerate(qs,1):
            good = SURVIVORS.get((h,a))
            lines.append('    · subst a')
            if good:
                lines += [f'      have hgate : t%{q}={good[1]} := by',
                          f'        apply only_h{h}_a{a} t v']
                indent = '        '
            else:
                lines += ['      exfalso', f'      apply no_h{h}_a{a} t v']
                indent = '      '
            lines += [f'{indent}have hexp : 486*t+{h}+1 = {h+1}+486*t := by omega',
                      f'{indent}rw [hexp] at heq',
                      f'{indent}simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq',
                      f'{indent}omega']
            if good:
                lines.append('      omega')
    lines += ['', '#print axioms all_generic_gates', 'end SheepPower486', '']
    return '\n'.join(lines)


def make_root_gate():
    return '''import SheepPower486All
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace SheepPower486

/-- Exclude every generic source admitted by the signed-power cutoff. -/
theorem no_generic_forbidden (h a t v : Nat)
    (hh : h ≤ 6) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (ht4 : t%4=0) (ht7 : t%7≠1) (ht9 : t%9≠2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(486*t+h+1)+3*3^h) : False := by
  rcases all_generic_gates h a t v hh ha hzero hpos heq with
    h1 | h2 | h3 | h4 | h5 | h6
  all_goals omega

#print axioms no_generic_forbidden
end SheepPower486
'''


def publish():
    core = CORE.read_text(encoding='utf-8').replace('SheepPower648','SheepPower486').replace('648','486')
    data = {'SheepPower486Core.lean': core,
            'SheepPower486Rows.lean': make_rows(),
            'SheepPower486All.lean': make_all(),
            'SheepPower486RootGate.lean': make_root_gate()}
    lock_path = HERE / '.generate-lean.lock'
    lock = os.open(lock_path, os.O_WRONLY|os.O_CREAT|os.O_EXCL, 0o600)
    try:
        for filename, body in data.items():
            with tempfile.NamedTemporaryFile(mode='w',encoding='utf-8',dir=HERE,
                                             prefix=f'.{filename}.',delete=False) as tmp:
                tmp.write(body)
                tmp_name = tmp.name
            os.replace(tmp_name, HERE/filename)
    finally:
        os.close(lock)
        os.unlink(lock_path)
    print('Generated 55 Lean arithmetic rows, complete generic gate and root exclusion')


if __name__ == '__main__':
    publish()
