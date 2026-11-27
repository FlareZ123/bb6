"""Apply after extracting the source archive; run from its root.

Copy minimize_cert.py into the extracted root first. This leaves already
checked automaton modules byte-identical, preserving exact dependency proofs.
The partitioning by original configuration count is unchanged.
"""
from pathlib import Path
p=Path('emit_siblings.py')
s=p.read_text()
a='from emit_automata import emit'
b="""from emit_automata import emit
from minimize_cert import quotient,validate
ORIGINAL = {"Raw56RE0LBAutomata00", "Raw56RE0LCAutomata00", "Raw56RE0LFAutomata00", "Raw56RE0LFAutomata01", "Raw56RE0LFAutomata02", "Raw56RE0RFAutomata01"}"""
c="proven[t]=f'{ns}.M{i}';parts.append(emit(i,p,cert));nodes+=cert[1]"
d="""proven[t]=f'{ns}.M{i}'
        model=cert if f'Raw56{tag}Automata{len(imports):02}' in ORIGINAL else quotient(cert)
        validate(p,model);parts.append(emit(i,p,model));nodes+=cert[1]"""
assert a in s and c in s
p.write_text(s.replace(a,b).replace(c,d))
