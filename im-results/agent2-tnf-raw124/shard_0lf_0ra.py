"""Split generated Raw124ZeroLF0RA.lean into independent Lean modules.
Invoke on the directory containing the generated source; the final module retains
its original public theorem names. This avoids monolithic elaboration OOM.
"""
import re
import sys
from pathlib import Path

root = Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent
p = root/'Raw124ZeroLF0RA.lean'
s = p.read_text()
a = s.index('\ndef kid00')
b = s.index('\ndef kids : Move')
header = s[:a]
footer = '\nend BB6.Agent2Raw124ZeroLF0RA\n'
(root/'Raw124ZeroLF0RABase.lean').write_text(header+footer)
begin = '''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw124ZeroLF0RA
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent2Raw124FastAudit
'''
kids = re.split(r'(?=\ndef kid\d\d : Audit)',s[a:b])[1:]
assert len(kids)==24
for i,k in enumerate(kids):
    (root/f'Raw124ZeroLF0RAKid{i:02}.lean').write_text('import Raw124ZeroLF0RABase\n'+begin+k+footer)
p.write_text(''.join(f'import Raw124ZeroLF0RAKid{i:02}\n' for i in range(24))+begin+s[b:])
