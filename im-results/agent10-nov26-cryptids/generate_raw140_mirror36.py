"""Extend a copy of the pinned original module, preserving its trusted definitions.
The added theorem concerns a different initial state, never the original entry.
"""
from pathlib import Path
import sys
root=Path(sys.argv[1])
fragment=Path(sys.argv[2])
name="M_1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH"
folder=root/"BusyBeaver/BB6/NonHalt"
s=(folder/(name+".lean")).read_text()
assert s.count("namespace BusyBeaver."+name)==1
assert s.count("end BusyBeaver."+name)==1
s=s.replace("BusyBeaver."+name,"BusyBeaver.Raw140Mirror36")
s=s.replace("end BusyBeaver.Raw140Mirror36",fragment.read_text()+"\nend BusyBeaver.Raw140Mirror36")
(folder/"Raw140Mirror36.lean").write_text(s)
