"""Exact dispatch of custom LE witnesses and explicit conditional tree joins."""
from pathlib import Path
import base64,hashlib,lzma
from shutil import copyfile
from prepare_semantic_branch import Builder
from unpack_le_sweeps import unpack

ROOT=Path(__file__).resolve().parent

def custom_le(branch,out):
    """Map frozen normalized open indices to checked Lean theorem terms.
    Audit.proven independently compares literal tables.
    """
    result={}
    def add(mod,indices,args=None,packed=False,scoped=False):
        if not packed and out.resolve()!=ROOT:
            copyfile(ROOT/(mod+'.lean'),out/(mod+'.lean'))
        for j,i in enumerate(indices):
            ns='BB6.Agent11'+mod+(f'.M{i}' if scoped else '')
            arg='' if args is None else ' '+args[j]
            assert i not in result
            result[i]=(mod,ns+'.table'+arg,ns+'.never'+arg)
    if branch=='0LE':
        add('Raw39LE1791',[1791,1800],['false','true'])
        add('Raw39LE5883',[5883])
        add('Raw39LE7634',[7634])
    elif branch=='1LE':
        add('Raw391LEBinaryFive',[19021,19049,19091,20727,20938],['.a','.b','.c','.d','.e'])
        add('Raw391LEBinarySix',[1897,2372,2529,2534,2535,2550],['.a','.b','.c','.d','.e','.f'])
        add('Raw391LE1837',[1837])
        add('Raw391LE2370',[2370])
        add('Raw391LEFTrio',[5774,5781,5789],['.a','.b','.c'])
        unpack(out)
        source=lzma.decompress(base64.b64decode((ROOT/'Raw391LEFiveSweep.lean.xz.b64').read_text()))
        assert hashlib.sha256(source).hexdigest()=='c69e36b505410b8d7d211a03c4befe1156cf3aada5c7bc7dbc4f65d68b0fb382'
        (out/'Raw391LEFiveSweep.lean').write_bytes(source)
        add('Raw391LEFiveSweep',[7492,7495,7527,7529,7532],packed=True,scoped=True)
        add('Raw391LEDFour',[5773,5783,5776,5782],packed=True,scoped=True)
        add('Raw391LEFMore',[5785,5775,5788],packed=True,scoped=True)
    return result

class ConditionalBuilder(Builder):
    """Only explicitly named residual leaves use hypotheses."""
    def __init__(self,out,branch,B,limit,far,special,tree,residual):
        super().__init__(out,branch,B,limit,far,special)
        self.pending=set()
        self.residual_nodes={}
        def mark(t):
            if t.tag=='open' and t.i in residual:
                assert t.i not in self.residual_nodes
                self.residual_nodes[t.i]=t
                found=True
            else:
                found=False
                for k in t.kids:
                    if mark(k): found=True
            if found:self.pending.add(t)
            return found
        mark(tree)
        assert set(self.residual_nodes)==set(residual)
    def hypotheses(self):
        return 'structure ResidualHypotheses : Prop where\n'+''.join(
            f'  h{i} : Bound {self.B} {t.p}\n'
            for i,t in sorted(self.residual_nodes.items()))
    def small(self,t):
        if t in self.pending:return t.tag=='open'
        return super().small(t)
    def bound_leaf(self,t,imports):
        if t in self.pending:
            assert t.tag=='open'
            self.stats['residual']+=1
            return f'theorem {t.name} (h : ResidualHypotheses) : Bound {self.B} {t.p} := h.h{t.i}\n'
        return super().bound_leaf(t,imports)
    def compose(self,t):
        code=super().compose(t)
        if t not in self.pending:return code
        code=code.replace(f'theorem {t.name} :',f'theorem {t.name} (h : ResidualHypotheses) :',1)
        pending_names={k.name for k in t.kids if k in self.pending}
        return '\n'.join(line+' h' if line.removeprefix('  · exact ') in pending_names else line
                         for line in code.splitlines())+'\n'
