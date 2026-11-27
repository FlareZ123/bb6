"""Exact dispatch of custom LE witnesses and explicit conditional tree joins."""
from pathlib import Path
import base64,hashlib,json,lzma
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
        source=lzma.decompress(base64.b64decode((ROOT/'Raw39LE3414.lean.xz.b64').read_text()))
        assert hashlib.sha256(source).hexdigest()=='9624031627f50c7ab9e607119b402b57a76aad7a1963f5d2707b98675122c91a'
        (out/'Raw39LE3414.lean').write_bytes(source)
        add('Raw39LE3414',[3414],packed=True)
        source=lzma.decompress(base64.b64decode((ROOT/'Raw39LE3334.lean.xz.b64').read_text()))
        assert hashlib.sha256(source).hexdigest()=='ebbe7b389ab65e2ea3877f604010b9aa911e781b1cc8bea27e0b956cd960dd68'
        (out/'Raw39LE3334.lean').write_bytes(source)
        add('Raw39LE3334',[3334],packed=True)
    elif branch=='1LE':
        gap_sources=json.loads(lzma.decompress(base64.b64decode((ROOT/'Raw391LEGapSystem.json.xz.b64').read_text())))
        gap_hashes={'Raw391LEGapMacros.lean':'bb37b243540b04fee8959850e8fc3b005aec670c768864268e3e10b934fe371a','Raw391LEGapSystem.lean':'3e4e6420568daf8e65f784742b29d3a1797aa3e82efea21517bf063de79536a7'}
        assert set(gap_sources)==set(gap_hashes)
        for name,code in gap_sources.items():
            assert hashlib.sha256(code.encode()).hexdigest()==gap_hashes[name]
            (out/name).write_bytes(code.encode())
        source=lzma.decompress(base64.b64decode((ROOT/'Raw391LEGapGrammar.lean.xz.b64').read_text()))
        assert hashlib.sha256(source).hexdigest()=='627855a60e4c2f7df514aacd99a90365997e771c6f3c950d9da5f6be55676de0'
        (out/'Raw391LEGapGrammar.lean').write_bytes(source)
        ns='BB6.Agent11Raw39Gap'
        for i in (5777,5779,5787):
            result[i]=('Raw391LEGapGrammar',f'{ns}.table .v{i}',f'{ns}.never .v{i}')
        source=lzma.decompress(base64.b64decode((ROOT/'Raw391LE8865.lean.xz.b64').read_text()))
        assert hashlib.sha256(source).hexdigest()=='ddb1c6799ae01327774bdd7e798f5be707dbfc62430f052a442c5e0090203427'
        (out/'Raw391LE8865.lean').write_bytes(source)
        add('Raw391LE8865',[8865],packed=True)
        source=lzma.decompress(base64.b64decode((ROOT/'Raw391LE7080.lean.xz.b64').read_text()))
        assert hashlib.sha256(source).hexdigest()=='350dcfad9767aca9a992640033b4c747eaeb0abd0894eee378072ab7a699170f'
        (out/'Raw391LE7080.lean').write_bytes(source)
        add('Raw391LE7080',[7080],packed=True)
        source=lzma.decompress(base64.b64decode((ROOT/'Raw391LE12198.lean.xz.b64').read_text()))
        assert hashlib.sha256(source).hexdigest()=='8edcd67da391ccd2549017db97541492e8e1b15cf73647c8d251c870b0363321'
        (out/'Raw391LE12198.lean').write_bytes(source)
        add('Raw391LE12198',[12198],packed=True)
        source=lzma.decompress(base64.b64decode((ROOT/'Raw391LEFourPhase.lean.xz.b64').read_text()))
        assert hashlib.sha256(source).hexdigest()=='f6b4214ffd898eac2882a23b9555976a1d995e04a2ff7f4d0e77b3f6bdbec2da'
        (out/'Raw391LEFourPhase.lean').write_bytes(source)
        add('Raw391LEFourPhase',[15741,15742,15743,22215],['.a','.b','.c','.d'],packed=True)
        add('Raw391LEDriftPair',[21614,21623],['.a','.b'])
        add('Raw391LEBinaryFive',[19021,19049,19091,20727,20938],['.a','.b','.c','.d','.e'])
        add('Raw391LEBinarySix',[1897,2372,2529,2534,2535,2550],['.a','.b','.c','.d','.e','.f'])
        add('Raw391LE1837',[1837])
        add('Raw391LE2370',[2370])
        add('Raw391LEFTrio',[5774,5781,5789],['.a','.b','.c'])
        source=lzma.decompress(base64.b64decode((ROOT/'Raw391LEPairTriple.lean.xz.b64').read_text()))
        assert hashlib.sha256(source).hexdigest()=='d1544eb03d92ef5cd18d5761fa4a02290d3d787167cdebae1bc9f6b529555248'
        (out/'Raw391LEPairTriple.lean').write_bytes(source)
        add('Raw391LEPairTriple',[18789,18790,20550],['.a','.b','.c'],packed=True)
        source=lzma.decompress(base64.b64decode((ROOT/'Raw391LEBlockRuns.lean.xz.b64').read_text()))
        assert hashlib.sha256(source).hexdigest()=='3cfb05edb3242a7eae387db247eaf12428dc0f9bb0ed1e72a247b48a8269be44'
        (out/'Raw391LEBlockRuns.lean').write_bytes(source)
        add('Raw391LEBlockRuns',[6270,16538],['.a','.b'],packed=True)
        unpack(out)
        source=lzma.decompress(base64.b64decode((ROOT/'Raw391LEFiveSweep.lean.xz.b64').read_text()))
        assert hashlib.sha256(source).hexdigest()=='c69e36b505410b8d7d211a03c4befe1156cf3aada5c7bc7dbc4f65d68b0fb382'
        (out/'Raw391LEFiveSweep.lean').write_bytes(source)
        add('Raw391LEFiveSweep',[7492,7495,7527,7529,7532],packed=True,scoped=True)
        source=lzma.decompress(base64.b64decode((ROOT/'Raw391LEMoreSweep.lean.xz.b64').read_text()))
        assert hashlib.sha256(source).hexdigest()=='499ace74395452b59ce9a6e3aa8e4bc0b82c0737c0f78284f786336b29468467'
        (out/'Raw391LEMoreSweep.lean').write_bytes(source)
        add('Raw391LEMoreSweep',[25795,9206,15745],packed=True,scoped=True)
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
