"""Packed, reproducible FAR witnesses for complete five-hole parents.

The character stream binds to the exact ordered n-gram leaf roster via SHA256.
Every reconstructed FAR witness is checked by the ordinary Lean kernel.
"""
from pathlib import Path
import hashlib
import string
from generateOneFAR import codes, fmt, saturate
D=Path(__file__).resolve().parent
DATA={
    "0RB": {
        "key": 999,
        "sha": "68a2dfd194691a7d3cd622129622392f70cc48d8747a01be7534600098f9bd1d",
        "dict": "0:0101,0:00,0:0123432444,0:01230321,1:00,0:0100,0:0121343323,1:0102343134,0:0121343322,1:010202,0:010202,1:012101,0:01023333,0:01230323,1:0101,1:0102342134,1:01211321,0:012101,1:01233123,0:0123032424,1:0102341134,1:01210321,1:01230123,0:01230320,0:0102343333,0:01200320,0:0123034303,1:01023221,1:01021313,1:01213321,1:0121342121,1:0102343124,0:0120032401,0:01200323,0:010200,1:0102340234,0:01020313,0:03616462615352,0:0123042121,0:0123040323,0:0123032421,0:052301242423,0:0123430244",
        "grams": "2222222b22b2447444f422oc2422222cc2cc222?222222222222222222222111e11111111122fk2k2242224f42622868222l2226866l98688l922b224t4be4e777777774e4u44e477?777?7111111222b2211111111111111111112111111111b1111111m1111122?k200000022222111111111111b22g?gggfg4v444f41100011101000011111111111111100003000003000000000000000a0001110100000011110300001111h1103n3nn0a0011111111111000000000000000000111101102000000000000000000111111111000000400003333000000000ppwx0505500000000555a55000000000000011011003300000000000000000000111111211011111103dq333330000000011111111112222222222664222222r4r2o2c42222222222ccc22222i22222222222m222200222222222222211111111220y002222i2222682882222222626668e88222222221011111222221111111222m229929222222292229i90000002b2111111a11111z111a211111111111111111111100000009929222111112222111a111e11a1922ass00A0000042224i41222b22111101122222111111102b21111110011111111111011022211161000111111115555533333555505333j300000000000000a0000000000011111103001111111101111001111111111011103333j30a0011111111111111000002000000000000000200000000022222211110112222222211111110022222110111000000000000000000222222222111116110000000000000000001111111101110000000000003dq333333000000000000Bd3d3d3j30000000000h000000000000000011111111101111111110000011100Cd33DE300h00h0000000000000a000001111116110111111111110F33d3d3j30000000111111111",
        "hard": "00000G000?000?????",
        "tables": "0RE0RF1RD---0RE 0RE0RF1RD---1RE 0RE1RF1RD---0RE 0RE1RF1RD---1LE 0RE1RF1RD---1RE 0RE1RD1RF---1RB 1LE1RF0RA---0RE 1RE0RF1RD---0RE 1RE0RF1RD---1RE 1RE0RF1RF---1RD 1RE1RF1RD---0RE 1RE1RF1RD---1LE 1RE1RF1RD---1RE 1RE1LE1RF---1RD 1RE1RD0RF---0RA 1RE1RD0RF---1LA 1RE1RD1RF---0LD 1RE1RD1RF---1RD"
    },
    "1LC": {
        "key": 1003,
        "sha": "e161605c4ea99ea72ed1af231190c5aedebf1117fb17febdfb0c707313e084de",
        "dict": "0:00,0:0101,0:0123441344,1:0102343134,0:01023333,0:01023202,0:0100,1:0100,1:0123414144,0:0123441444,1:0121342121,0:01023102,1:0123410101,0:0123014444,0:0655745553557142,0:010201",
        "grams": "2724333329a27201000113?300011100000000011000?b100001111011011174111110005151022222000100666611000000010110101?0000000?0000000?000",
        "hard": "c??d?4?44ef5588?85",
        "tables": "0LE0RF---1RE1RB 0RE0RF---0RD1RF 0RE0RF---0RD1RA 0RE1RD0RF---1LE 0RE1RD0RF---1RE 0RE1RD0RF---1LC 0RE1RD0RF---1RA 0RE1RD1RF---0RE 1LE1RD0RF---1RE 1LE1RD1RF---0RE 1RE0RF1LB---1RD 1RE0RF------1RB 1RE1RF0RA---0LE 1RE0RD0RF---1LE 1RE0RD0RF---1RE 1RE0RD0RF---1RB 1RE0RD1RF---1LB 1RE1LD0RF---1RB"
    }
}

def generate(branch,grams):
    a=DATA[branch]
    assert len(grams)==len(a["grams"])
    assert hashlib.sha256("\n".join(grams).encode()).hexdigest()==a["sha"]
    assert len(set(grams))==len(grams)
    prefix="1RB1LC1RC0LD1LA0RB"+branch
    root="Agent46Raw13"+("Zero" if branch[0]=="0" else "One")+branch[1:]
    ns="BB6."+root
    alphabet=string.digits+string.ascii_letters
    ds=[(int(x.split(":")[0]),list(map(int,x.split(":")[1]))) for x in a["dict"].split(",")]
    hard=[prefix+x for x in a["tables"].split()]
    rows=[(a["key"]*1000+i,t,c) for i,(t,c) in enumerate(zip(hard,a["hard"])) if c!="?"]
    rows += [(a["key"]*10000+1000+i,t,c) for i,(t,c) in enumerate(zip(grams,a["grams"])) if c!="?"]
    proven={}
    modules=[]
    for j in range(0,len(rows),80):
        name=root+"FAR"+str(j//80)
        modules.append(name)
        body=["import FastFAR","import Agent46CanonicalCut","set_option maxRecDepth 100000","set_option maxHeartbeats 0","namespace "+ns,"open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut","open BB6Coverage.FAR"]
        for i,raw,c in rows[j:j+80]:
            assert raw not in proven and len(raw)==36
            rev,dfa=ds[alphabet.index(c)]
            m0,m1,z=saturate(codes(raw),dfa,rev)
            p=f"pF{i}"
            cert=f"cF{i}"
            h=f"okF{i}"
            pp=f"(reflectPartial {p})" if rev else p
            body += [f"def {p} : PartialMachine := FAR.fromCodes {fmt(codes(raw))}",
                     f"def {cert} : Data {len(dfa)//2} := ⟨0,{fmt(dfa)},{fmt(m0)},{fmt(m1)},{z}⟩",
                     f"theorem {h} : ({cert}).fastValid {pp} = true := by decide"]
            sound=f"({cert}).sound {pp} (({cert}).fastValid_sound {pp} {h})"
            proof=f"reflectNever m ({sound} (reflectTable m) (reflectCompatible {p} m hm))" if rev else f"{sound} m hm"
            body += [f"theorem neverF{i} (m : Machine) (hm : compatible {p} m) : NeverHalts m := {proof}"]
            proven[raw]=i
        body.append("end "+ns)
        (D/(name+".lean")).write_text("\n".join(body)+"\n")
    assert len(proven)=={"0RB":1325,"1LC":137}[branch]
    return proven,modules
