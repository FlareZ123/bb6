/*
 * Universal affine-cost abstract interpreter for the source's fixed-length
 * stepPure proof blocks. Each symbolic natural is a constant plus a
 * nonnegative integer-linear combination of p,m,k,d, with all variables >=0.
 * Branches are accepted only if statically determined over the WHOLE domain.
 * An opaque right-tail sentinel rejects any computation that inspects R_tail.
 *
 * It proves affine formulas relative to the transcribed source transition and
 * machine-specific cost table, not a Lean kernel theorem.
 */
function verifyAffineBlocks() {
  const E=(c=0n,p=0n,m=0n,k=0n,d=0n)=>[c,p,m,k,d].map(BigInt);
  const C=v=>E(BigInt(v)),P=E(0n,1n),M=E(0n,0n,1n),K=E(0n,0n,0n,1n),D=E(0n,0n,0n,0n,1n);
  const plus=(a,b)=>a.map((v,i)=>v+b[i]),neg=a=>a.map(v=>-v);
  const sub=(a,b)=>plus(a,neg(b)),times=(n,a)=>a.map(v=>BigInt(n)*v);
  const eqE=(a,b)=>a.every((v,i)=>v===b[i]);
  const canonical=a=>a.join(",");
  function eqConst(e,n) {
    const diff=sub(e,C(n));
    if(diff.every(x=>x===0n))return true;
    if(diff[0]>0n&&diff.slice(1).every(x=>x>=0n))return false;
    if(diff[0]<0n&&diff.slice(1).every(x=>x<=0n))return false;
    if(diff.slice(1).every(x=>x===0n))return false;
    throw Error("affine equality undecided: "+canonical(e)+" vs "+n);
  }
  function geConst(e,n) {
    const diff=sub(e,C(n));
    if(diff.every(x=>x>=0n))return true;
    if(diff.every(x=>x<=0n)&&diff.some(x=>x<0n))return false;
    throw Error("affine inequality undecided: "+canonical(e)+" >= "+n);
  }
  function eqExpr(a,b) {
    const diff=sub(a,b);
    if(diff.every(x=>x===0n))return true;
    if(diff[0]>0n&&diff.slice(1).every(x=>x>=0n))return false;
    if(diff[0]<0n&&diff.slice(1).every(x=>x<=0n))return false;
    if(diff.slice(1).every(x=>x===0n))return false;
    throw Error("affine token equality undecided: "+canonical(a)+" vs "+canonical(b));
  }
  const I=v=>({t:"i",v:v===-1?null:C(v)});
  const run=v=>({t:"i",v});
  const b1=v=>({t:"b1",n:v}),r2=v=>({t:"r2",n:v}),r12=v=>({t:"r12",n:v});
  const tail={t:"Rtail"};
  function eqTok(a,b) {
    if(a.t==="Rtail"||b.t==="Rtail")throw Error("attempt to inspect unrestricted R_tail");
    if(a.t!==b.t)return false;
    if(a.t==="i")return a.v===null||b.v===null?a.v===b.v:eqExpr(a.v,b.v);
    return eqExpr(a.n,b.n);
  }
  const strip=(pre,xs)=>{
    if(xs.length<pre.length)return null;
    for(let i=0;i<pre.length;i++)if(!eqTok(pre[i],xs[i]))return null;
    return xs.slice(pre.length);
  };
  function bump(M0,right=false) {
    if(!M0.length)return [I(0)];
    const [t,...xs]=M0;
    if(t.t==="Rtail")throw Error("bumped unrestricted R_tail");
    if(t.t==="i")return [run(t.v===null?C(0):plus(t.v,C(1))),...xs];
    if(eqConst(t.n,0))return bump(xs,right);
    if(!geConst(t.n,1))throw Error("unreachable");
    const rest=sub(t.n,C(1));
    if(t.t==="b1"){
      return [I(1),I(1),...(eqConst(t.n,1)?[]:[b1(rest)]),...xs];
    }
    if(t.t==="r2")return right ?
      [I(1),I(1),I(1),r2(rest),...xs] :
      [I(2),I(0),I(1),r2(rest),...xs];
    return right ?
      [I(1),I(1),I(0),I(1),I(1),r12(rest),...xs]:
      [I(2),I(0),I(1),I(0),I(1),r12(rest),...xs];
  }
  const bumpL=x=>bump(x,false),bumpR=x=>bump(x,true);
  function peelPure(t,xs) {
    if(t.t==="Rtail")throw Error("peeled tail");
    if(t.t==="i")return [t,...xs];
    if(eqConst(t.n,0))return [t,...xs];
    if(!geConst(t.n,1))throw Error("unreachable");
    const rest=sub(t.n,C(1));
    if(t.t==="b1")return [I(0),I(1),b1(rest),...xs];
    if(t.t==="r2")return [I(1),I(0),I(1),r2(rest),...xs];
    return [I(1),I(0),I(1),I(0),I(1),r12(rest),...xs];
  }
  function prependZeroSym(n,acc) {
    for(let j=0;j<=16;j++)if(eqConst(n,j))return [...Array(j).fill(null).map(()=>I(-1)),...acc];
    throw Error("symbolic unbounded prependZeroSym "+canonical(n));
  }
  function stepElemBB(L,R,F) {
    if(!L.length)return [["CB",[],bumpR(R)],C(1),"BB:empty"];
    const [t,...xs]=L;
    if(t.t==="Rtail")throw Error("unrestricted Rtail on left");
    if(t.t==="i"&&t.v===null)return [["CB",xs,bumpR(R)],C(1),"BB:zero"];
    if(t.t!=="i")return [["BB",L,R],C(0),"BB:rep"];
    if(eqConst(t.v,0))return [["BB",xs,[I(0),...R]],C(F?8:6),"BB:run0"];
    if(eqConst(t.v,1))return [["BB",xs,[I(0),...bumpR(R)]],C(3),"BB:run1"];
    if(eqConst(t.v,2))return [["DL",xs,[I(0),I(0),...bumpR(R)]],C(5),"BB:run2"];
    if(eqConst(t.v,3))return [["BB",[I(0),I(-1),I(-1),...xs],bumpR(R)],C(9),"BB:run3"];
    if(geConst(t.v,4))return [["BB",[I(0),I(-1),run(sub(t.v,C(4))),...xs],bumpR(R)],C(9),"BB:run>=4"];
    throw Error("BB run branch");
  }
  function stepElemDL(L,R,F) {
    if(!L.length)return [["DL",[],R],C(0),"DL:empty"];
    const [t,...xs]=L;
    if(t.t==="Rtail")throw Error("unrestricted Rtail left");
    if(t.t==="i"&&t.v===null)return [["HALT",L,R],C(0),"DL:zero-halt"];
    if(t.t!=="i")return [["DL",L,R],C(0),"DL:rep"];
    if(eqConst(t.v,0))return [["BB",xs,bumpR(R)],C(1),"DL:run0"];
    if(eqConst(t.v,1))return [["DL",xs,[I(0),...bumpR(R)]],C(3),"DL:run1"];
    if(eqConst(t.v,2)&&R.length&&R[0].t==="i"&&R[0].v!==null){
      const d=R[0].v;
      return [["CB",[I(0),I(0),...prependZeroSym(plus(d,C(1)),xs)],R.slice(1)],
        plus(times(3,d),C(F?22:20)),"DL:run2/run"];
    }
    return [["DL",L,R],C(0),"DL:other"];
  }
  function stepElemCBrun0(L,R,F) {
    if(!R.length)return [["BB",[I(0),...bumpL(L)],[]],C(3),"CB:run0/empty"];
    const [t,...xs]=R;
    if(t.t==="Rtail")throw Error("CB run0 touches unrestricted R_tail");
    if(t.t==="i"&&t.v===null)return [["BB",[I(0),...bumpL(L)],xs],C(3),"CB:run0/zero"];
    if(t.t==="i") {
      if(eqConst(t.v,0))return [["BB",[I(0),I(-1),...bumpL(L)],xs],C(6),"CB:run0/run0"];
      if(geConst(t.v,1))return [["CB",[I(0),I(0),...prependZeroSym(sub(t.v,C(1)),bumpL(L))],xs],
        plus(times(3,sub(t.v,C(1))),C(F?21:19)),"CB:run0/runpos"];
    }
    return [["CB",L,[I(0),t,...xs]],C(0),"CB:run0/rep"];
  }
  function stepElemCB(L,R,F) {
    if(!R.length)return [["DL",bumpL(L),[I(0)]],C(2),"CB:empty"];
    const [t,...xs]=R;
    if(t.t==="Rtail")throw Error("CB touches unrestricted R_tail");
    if(t.t==="i"&&t.v===null)return [["DL",bumpL(L),bumpR(xs)],C(2),"CB:zero"];
    if(t.t==="i") {
      if(eqConst(t.v,0))return stepElemCBrun0(L,xs,F);
      if(eqConst(t.v,1))return [["CB",[I(0),...bumpL(L)],xs],C(3),"CB:run1"];
      if(eqConst(t.v,2))return [["BB",bumpL(L),[I(0),I(-1),...xs]],C(5),"CB:run2"];
      if(geConst(t.v,3))return [["BB",bumpL(L),[I(0),run(sub(t.v,C(3))),...xs]],C(5),"CB:run>=3"];
    }
    return [["CB",L,R],C(0),"CB:rep"];
  }
  function stepPure(s,F) {
    const [mode,L,R]=s;
    if(mode==="HALT")return [s,C(0),"HALT"];
    if(mode==="BB"){
      if(!L.length||L[0].t==="i")return stepElemBB(L,R,F);
      const [t,...xs]=L;
      if(t.t==="b1")return [["BB",xs,[t,...R]],times(F?11:9,t.n),"BB:B1"];
      const rs=strip([I(0),I(1)],R);
      if(rs!==null)return [["BB",xs,[I(0),I(1),t,...rs]],
        times(t.t==="r2"?(F?14:12):(F?25:21),t.n),t.t==="r2"?"BB:C2":"BB:C12"];
      return stepElemBB(peelPure(t,xs),R,F);
    }
    if(mode==="DL")return !L.length?[s,C(0),"DL:empty"]:stepElemDL(peelPure(L[0],L.slice(1)),R,F);
    if(!R.length||R[0].t==="i"&&R[0].v===null)return stepElemCB(L,R,F);
    const [t,...xs]=R;
    if(t.t==="Rtail")throw Error("CB touches unrestricted R_tail");
    if(t.t==="i"){
      if(eqConst(t.v,0))return stepElemCBrun0(L,xs,F);
      if(eqConst(t.v,1)||eqConst(t.v,2))return stepElemCB(L,R,F);
      if(geConst(t.v,3))return [["BB",bumpL(L),[I(0),run(sub(t.v,C(3))),...xs]],C(5),"CB:run>=3"];
    }
    if(t.t==="b1"){
      const r3=strip([I(0),I(0),I(1)],L);
      if(r3!==null)return [["CB",[I(0),b1(plus(t.n,C(1))),...r3],xs],times(F?21:19,t.n),"CB:B1-inc"];
      const r=strip([I(0)],L);
      return r===null?[s,C(0),"CB:B1-none"]:[["CB",[I(0),t,...r],xs],times(F?21:19,t.n),"CB:B1"];
    }
    if(t.t==="r2"){
      const r4=strip([I(0),I(1),I(0),I(1)],L);
      if(r4!==null)return [["CB",[I(0),r2(plus(t.n,C(1))),...r4],xs],times(F?24:22,t.n),"CB:B2-inc"];
      const r=strip([I(0)],L);
      return r===null?[s,C(0),"CB:B2-none"]:[["CB",[I(0),t,...r],xs],times(F?24:22,t.n),"CB:B2"];
    }
    const r=strip([I(0)],L);
    return r===null?[s,C(0),"CB:B12-none"]:[["CB",[I(0),t,...r],xs],times(F?45:41,t.n),"CB:B12"];
  }
  const sep3A=[I(0),I(1),I(2)],sep3B=[I(0),I(-1),I(1)];
  const stateA0=(k,d)=>["CB",[I(0),I(0),I(1),I(1),I(0),I(1),I(1),I(1),I(0),I(-1),I(1),b1(k),I(0)],[run(d),tail]];
  const stateA=(m,k,d)=>["CB",[I(0),I(0),I(1),I(1),I(0),I(1),I(1),I(1),I(0),I(1),r12(m),I(1),I(0),I(1),I(0),I(-1),I(1),b1(k),I(0)],[run(d),tail]];
  const stateC=(p,k,d)=>["CB",[I(0),I(0),I(1),r2(p),I(0),I(1),I(1),I(1),b1(k),I(0)],[I(-1),run(d),tail]];
  const stateB=(sa,ma,p,m,k,d)=>["CB",[I(0),I(0),I(1),r2(p),I(1),...sa,r12(m),I(1),I(0),I(1),...ma,b1(k),I(0)],[I(-1),run(d),tail]];
  const blocks=[];
  for(const F of [true,false]){
    const lab=F?"F424":"F412";
    const tasks=[
      ["A0",46,stateA0(plus(K,C(1)),plus(D,C(6))),E(F?314:284,0n,0n,F?32:28)],
      ["A",66,stateA(M,plus(K,C(1)),plus(D,C(6))),E(F?454:408,0n,F?140:124,F?32:28)],
      ["C",46,stateC(plus(P,C(3)),plus(K,C(1)),D),E(F?486:434,F?76:68,0n,F?64:56)],
    ];
    for(const [sa,st] of [["A",sep3A],["B",sep3B]])for(const [ma,mt] of [["A",sep3A],["B",sep3B]]){
      const id=sa+ma;
      const length={AA:126,AB:118,BA:106,BB:98}[id];
      const constants=F?{AA:1048,AB:978,BA:896,BB:826}:{AA:942,AB:880,BA:806,BB:744};
      tasks.push(["B"+id,length,stateB(st,mt,plus(P,C(1)),plus(M,C(2)),plus(K,C(1)),D),
        E(constants[id],F?152:136,F?140:124,F?32:28)]);
    }
    for(const [name,length,init,expected] of tasks){
      let s=init,total=C(0),trace=[];
      try {
        for(let j=0;j<length;j++){
          const [next,c,kind]=stepPure(s,F);total=plus(total,c);trace.push(kind);s=next;
        }
      }catch(err){throw Error(lab+" "+name+" step "+trace.length+" trace "+trace.slice(-10).join(",")+" : "+err.message);}
      if(!eqE(total,expected))throw Error(lab+" "+name+" computed "+canonical(total)+" expected "+canonical(expected));
      const tailCount=s[2].filter(t=>t.t==="Rtail").length;
      if(tailCount!==1)throw Error("R_tail was not preserved");
      blocks.push({machine:lab,block:name,iterations:length,affine:canonical(total),trace:trace.join("|")});
    }
  }
  return blocks;
}
if(typeof module!=="undefined" && module.exports)module.exports=verifyAffineBlocks;
verifyAffineBlocks;
