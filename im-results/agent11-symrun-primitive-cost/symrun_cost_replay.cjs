/*
 * Deterministic SymRunEngine state replay for upstream Cryptids F424/F412.
 *
 * Source pin: google-deepmind/cryptids @
 * 3647718b5df22e1a61462dec0376bd204526285a
 *
 * This validates the symbolic stepSym trajectory against the upstream
 * symChk checkpoints and records maximum encoded-state sizes. It is a
 * JavaScript translation for reproducible computational analysis, not a
 * Lean proof and not a primitive-step cost calculation.
 *
 * Usage in Node:
 *   const replay = require("./symrun_state_replay.cjs");
 *   replay(url => fetch(url).then(r => r.text()))
 *     .then(x => console.log(JSON.stringify(x, null, 2)));
 */

const run = async function(fetchText) {
  const base = "https://raw.githubusercontent.com/google-deepmind/cryptids/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/Halt/";
  const I = v => ({t:"i",v:BigInt(v)});
  const B1 = n => ({t:"b1",n});
  const R2 = n => ({t:"r2",n});
  const R12 = n => ({t:"r12",n});
  let maxZeroExpansion = 0n;
  const eqTok = (a,b) => a.t===b.t && (a.t==="i" ? a.v===b.v : a.n===b.n);
  const strip = (pre,xs) =>
    pre.length<=xs.length && pre.every((t,i)=>eqTok(t,xs[i])) ? xs.slice(pre.length) : null;

  const eatStep = (blk,tag,k,xs) => {
    if (!xs.length) return null;
    if (xs[0].t===tag) return {k:k+xs[0].n,rest:xs.slice(1)};
    const rest=strip(blk,xs);
    return rest===null ? null : {k:k+1n,rest};
  };
  const eatFuel = (blk,tag,mkRep,k,xs) => {
    let acc=k, rest=xs;
    for (let i=0;i<4;i++) {
      const e=eatStep(blk,tag,acc,rest);
      if (!e) return [mkRep(acc),...rest];
      acc=e.k; rest=e.rest;
    }
    return [mkRep(acc),...rest];
  };
  const eatB1=(k,x)=>eatFuel([I(0),I(1)],"b1",B1,k,x);
  const eatC2=(p,x)=>eatFuel([I(1),I(0),I(1)],"r2",R2,p,x);
  const eatB2=(p,x)=>eatFuel([I(0),I(1),I(1)],"r2",R2,p,x);
  const eatC12=(m,x)=>eatFuel([I(1),I(0),I(1),I(0),I(1)],"r12",R12,m,x);
  const eatB12R=(m,x)=>eatFuel([I(0),I(1),I(0),I(1),I(1)],"r12",R12,m,x);

  function peelTok(t,xs) {
    if (t.t==="i") return [t,...xs];
    if (t.t==="b1") return t.n===0n ? [B1(0n),...xs] :
      [I(0),I(1),...(t.n===1n?[]:[B1(t.n-1n)]),...xs];
    if (t.t==="r2") return t.n===0n ? [R2(0n),...xs] :
      [I(1),I(0),I(1),...(t.n===1n?[]:[R2(t.n-1n)]),...xs];
    return t.n===0n ? [R12(0n),...xs] :
      [I(1),I(0),I(1),I(0),I(1),...(t.n===1n?[]:[R12(t.n-1n)]),...xs];
  }
  const peelL=L=>L.length ? peelTok(L[0],L.slice(1)) : [];

  function splitB2(xs) {
    let p=0n,rest=xs;
    for (let i=0;i<32;i++) {
      const r=strip([I(0),I(1),I(1)],rest);
      if (r===null) break;
      p++; rest=r;
    }
    return [p,rest];
  }

  const sep3A=[I(0),I(1),I(2)];
  const sep3B=[I(0),I(-1),I(1)];
  function popSep3(xs) {
    let rest=strip(sep3A,xs);
    if (rest!==null) return {sep:sep3A,rest};
    rest=strip(sep3B,xs);
    return rest===null ? null : {sep:sep3B,rest};
  }
  const popRep2=xs=>xs.length&&xs[0].t==="r2" ? {n:xs[0].n,rest:xs.slice(1)} : null;
  const popRep12=xs=>xs.length&&xs[0].t==="r12" ? {n:xs[0].n,rest:xs.slice(1)} : null;
  const popRepB1=xs=>xs.length&&xs[0].t==="b1" ? {n:xs[0].n,rest:xs.slice(1)} : null;
  function matchEndB1(xs) {
    const p=popRepB1(xs);
    if (!p) return null;
    const rest=strip([I(0)],p.rest);
    return rest!==null&&rest.length===0 ? p.n : null;
  }

  function bumpSymL(M) {
    if (!M.length) return [I(0)];
    const [t,...xs]=M;
    if (t.t==="i") return [I(t.v===-1n?0n:t.v+1n),...xs];
    if (t.t==="b1") {
      if (t.n===0n) return bumpSymL(xs);
      return [I(1),I(1),...(t.n===1n?[]:[B1(t.n-1n)]),...xs];
    }
    if (t.t==="r2") {
      if (t.n===0n) return bumpSymL(xs);
      return [I(2),I(0),I(1),R2(t.n-1n),...xs];
    }
    if (t.n===0n) return bumpSymL(xs);
    return [I(2),I(0),I(1),I(0),I(1),R12(t.n-1n),...xs];
  }
  function bumpSymR(M) {
    if (!M.length) return [I(0)];
    const [t,...xs]=M;
    if (t.t==="i") return [I(t.v===-1n?0n:t.v+1n),...xs];
    if (t.t==="b1") {
      if (t.n===0n) return bumpSymR(xs);
      return [I(1),I(1),...(t.n===1n?[]:[B1(t.n-1n)]),...xs];
    }
    if (t.t==="r2") {
      if (t.n===0n) return bumpSymR(xs);
      return [I(1),I(1),I(1),R2(t.n-1n),...xs];
    }
    if (t.n===0n) return bumpSymR(xs);
    return [I(1),I(1),I(0),I(1),I(1),R12(t.n-1n),...xs];
  }
  function prependZeroSym(n,acc) {
    if (n>maxZeroExpansion) maxZeroExpansion=n;
    if (n>1000000n) throw new Error("unexpected large zero expansion: "+n);
    return [...Array(Number(n)).fill(0).map(()=>I(-1)),...acc];
  }

  function stepElemBB_raw(L,R) {
    if (!L.length) return ["CB",[],bumpSymR(R)];
    const [t,...xs]=L;
    if (t.t==="i") {
      if (t.v===-1n) return ["CB",xs,bumpSymR(R)];
      if (t.v===0n) return ["BB",xs,[I(0),...R]];
      if (t.v===1n) return ["BB",xs,[I(0),...bumpSymR(R)]];
      if (t.v===2n) return ["DL",xs,[I(0),I(0),...bumpSymR(R)]];
      if (t.v===3n) return ["BB",[I(0),I(-1),I(-1),...xs],bumpSymR(R)];
      return ["BB",[I(0),I(-1),I(t.v-4n),...xs],bumpSymR(R)];
    }
    return ["BB",L,R];
  }
  function stepElemDL_raw(L,R) {
    if (!L.length) return ["DL",[],R];
    const [t,...xs]=L;
    if (t.t==="i") {
      if (t.v===-1n) return ["HALT",L,R];
      if (t.v===0n) return ["BB",xs,bumpSymR(R)];
      if (t.v===1n) return ["DL",xs,[I(0),...bumpSymR(R)]];
      if (t.v===2n && R.length && R[0].t==="i" && R[0].v>=0n)
        return ["CB",[I(0),I(0),...prependZeroSym(R[0].v+1n,xs)],R.slice(1)];
    }
    return ["DL",L,R];
  }
  function stepElemCB_run0_raw(L,R1) {
    if (!R1.length) return ["BB",[I(0),...bumpSymL(L)],[]];
    const [t,...xs]=R1;
    if (t.t==="i") {
      if (t.v===-1n) return ["BB",[I(0),...bumpSymL(L)],xs];
      if (t.v===0n) return ["BB",[I(0),I(-1),...bumpSymL(L)],xs];
      return ["CB",[I(0),I(0),...prependZeroSym(t.v-1n,bumpSymL(L))],xs];
    }
    return ["CB",L,[I(0),t,...xs]];
  }
  function stepElemCB_raw(L,R) {
    if (!R.length) return ["DL",bumpSymL(L),[I(0)]];
    const [t,...xs]=R;
    if (t.t==="i") {
      if (t.v===-1n) return ["DL",bumpSymL(L),bumpSymR(xs)];
      if (t.v===0n) return stepElemCB_run0(L,xs);
      if (t.v===1n) return ["CB",[I(0),...bumpSymL(L)],xs];
      if (t.v===2n) return ["BB",bumpSymL(L),[I(0),I(-1),...xs]];
      return ["BB",bumpSymL(L),[I(0),I(t.v-3n),...xs]];
    }
    return ["CB",L,R];
  }
  function stepElemSym(mode,L,R) {
    if (mode==="BB") return stepElemBB(L,R);
    if (mode==="DL") return stepElemDL(L,R);
    if (mode==="CB") return stepElemCB(L,R);
    return ["HALT",L,R];
  }

  function sweepBB_raw(L,R) {
    if (!L.length) return stepElemBB([],R);
    const [t,...xs]=L;
    if (t.t==="i") {
      if (t.v===-1n) return stepElemBB(L,R);
      if (t.v===0n) return sweepBB(xs,[I(0),...R]);
      if (t.v===1n) return sweepBB(xs,[I(0),...bumpSymR(R)]);
      return stepElemBB(L,R);
    }
    if (t.t==="b1") return sweepBB(xs,eatB1(t.n,R));
    if (t.t==="r2") {
      const rest=strip([I(0),I(1)],R);
      return rest===null ? stepElemBB(peelTok(t,xs),R) :
        sweepBB(xs,[I(0),I(1),...eatB2(t.n,rest)]);
    }
    const rest=strip([I(0),I(1)],R);
    return rest===null ? stepElemBB(peelTok(t,xs),R) :
      sweepBB(xs,[I(0),I(1),...eatB12R(t.n,rest)]);
  }
  function sweepCB_raw(L,R) {
    if (!R.length) return [L,[]];
    const [t,...xs]=R;
    if (t.t==="i") {
      if (t.v===-1n) return [L,R];
      if (t.v===0n && xs.length && xs[0].t==="i" && xs[0].v===1n)
        return sweepCB([I(0),I(0),...bumpSymL(L)],xs.slice(1));
      if (t.v===0n) return [L,R];
      if (t.v===1n) return sweepCB([I(0),...bumpSymL(L)],xs);
      return [L,R];
    }
    const rest=strip([I(0)],L);
    if (rest===null) return [L,R];
    if (t.t==="b1") return sweepCB([I(0),...eatB1(t.n,rest)],xs);
    if (t.t==="r2") return sweepCB([I(0),...eatC2(t.n,rest)],xs);
    return sweepCB([I(0),...eatC12(t.n,rest)],xs);
  }

  const finishThenBB=s=>s[0]==="BB" ? sweepBB(s[1],s[2]) : s;
  const stepElemThenBB=(mode,L,R)=>finishThenBB(stepElemSym(mode,L,R));
  const aPrefix=[I(0),I(0),I(1),I(1),I(0),I(1),I(1),I(1),I(0),I(-1),I(1)];

  function tryRuleA_raw(L,d,Rtail) {
    const rest=strip(aPrefix,L);
    if (rest===null) return stepElemThenBB("CB",L,[I(d),...Rtail]);
    const k=matchEndB1(rest);
    if (k===null) return stepElemThenBB("CB",L,[I(d),...Rtail]);
    const n1=d/6n;
    if (n1<2n || n1>k) return stepElemThenBB("CB",L,[I(d),...Rtail]);
    return ["CB",
      [I(0),I(0),I(1),I(1),I(0),I(1),I(1),I(1),I(0),I(1),R12(n1-1n),
       I(1),I(0),I(1),I(0),I(-1),I(1),B1(k-n1),I(0)],
      [I(d-6n*n1),...Rtail]
    ];
  }

  function afterSplitB2_raw(L,d2,Rtail,res) {
    const [p,rest]=res;
    const q=popSep3(rest);
    if (!q) return stepElemThenBB("CB",L,[I(-1),I(d2),...Rtail]);
    const m12=popRep12(q.rest);
    if (!m12) return stepElemThenBB("CB",L,[I(-1),I(d2),...Rtail]);
    const rest2=strip([I(1),I(0),I(1)],m12.rest);
    if (rest2===null) return stepElemThenBB("CB",L,[I(-1),I(d2),...Rtail]);
    const q2=popSep3(rest2);
    if (!q2) return stepElemThenBB("CB",L,[I(-1),I(d2),...Rtail]);
    const k1=matchEndB1(q2.rest);
    if (k1===null || p<2n || m12.n<2n || m12.n>k1)
      return stepElemThenBB("CB",L,[I(-1),I(d2),...Rtail]);
    const n3=m12.n-1n;
    return ["CB",
      [I(0),I(0),I(1),R2(p+2n*n3-1n),I(1),...q.sep,
       R12(1n),I(1),I(0),I(1),...q2.sep,B1(k1-n3),I(0)],
      [I(-1),I(d2+4n*n3),...Rtail]
    ];
  }

  function tryRuleB(L,d2,Rtail) {
    const rest=strip([I(0)],L);
    return rest===null ? stepElemThenBB("CB",L,[I(-1),I(d2),...Rtail]) :
      afterSplitB2(L,d2,Rtail,splitB2(rest));
  }

  function tryRuleBC_raw(L,d2,Rtail) {
    const rest1=strip([I(0),I(0),I(1)],L);
    if (rest1!==null) {
      const p=popRep2(rest1);
      if (p) {
        const rest2=strip([I(0),I(1),I(1),I(1)],p.rest);
        if (rest2!==null) {
          const k1=matchEndB1(rest2);
          if (k1!==null && p.n>=3n && k1>=1n) {
            const n4=p.n-2n;
            return ["CB",
              [I(0),I(0),I(1),R2(2n),I(0),I(1),I(1),I(1),B1(k1+2n*n4),I(0)],
              [I(-1),I(d2+2n*n4),...Rtail]
            ];
          }
        }
      }
    }
    return tryRuleB(L,d2,Rtail);
  }

  function afterSweepCB(L,R) {
    if (R.length>=2 && R[0].t==="i" && R[0].v===-1n &&
        R[1].t==="i" && R[1].v>=0n)
      return tryRuleBC(L,R[1].v,R.slice(2));
    if (R.length && R[0].t==="i" && R[0].v>=12n)
      return tryRuleA(L,R[0].v,R.slice(1));
    return stepElemThenBB("CB",L,R);
  }

  function stepSym(state) {
    const [mode,L,R]=state;
    if (mode==="BB") return sweepBB(L,R);
    if (mode==="DL") return stepElemThenBB("DL",peelL(L),R);
    if (mode==="HALT") return state;
    const [L2,R2]=sweepCB(L,R);
    return afterSweepCB(L2,R2);
  }

  // Injected *inside* symrun_state_replay.cjs's run closure, after raw functions.
// Renamed original functions to *_raw by symrun_cost_replay.cjs generator.
let variant="F424",primitive=0n,primitiveBreakdown={},macroHits={};
const isF424=()=>variant==="F424";
function charge(kind,n){if(n<0n)throw Error("negative cost");primitive+=n;primitiveBreakdown[kind]=(primitiveBreakdown[kind]||0n)+n;}
function stepElemBB(L,R){
 const t=L[0];
 if(!t||(t.t==="i"&&t.v===-1n))charge("atomic",1n);
 else if(t.t==="i")charge("atomic",t.v===0n?(isF424()?8n:6n):t.v===1n?3n:t.v===2n?5n:9n);
 return stepElemBB_raw(L,R);
}
function stepElemDL(L,R){
 const t=L[0];
 if(t&&t.t==="i"){
   if(t.v===0n)charge("atomic",1n);
   else if(t.v===1n)charge("atomic",3n);
   else if(t.v===2n&&R.length&&R[0].t==="i"&&R[0].v>=0n)
     charge("atomic",3n*R[0].v+(isF424()?22n:20n));
 }
 return stepElemDL_raw(L,R);
}
function stepElemCB_run0(L,R1){
 const t=R1[0];
 if(!t)charge("atomic",3n);
 else if(t.t==="i"){
  if(t.v===-1n)charge("atomic",3n);
  else if(t.v===0n)charge("atomic",6n);
  else charge("atomic",3n*(t.v-1n)+(isF424()?21n:19n));
 }
 return stepElemCB_run0_raw(L,R1);
}
function stepElemCB(L,R){
 const t=R[0];
 if(!t)charge("atomic",2n);
 else if(t.t==="i"){
  if(t.v===-1n)charge("atomic",2n);
  else if(t.v===1n)charge("atomic",3n);
  else if(t.v>=2n)charge("atomic",5n);
 }
 return stepElemCB_raw(L,R);
}
function sweepBB(L,R){
 const t=L[0];
 if(t&&t.t==="i"){
  if(t.v===0n)charge("sweep",isF424()?8n:6n);
  else if(t.v===1n)charge("sweep",3n);
 }else if(t&&t.t==="b1")charge("sweep",(isF424()?11n:9n)*t.n);
 else if(t&&(t.t==="r2"||t.t==="r12")&&strip([I(0),I(1)],R)!==null)
  charge("sweep",(t.t==="r2"?(isF424()?14n:12n):(isF424()?25n:21n))*t.n);
 return sweepBB_raw(L,R);
}
function sweepCB(L,R){
 const t=R[0],r=R[1];
 if(t&&t.t==="i"){
  if(t.v===0n&&r&&r.t==="i"&&r.v===1n)charge("sweep",isF424()?21n:19n);
  else if(t.v===1n)charge("sweep",3n);
 }else if(t&&strip([I(0)],L)!==null)
  charge("sweep",(t.t==="b1"?(isF424()?21n:19n):
    t.t==="r2"?(isF424()?24n:22n):(isF424()?45n:41n))*t.n);
 return sweepCB_raw(L,R);
}
function tryRuleA(L,d,Rtail){
 const tail=strip(aPrefix,L);
 if(tail!==null){
  const k=matchEndB1(tail),n=d/6n;
  if(k!==null&&n>=2n&&n<=k){
   charge("A",n*((isF424()?32n:28n)*k+
     (isF424()?54n:48n)*n+(isF424()?228n:208n)));
   macroHits.A++;
  }
 }
 return tryRuleA_raw(L,d,Rtail);
}
function afterSplitB2(L,d2,Rtail,res){
 const [p,rest]=res,q=popSep3(rest);
 if(q!==null){
  const m=popRep12(q.rest);
  if(m!==null){
   const r=strip([I(1),I(0),I(1)],m.rest),q2=r===null?null:popSep3(r);
   if(q2!==null){
    const k=matchEndB1(q2.rest);
    if(k!==null&&p>=2n&&m.n>=2n&&k>=m.n){
     const n=m.n-1n;
     const id=(q.sep===sep3A?"A":"B")+(q2.sep===sep3A?"A":"B");
     const constant=isF424()?{AA:506n,AB:436n,BA:354n,BB:284n}[id]:
       {AA:458n,AB:396n,BA:322n,BB:260n}[id];
     charge("B",n*((isF424()?206n:184n)*n+
       (isF424()?152n:136n)*p+(isF424()?32n:28n)*k+constant));
     macroHits.B++;
    }
   }
  }
 }
 return afterSplitB2_raw(L,d2,Rtail,res);
}
function tryRuleBC(L,d2,Rtail){
 const r=strip([I(0),I(0),I(1)],L);
 if(r!==null){
  const p=popRep2(r);
  if(p!==null){
   const r2=strip([I(0),I(1),I(1),I(1)],p.rest);
   if(r2!==null){
    const k=matchEndB1(r2);
    if(k!==null&&p.n>=3n&&k>=1n){
     const n=p.n-2n;
     charge("C",n*((isF424()?102n:90n)*n+
       (isF424()?64n:56n)*k+(isF424()?320n:288n)));
     macroHits.C++;
    }
   }
  }
 }
 return tryRuleBC_raw(L,d2,Rtail);
}

function parseTokens(s) {
    const compact=s.replace(/\s+/g,"");
    const re=/\.item\.zero|\.item\(\.run(\d+)\)|\.repB1(\d+)|\.rep2(\d+)|\.rep12(\d+)/g;
    const out=[]; let m;
    while ((m=re.exec(compact))!==null) {
      if (m[0]===".item.zero") out.push(I(-1));
      else if (m[1]!==undefined) out.push(I(BigInt(m[1])));
      else if (m[2]!==undefined) out.push(B1(BigInt(m[2])));
      else if (m[3]!==undefined) out.push(R2(BigInt(m[3])));
      else out.push(R12(BigInt(m[4])));
    }
    return out;
  }

  function takeBracket(s,start) {
    let depth=0;
    for (let i=start;i<s.length;i++) {
      if (s[i]==="[") depth++;
      else if (s[i]==="]" && --depth===0)
        return {body:s.slice(start+1,i),end:i+1};
    }
    throw new Error("unclosed state list");
  }

  function parseState(lines,name) {
    const i=lines.findIndex(x=>x.startsWith("def "+name+" "));
    if (i<0) throw new Error("missing state definition "+name);
    let j=i+1;
    while (j<lines.length && !(lines[j].startsWith("def ") ||
      lines[j].startsWith("theorem ") || lines[j].startsWith("instance "))) j++;
    const block=lines.slice(i,j).join("\n");
    const modeMatch=block.match(/\(\.(BB|DL|CB|HALT),/);
    if (!modeMatch) throw new Error("missing mode in "+name);
    const p=modeMatch.index+modeMatch[0].length;
    const left=takeBracket(block,block.indexOf("[",p));
    const right=takeBracket(block,block.indexOf("[",left.end));
    return [modeMatch[1],parseTokens(left.body),parseTokens(right.body)];
  }

  function sameState(a,b) {
    return a[0]===b[0] && a[1].length===b[1].length && a[2].length===b[2].length &&
      a[1].every((x,i)=>eqTok(x,b[1][i])) && a[2].every((x,i)=>eqTok(x,b[2][i]));
  }

  function measure(state) {
    let maxField=0n,repeatSum=0n,expandedTapeLength=0n;
    for (const xs of [state[1],state[2]]) for (const t of xs) {
      if (t.t==="i") {
        if (t.v>maxField) maxField=t.v;
        expandedTapeLength++;
      } else {
        if (t.n>maxField) maxField=t.n;
        repeatSum+=t.n;
        expandedTapeLength+=(t.t==="b1"?2n:t.t==="r2"?3n:5n)*t.n;
      }
    }
    return {
      maxField,
      repeatSum,
      expandedTapeLength,
      symTokenCount:BigInt(state[1].length+state[2].length)
    };
  }

  async function replayOne(path,label) {
    maxZeroExpansion=0n;variant=label;primitive=0n;primitiveBreakdown={atomic:0n,sweep:0n,A:0n,B:0n,C:0n};macroHits={A:0,B:0,C:0};
    const source=await fetchText(base+path);
    const lines=source.split("\n");
    const names=lines.map(x=>x.match(/^def (symChk\d+) /)?.[1]).filter(Boolean);
    const checkpoints=names.map(name=>({
      step:Number(name.slice(6)),
      state:parseState(lines,name)
    })).sort((a,b)=>a.step-b.step);
    let state=parseState(lines,"initSymCyc3"),step=0,haltAt=null;
    const maxima={maxField:0n,repeatSum:0n,expandedTapeLength:0n,symTokenCount:0n};
    let maxFieldStep=0;
    const checkpointResults=[];
    for (const cp of checkpoints) {
      let chunkMaxField=measure(state).maxField;
      while (step<cp.step) {
        state=stepSym(state);
        step++;
        if (state[0]==="HALT" && haltAt===null) haltAt=step;
        const q=measure(state);
        if (q.maxField>chunkMaxField) chunkMaxField=q.maxField;
        for (const k of Object.keys(maxima)) if (q[k]>maxima[k]) { maxima[k]=q[k]; if (k==="maxField") maxFieldStep=step; }
      }
      const matches=sameState(state,cp.state);
      checkpointResults.push({
        step:cp.step,
        matches,
        mode:state[0],
        leftSymTokens:state[1].length,
        rightSymTokens:state[2].length,
        maxFieldInChunk:chunkMaxField.toString(),
        maxFieldAtCheckpoint:measure(cp.state).maxField.toString()
      });
      if (!matches) throw new Error(label+" mismatch at symChk"+cp.step);
    }
    return {
      machine:label,
      stepSymIterations:step,
      firstHaltAtStepSym:haltAt,
      checkpointResults,
      maxima:Object.fromEntries(Object.entries(maxima).map(([k,v])=>[k,v.toString()])),
      maxZeroExpansion:maxZeroExpansion.toString(),
      maxFieldStep,
      primitiveStepSymCost:primitive.toString(),primitiveBreakdown:Object.fromEntries(Object.entries(primitiveBreakdown).map(([k,v])=>[k,v.toString()])),macroHits:{...macroHits},finalMode:state[0]
    };
  }

  const f424=await replayOne(
    "M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.lean","F424");
  const f412=await replayOne(
    "M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.lean","F412");
  return {F424:f424,F412:f412};
};

if (typeof module !== "undefined" && module.exports) module.exports=run;
run;
