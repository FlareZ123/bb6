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
