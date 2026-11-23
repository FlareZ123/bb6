/*
 * Cost-instrumented primitive steps for the pinned Cryptids SymRun stepPure
 * (google-deepmind/cryptids @ 3647718b5df22e1a61462dec0376bd204526285a).
 * F424 and F412 have distinct atomic and repeated-block primitive costs.
 *
 * These are candidate exact counts along the particular source-verified
 * stepPure witnesses. They are computed, not formal Lean theorems.
 */
function createCostModel(api) {
  const {I,B1,R2,R12,strip,bumpSymL,bumpSymR,stepElemBB,stepElemDL,stepElemCB}=api;
  const sep3A=[I(0),I(1),I(2)],sep3B=[I(0),I(-1),I(1)];
  const purePeel=(t,xs)=> t.t==="i" ? [t,...xs] : t.n===0n ? [t,...xs] :
    t.t==="b1" ? [I(0),I(1),B1(t.n-1n),...xs] :
    t.t==="r2" ? [I(1),I(0),I(1),R2(t.n-1n),...xs] :
      [I(1),I(0),I(1),I(0),I(1),R12(t.n-1n),...xs];

  function stepPureCosted(mode,L,R,variant) {
    const F=variant==="F424", BB0=F?8n:6n, PB1=F?11n:9n, PC2=F?14n:12n, PC12=F?25n:21n;
    const QB1=F?21n:19n, QB2=F?24n:22n, QB12=F?45n:41n;
    const elemBB=(A,B)=>{
      const t=A[0]; let c=0n;
      if(!t || (t.t==="i" && t.v===-1n)) c=1n;
      else if(t.t==="i") c=t.v===0n?BB0:t.v===1n?3n:t.v===2n?5n:9n;
      return [stepElemBB(A,B),c];
    };
    const elemDL=(A,B)=>{
      const t=A[0]; let c=0n;
      if(t&&t.t==="i") {
        if(t.v===0n) c=1n;
        else if(t.v===1n) c=3n;
        else if(t.v===2n&&B.length&&B[0].t==="i"&&B[0].v>=0n)
          c=3n*B[0].v+(F?22n:20n);
      }
      return [stepElemDL(A,B),c];
    };
    const elemCB=(A,B)=>{
      let c=0n;
      if(!B.length) c=2n;
      else {const t=B[0];
        if(t.t==="i") {
          if(t.v===-1n)c=2n;
          else if(t.v===0n){
            const r=B[1];
            c=!r?3n:r.t!=="i"?0n:r.v===-1n?3n:r.v===0n?6n:
              3n*(r.v-1n)+(F?21n:19n);
          }
          else if(t.v===1n)c=3n;
          else c=5n;
        }
      }
      return [stepElemCB(A,B),c];
    };
    if(mode==="HALT") return [["HALT",L,R],0n];
    if(mode==="BB") {
      if(!L.length||L[0].t==="i")return elemBB(L,R);
      const [t,...xs]=L;
      if(t.t==="b1")return [["BB",xs,[B1(t.n),...R]],PB1*t.n];
      const rs=strip([I(0),I(1)],R);
      if(rs!==null) return [["BB",xs,[I(0),I(1),t,...rs]],(t.t==="r2"?PC2:PC12)*t.n];
      return elemBB(purePeel(t,xs),R);
    }
    if(mode==="DL") return !L.length ? [["DL",L,R],0n] :
      elemDL(purePeel(L[0],L.slice(1)),R);
    if(!R.length || (R[0].t==="i" && R[0].v<=2n)) return elemCB(L,R);
    const [t,...xs]=R;
    if(t.t==="i") return [["BB",bumpSymL(L),[I(0),I(t.v-3n),...xs]],5n];
    if(t.t==="b1"){
      const r3=strip([I(0),I(0),I(1)],L);
      if(r3!==null) return [["CB",[I(0),B1(t.n+1n),...r3],xs],QB1*t.n];
      const r=strip([I(0)],L);
      return r===null ? [["CB",L,R],0n]:[["CB",[I(0),B1(t.n),...r],xs],QB1*t.n];
    }
    if(t.t==="r2"){
      const r4=strip([I(0),I(1),I(0),I(1)],L);
      if(r4!==null) return [["CB",[I(0),R2(t.n+1n),...r4],xs],QB2*t.n];
      const r=strip([I(0)],L);
      return r===null?[["CB",L,R],0n]:[["CB",[I(0),R2(t.n),...r],xs],QB2*t.n];
    }
    const r=strip([I(0)],L);
    return r===null?[["CB",L,R],0n]:[["CB",[I(0),R12(t.n),...r],xs],QB12*t.n];
  }

  const stateA0=(k,d,r=[])=>["CB",[I(0),I(0),I(1),I(1),I(0),I(1),I(1),I(1),I(0),I(-1),I(1),B1(k),I(0)],[I(d),...r]];
  const stateA=(m,k,d,r=[])=>["CB",[I(0),I(0),I(1),I(1),I(0),I(1),I(1),I(1),I(0),I(1),R12(m),I(1),I(0),I(1),I(0),I(-1),I(1),B1(k),I(0)],[I(d),...r]];
  const stateC=(p,k,d,r=[])=>["CB",[I(0),I(0),I(1),R2(p),I(0),I(1),I(1),I(1),B1(k),I(0)],[I(-1),I(d),...r]];
  const stateB=(s,m,p,n,k,d,r=[])=>["CB",[I(0),I(0),I(1),R2(p),I(1),...s,R12(n),I(1),I(0),I(1),...m,B1(k),I(0)],[I(-1),I(d),...r]];

  function runPure(state,iterations,variant){
    let cost=0n;
    for(let i=0;i<iterations;i++){
      const [after,c]=stepPureCosted(...state,variant);
      state=after;cost+=c;
    }
    return {state,cost};
  }
  return {stepPureCosted,runPure,stateA0,stateA,stateB,stateC,sep3A,sep3B};
}
if(typeof module!=="undefined" && module.exports) module.exports=createCostModel;
createCostModel;
