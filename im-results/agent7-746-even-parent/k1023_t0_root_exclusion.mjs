#!/usr/bin/env node
// Exact ResetParent-chain exclusion for the K=1023 t=0 candidate.
// Parent grammar is the two exhaustive cases of CascadeResetInverse.ResetParent.

function pow2(n) { return 1n << BigInt(n); }
function v3(n) { let v=0; while(n%3n===0n){n/=3n;v++;} return v; }
function bits(n) { return n.toString(2).length; }

function directParents(u) {
  const out = [];
  const ke = bits(u)-3;
  if (ke>=0) {
    const p=pow2(ke);
    if (6n*p-1n<=u && u<=8n*p-3n) {
      const h=2n*u-8n*p-BigInt(ke);
      if (h>=u) throw Error("even parent violates strict ranking");
      out.push({type:"even",t:null,k:ke,h});
    }
  }
  const X=2n*u+5n, vmax=v3(X);
  for (let t=0;t<vmax;t++) {
    const d=X/(3n**BigInt(t+1)), P=pow2(t)*d, k=bits(P)-3;
    if (k<0) continue;
    const p=pow2(k);
    if (d%2n===1n && 6n*p+1n<=P && P<=8n*p-1n) {
      const h=2n*P-8n*p-BigInt(k)-5n;
      if (h>=u) throw Error("odd parent violates strict ranking");
      out.push({type:"odd",t,k,h});
    }
  }
  return out;
}

function edgeCheck(u,e) {
  const p=pow2(e.k);
  if (e.type==="even") {
    if (!(6n*p-1n<=u && u<=8n*p-3n) ||
        2n*u!==8n*p+e.h+BigInt(e.k)) throw Error("even edge failed");
  } else {
    const X=2n*u+5n, d=X/(3n**BigInt(e.t+1)), P=pow2(e.t)*d;
    if (d%2n!==1n || !(6n*p+1n<=P && P<=8n*p-1n) ||
        X!==3n**BigInt(e.t+1)*d ||
        2n*P!==8n*p+e.h+BigInt(e.k)+5n) throw Error("odd edge failed");
  }
}

const K=1023n, c=2n*K+7n, a=11n, r=K+1n-a, p=pow2(K);
if (r%2n!==1n || 4n*c>7n*pow2(a)) throw Error("source criterion");
const B0=c*pow2(r+3n), D0=(B0-16n*p+2n*K+1n)/3n;
if (D0%3n!==2n) throw Error("D0 phase");
const local=[];
for (let q=0n;q<=a-3n;q+=2n) {
  const E=8n*p+K-pow2(q)*D0;
  if (4n*p>E+K+4n || E+K+5n>=8n*p) continue;
  const X=2n*E+5n;
  if (X%3n!==0n) continue;
  const v=v3(X), t=v-1, d=X/(3n**BigInt(v)), P=pow2(t)*d;
  const L=bits(P)-3;
  if (L<0) continue;
  const pL=pow2(L);
  if (6n*pL+1n<=P && P<=8n*pL-1n) {
    const h=2n*P-8n*pL-BigInt(L)-5n;
    local.push({q,E,t,d,P,L,h});
  }
}
if (local.length!==1 || local[0].q!==8n) throw Error("expected unique q=8 odd parent");
const {q,E,L,h:h0}=local[0];
const ke=bits(E)-3, pe=pow2(ke);
if (6n*pe-1n<=E && E<=8n*pe-3n) throw Error("unexpected even parent of E");

const chain=[];
let u=h0;
while (true) {
  if (u===2n) throw Error("blank root reached");
  const ps=directParents(u);
  for (const e of ps) edgeCheck(u,e);
  chain.push({height:String(u),bits:bits(u),parentCount:ps.length,
    parents:ps.map(e=>({type:e.type,t:e.t,k:e.k,parent:String(e.h)}))});
  if (ps.length===0) break;
  if (ps.length!==1) throw Error("unexpected branching");
  u=ps[0].h;
  if (chain.length>100) throw Error("unexpectedly long chain");
}
if (chain.length!==8 || chain.slice(0,-1).some(x=>x.parentCount!==1) ||
    chain[7].parentCount!==0) throw Error("unexpected chain shape");
console.log(JSON.stringify({
  K:String(K),a:String(a),r:String(r),q:String(q),D0mod3:String(D0%3n),
  entry:String(E),incomingOddSource:String(h0),chain
},null,2));
