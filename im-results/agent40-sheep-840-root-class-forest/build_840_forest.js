#!/usr/bin/env node
"use strict";

// Rebuild the 633 new finite inverse trees in the seventh Sheep 3-adic stratum.
// Exact arithmetic only: BigInt modular powers, integer inequalities, no floating point.
// Run: node build_840_forest.js > forest.json

const J = 1458n;
const M = 1n << 182n; // every row modulus is strictly below this bound
const PRIOR = [[138,4860],[402,4860],[1218,4860],[1738,4860],[118,14580],[246,24300],[558,8100],[846,8100],[702,11340],[194,24300],[5054,24300],[366,8100],[1986,8100],[374,8100],[1994,8100],[482,43740],[9230,43740],[495,43740],[9243,43740],[819,14580],[3735,14580],[188,55080],[190,306180],[220,55080],[262,53460],[442,1837080],[624,29160],[648,122472]];
const KNOWN = [1,50,58,170,178,230,238,350,430,490,598,610,710,770,778,790,850,890,898,958,1030,1070,1078,1130,1138,1210,1250,40,124,152,236,292,320,376,404,544,572,628,656,740,796,824,880,992,1048,1076,1132,1160,1244,28,64,136,244,280,352,388,568,604,676,784,892,928,1000,1036,1108,1252,8,188,368,428,548,608,968,1088,1148];
const KNOWN_SET = new Set(KNOWN);

function modPow(a,e,m) {
  let r=1n; a%=m;
  while(e>0n) { if(e&1n) r=r*a%m; a=a*a%m; e>>=1n; }
  return r;
}
function pow2(n) { return 2n ** BigInt(n); }
function v3(n) {
  if(n<0n) n=-n;
  let e=0;
  while(n%3n===0n) { n/=3n; e++; }
  return e;
}
function bitLength(n) {
  if(n<0n) n=-n;
  return n===0n ? 0 : n.toString(2).length;
}
function genericCutoff(C,B,h) {
  const D=C*3n**BigInt(h);
  const K=a=>2n**BigInt(h+1)*(C-B)+D*(2n*BigInt(a)-3n);
  let A=1;
  while(!(K(A)>1n && K(A)<pow2(A) && 2n*D<=pow2(A))) A++;
  return {A,D};
}
function specialCutoff(C,B,h) {
  const D=C*3n**BigInt(h);
  const L=a=>D*BigInt(a+2)+2n**BigInt(h)*(C-B);
  let S=1;
  while(!(L(S)>1n && L(S)<pow2(S) && D<=pow2(S))) S++;
  return {S,D};
}
function buildTree(t0) {
  const jt=J*BigInt(t0);
  const nodes=[{id:0,s:0n,B:0n,C:1n,depth:0}];
  const seen=new Map([["0|0|1",0]]);
  const queue=[0], edges=[];
  let rows=0, maxN=0n, maxVal=0n, maxBbits=0, maxCbits=0, maxA=0, maxr=0;
  let lowSpecialFailures=0, integralityFailures=0, cofactorFailures=0;
  while(queue.length) {
    const id=queue.shift(), n=nodes[id];
    if((modPow(2n,jt+n.s,n.C)+n.B)%n.C!==0n) { integralityFailures++; break; }
    const c3=v3(n.C);
    let r=null;
    for(let rr=0;rr<24;rr++) {
      const m=3n**BigInt(c3+rr+1);
      if((modPow(2n,jt+n.s,m)+n.B-n.C)%m!==0n) { r=rr; break; }
    }
    if(r===null) { integralityFailures++; break; }
    n.r=r; maxr=Math.max(maxr,r);
    const valMod=3n**BigInt(c3+r+1);
    if(valMod>maxVal) maxVal=valMod;
    maxBbits=Math.max(maxBbits,bitLength(n.B));
    maxCbits=Math.max(maxCbits,bitLength(n.C));
    if(n.B%2n!==0n || n.C%2n!==1n || n.C<=0n) throw new Error("node parity/positivity failure");
    n.out=[];
    for(let h=0;h<=r;h++) {
      const gc=genericCutoff(n.C,n.B,h), sc=specialCutoff(n.C,n.B,h), D=gc.D;
      maxA=Math.max(maxA,gc.A,sc.S);
      const exponent=jt+n.s+BigInt(h);
      // All low-a special-source equations are strictly below the left side.
      for(let a=1;a<sc.S;a++) {
        const L=D*BigInt(a+2)+2n**BigInt(h)*(n.C-n.B);
        const rhs=3n*D*pow2(a)+L;
        if(rhs>=0n && BigInt(bitLength(rhs))>exponent) lowSpecialFailures++;
      }
      // Exact low-a generic congruence enumeration.
      for(let a=1;a<gc.A;a++) {
        rows++;
        const N=D*(pow2(a+1)+1n);
        if(N>maxN) maxN=N;
        const K=2n**BigInt(h+1)*(n.C-n.B)+D*(2n*BigInt(a)-3n);
        if(modPow(2n,jt+n.s+BigInt(h+1),N)===((K%N)+N)%N) {
          // 2^E > 5N+K proves the source cofactor is >=5; it is odd since N,K are odd.
          if(5n*N+K>=0n && BigInt(bitLength(5n*N+K))>jt+n.s+BigInt(h+1)) cofactorFailures++;
          const s2=n.s+BigInt(a+h+1);
          const B2=pow2(a)*(2n**BigInt(h+1)*(n.B-n.C)+n.C*3n**BigInt(h)*(3n-2n*BigInt(a)));
          const C2=N, key=`${s2}|${B2}|${C2}`;
          let child=seen.get(key);
          if(child===undefined) {
            child=nodes.length; seen.set(key,child);
            nodes.push({id:child,s:s2,B:B2,C:C2,depth:n.depth+1});
            queue.push(child);
          }
          n.out.push([h,a,child]);
          edges.push([id,child,h,a]);
        }
      }
    }
  }
  const indegree=nodes.map(n=>0);
  for(const e of edges) indegree[e[1]]++;
  const tree=edges.length===nodes.length-1 && indegree[0]===0 && indegree.slice(1).every(x=>x===1);
  const summary={
    t:t0,nodes:nodes.length,edges:edges.length,
    leaves:nodes.filter(n=>!edges.some(e=>e[0]===n.id)).length,
    rows,maxDepth:Math.max(...nodes.map(n=>n.depth)),tree,
    lowSpecialFailures,integralityFailures,cofactorFailures
  };
  return {
    summary,
    nodes:nodes.map(n=>({id:n.id,s:n.s.toString(),B:n.B.toString(),C:n.C.toString(),r:n.r,depth:n.depth})),
    edges,maxN,maxVal,maxBbits,maxCbits,maxA,maxr,
    unfinished:queue.length!==0
  };
}

const R_FREE=[], R_HIT=[], NEW_TREES=[];
let sumNodes=0,sumEdges=0,sumRows=0,maxNodes=0,maxRows=0;
let maxN=0n,maxVal=0n,maxBbits=0,maxCbits=0,maxA=0,maxr=0;
for(let t=1;t<1260;t++) {
  if(t%3===0) continue;
  const tree=buildTree(t);
  const s=tree.summary;
  if(tree.unfinished || !s.tree || s.lowSpecialFailures || s.integralityFailures || s.cofactorFailures)
    throw new Error("tree verification failed at t="+t);
  if(s.edges===0) { R_FREE.push(t); continue; }
  R_HIT.push(t);
  sumNodes+=s.nodes; sumEdges+=s.edges; sumRows+=s.rows;
  maxNodes=Math.max(maxNodes,s.nodes); maxRows=Math.max(maxRows,s.rows);
  if(tree.maxN>maxN) maxN=tree.maxN;
  if(tree.maxVal>maxVal) maxVal=tree.maxVal;
  maxBbits=Math.max(maxBbits,tree.maxBbits); maxCbits=Math.max(maxCbits,tree.maxCbits);
  maxA=Math.max(maxA,tree.maxA); maxr=Math.max(maxr,tree.maxr);
  if(!KNOWN_SET.has(t)) {
    const overlapsPrior=PRIOR.some(([b,p])=>(J*BigInt(t)-BigInt(b))%BigInt(p)===0n);
    if(!overlapsPrior) NEW_TREES.push({t,summary:s,nodes:tree.nodes,edges:tree.edges});
  }
}
const R_FREE_EXPECTED=[];
for(let t=1;t<1260;t++) if(t%3!==0 && t%4===0 && t%7!==5 && t%9!==1 && t%15!==8) R_FREE_EXPECTED.push(t);
if(JSON.stringify(R_FREE)!==JSON.stringify(R_FREE_EXPECTED)) throw new Error("132 direct-root-free set mismatch");
if(R_FREE.length!==132 || R_HIT.length!==708 || KNOWN.length!==75 || NEW_TREES.length!==633)
  throw new Error("unexpected partition counts");
if(maxN>=M || maxVal>=M || maxBbits>88 || maxCbits>87 || maxA>95 || maxr>7)
  throw new Error("universal factorial bound is insufficient");
if(!PRIOR.every(([b,p])=>BigInt(p)<M)) throw new Error("prior cone period exceeds M");
if(!KNOWN.every(t=>R_HIT.includes(t))) throw new Error("known tree base lacks a root parent");

const forest={
  schema:"agent40-sheep-840-root-class-forest-v1",
  J:"1458", M:"2^182", common_period:"(2^182)!",
  R_free:R_FREE, R_known:KNOWN, R_new:NEW_TREES.map(x=>x.t),
  stats:{
    nonzero_mod3_residues:840,root_free:132,root_hit_trees:708,
    known_tree_bases:75,new_trees:633,
    sum_nodes_all_708:sumNodes,sum_edges_all_708:sumEdges,sum_low_generic_rows_all_708:sumRows,
    max_nodes_per_tree:maxNodes,max_rows_per_tree:maxRows,
    max_row_modulus:maxN.toString(),max_row_modulus_bits:bitLength(maxN),
    max_valuation_modulus:maxVal.toString(),max_valuation_modulus_bits:bitLength(maxVal),
    max_abs_B_bits:maxBbits,max_C_bits:maxCbits,max_generic_or_special_cutoff:maxA,
    max_hidden_3adic_length:maxr,prior_overlaps_among_new:0
  },
  trees:NEW_TREES
};
console.log(JSON.stringify(forest,null,2));
