#!/usr/bin/env node
// Exact BigInt replay of the DRegular table in DRegularFirstExit.lean.
// This is an arithmetic/model diagnostic, not a raw-tape simulator.

const C = 1975700577069254261393123959451562008800234946348086n;

function step(s) {
  const {a,q,b} = s;
  if (a % 3n === 2n) {
    const k = (a - 2n) / 3n;
    if (q === 0) return {a:8n*k+9n,q:0,b:0};
    if (q === 1) return {a:8n*k+10n+BigInt(b),q:0,b:0};
    return {a:8n*k+10n,q:q-1,b};
  }
  if (a % 3n === 0n) {
    const k = (a - 3n) / 3n;
    if (q === 0) return {a:8n*k+11n,q:0,b:0};
    const r = Math.floor((b+1)/3);
    const d = q - 1 + 4*r;
    if ((b+1)%3 === 0) return {a:8n*k+11n+2n*BigInt(d),q:0,b:0};
    if ((b+1)%3 === 1) return {a:8n*k+13n+2n*BigInt(d),q:0,b:0};
    return {a:8n*k+7n+2n*BigInt(d),q:1,b:5};
  }
  const k = (a - 4n) / 3n;
  if (q === 0) return {a:8n*k+5n,q:1,b:5};
  if (b === 0) return {a:8n*k+5n,q:1,b:2*q+5};
  if (b === 2) return {a:8n*k+9n,q:q+1,b:0};
  if (b >= 3) return {a:8n*k+9n,q:q+2,b:b-3};
  return null;
}

function valuation(n,p) {
  if (n === 0n) return null;
  let x = n < 0n ? -n : n;
  let v = 0;
  while (x % p === 0n) { x /= p; v++; }
  return v;
}
function branch(a) {
  const r = a % 3n;
  return r === 1n ? "E" : r === 2n ? "B" : "A";
}
function insist(condition,message) {
  if (!condition) throw new Error(message);
}

const checkpoints = [];
let external = {a:C,q:0,b:0};
for (let j=0;j<=10;j++) {
  checkpoints.push({
    j, a:external.a, q:external.q, b:external.b,
    modulus:3n**BigInt(108-j)*8n**BigInt(j)
  });
  if (j<10) external = step(external);
}

const stats = checkpoints.map(t => ({
  j:t.j,q:t.q,b:t.b,count:0,maxV3:-1,maxV2:-1,
  v2AtMaxV3:null,bestIndex:null,hit:false
}));
let root = {a:9n,q:0,b:0};
let root2640 = null;
for (let i=0;i<=8394;i++) {
  if (i===2640) root2640 = root;
  for (let z=0;z<checkpoints.length;z++) {
    const t=checkpoints[z], st=stats[z];
    if (root.q===t.q && root.b===t.b) {
      st.count++;
      const d=root.a-t.a;
      const v3=valuation(d,3n), v2=valuation(d,2n);
      if (v3!==null && v3>st.maxV3) {
        st.maxV3=v3; st.v2AtMaxV3=v2; st.bestIndex=i;
      }
      if (v2!==null && v2>st.maxV2) st.maxV2=v2;
      if (d>=0n && d%t.modulus===0n) st.hit=true;
    }
  }
  if (i<8394) {
    root=step(root);
    insist(root!==null,"DRegular model exited before index 8394");
  }
}
insist(root2640!==null,"missing root index 2640");
insist(root.q===6 && root.b===1 && root.a%243n===157n,
  "final seed9 signature disagrees with seed9_exception");
insist(step(root)===null,"seed9 should exit after 8394 transitions");

const p=(root2640.a-C)/(3n**7n);
insist(root2640.a-C===3n**7n*p,"root index 2640 is not an exact 3^7 lift");
insist(p%3n===1n && p%2n===1n,"unexpected lift parameter residue");

const shadow=[];
let r=root2640, e={a:C,q:0,b:0};
for (let j=0;j<=7;j++) {
  const d=r.a-e.a;
  const expected=3n**BigInt(7-j)*8n**BigInt(j)*p;
  insist(r.q===e.q && r.b===e.b,"suffix mismatch in seven-step shadow");
  insist(d===expected,"affine 3-adic shadow identity failed");
  shadow.push({
    j, suffix:[r.q,r.b], externalSuffix:[e.q,e.b],
    rootBranch:branch(r.a), externalBranch:branch(e.a),
    v3Difference:valuation(d,3n), v2Difference:valuation(d,2n)
  });
  if (j<7) { r=step(r); e=step(e); }
}
const rootEighth=step(r), externalEighth=step(e);
insist(rootEighth && rootEighth.q===1 && rootEighth.b===5,
  "root eighth successor should have suffix (1,5)");
insist(externalEighth && externalEighth.q===3 && externalEighth.b===4,
  "external eighth successor should have suffix (3,4)");
insist(r.a%3n===0n && e.a%3n===1n,
  "eighth branch residues do not diverge as expected");

console.log(JSON.stringify({
  machine:"D start / regular-section model",
  target:"A(3^108*k + C, [])",
  C:C.toString(),
  rootStart:"L(9,0,0)",
  rootTransitionsChecked:8394,
  root2640:{
    suffix:[root2640.q,root2640.b],
    aBits:root2640.a.toString(2).length,
    pBits:p.toString(2).length,
    pMod3:(p%3n).toString(),
    pMod2:(p%2n).toString(),
    exactRelation:"a_2640 = C + 3^7*p"
  },
  sevenStepShadow:shadow,
  eighthDivergence:{
    rootBranch:branch(r.a),
    externalBranch:branch(e.a),
    rootSuffix:[rootEighth.q,rootEighth.b],
    externalSuffix:[externalEighth.q,externalEighth.b],
    rootResidue:(r.a%3n).toString(),
    externalResidue:(e.a%3n).toString()
  },
  checkpointEndpointSieve:stats.map(s=>({
    j:s.j,suffix:[s.q,s.b],sampledStates:s.count,
    requiredV3:108-s.j,maxObservedV3:s.maxV3,
    maxObservedV2:s.maxV2,bestIndex:s.bestIndex,
    exactCylinderHit:s.hit
  })),
  rootFirstExit:{
    transitions:8394,q:root.q,b:root.b,
    aMod243:(root.a%243n).toString(),
    nextDefined:step(root)!==null
  },
  caveat:"The sieve checks DRegular section endpoints only; it does not exclude intermediate raw configurations."
},null,2));
