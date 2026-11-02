"use strict";

/**
 * Exact affine inverse-cone certificate for the genuine P1 critical family
 * n = 65536*q+382, q >= 0. This is computer-checked symbolic evidence
 * pending a source-level Lean certificate for the entire infinite family.
 * Coefficient pair [A,C] represents A*s+C, where
 * s(q) = 7*2^(65536*q+366)-q-1.
 *
 * No floating point values, brute-force q samples, or arbitrary cutoffs.
 */
const assert = require("node:assert/strict");
const crypto = require("node:crypto");

/** @param {bigint} a @param {bigint} c */
const aff = (a, c) => [a, c];
/** @param {bigint[]} a @param {bigint[]} b */
const add = (a, b) => aff(a[0] + b[0], a[1] + b[1]);
/** @param {bigint[]} a @param {bigint} n */
const mul = (a, n) => aff(a[0] * n, a[1] * n);
/** @param {bigint[]} a @param {bigint} n */
const div = (a, n) => {
  assert.equal(a[0] % n, 0n, "non-integral parameter coefficient");
  assert.equal(a[1] % n, 0n, "non-integral constant coefficient");
  return aff(a[0] / n, a[1] / n);
};
/** @param {bigint[]} a @param {bigint} n */
const rem = (a, n) => {
  assert.equal(a[0] % n, 0n, "parameter-dependent residue");
  return ((a[1] % n) + n) % n;
};
/** @param {bigint[]} a @param {bigint} min */
const lower = (a, min) => {
  assert(a[0] >= 0n && a[1] >= min, "non-uniform lower bound");
};
const c = n => aff(0n, n);
const nodes = new Map();
const leaves = [];
const root = {b: aff(131072n,130292n), d: c(3n), path:"root"};

/** Prove the adjacent-power gap using W >= 64(q+1).
 * 14*2^(n-1) = 458752*W and 14*2^n = 917504*W.
 * The value is A*s+C = 7*A*W-A*(q+1)+C.
 * @param {bigint[]} x
 */
function checkGap(x) {
  const value = add(x, c(12n));
  const [A, C] = value;
  assert(A >= 66048n && A <= 130560n, "power coefficient outside gap band");
  assert(C >= 0n && C <= 129782n, "power constant outside gap band");
  assert(3584n*64n > 130560n, "lower gap arithmetic invalid");
  assert(3584n*64n > 129782n, "upper gap arithmetic invalid");
  return value;
}

/** @param {bigint[]} b @param {bigint[]} d @param {string} path */
function visit(b,d,path) {
  assert(!nodes.has(path), "repeated symbolic hub");
  lower(b,8n); lower(d,1n);
  assert.equal(rem(b,4n),0n,"non-positive G return");
  nodes.set(path, {b:b.map(String), d:d.map(String)});
  let k=add(div(b,4n),c(-1n));
  let z=add(d,div(b,2n));
  let t=0;
  for (;;) {
    lower(z,2n); // No exceptional G-ancestor input c=1 at any hub.
    const x=add(mul(k,2n),c(-4n));
    const y=add(z,c(4n));
    lower(x,8n); lower(y,1n);
    const branch=path+"."+t;
    if(rem(y,2n)===0n) {
      const val=checkGap(x);
      leaves.push({path:branch,kind:"power-gap",x:x.map(String),
        y:y.map(String),power:val.map(String)});
    } else if(rem(x,4n)===2n) {
      lower(x,3n);
      leaves.push({path:branch,kind:"forbidden-mod4",x:x.map(String),y:y.map(String)});
    } else if(rem(x,4n)===0n) {
      visit(x,y,branch);
    } else {
      throw Error("uncovered residue "+branch);
    }
    if(rem(z,2n)===0n)break;
    z=div(add(z,c(-3n)),2n);
    k=add(add(k,div(add(z,c(-rem(z,2n))),2n)),c(1n));
    t++;
    assert(t<=16,"unexpected inverse depth");
  }
}
visit(root.b,root.d,root.path);
assert.equal(nodes.size,31);
assert.equal(leaves.length,62);
assert.equal(leaves.filter(x=>x.kind==="power-gap").length,31);
assert.equal(leaves.filter(x=>x.kind==="forbidden-mod4").length,31);
const report={family:"n=65536*q+382 for all q>=0",status:"symbolic evidence only; all-parameter Lean proof pending",
    source:"Exact GAncestor inverse and Agent1 reachability obstruction shapes",
    hubCount:nodes.size, leafCount:leaves.length,
    nodes:Object.fromEntries([...nodes].sort(([x],[y])=>x.localeCompare(y))),
    leaves:leaves.sort((x,y)=>x.path.localeCompare(y.path))};
const out=JSON.stringify(report,null,2);
process.stdout.write(out+"\n");
process.stderr.write("SHA256 "+crypto.createHash("sha256").update(out).digest("hex")+"\n");
