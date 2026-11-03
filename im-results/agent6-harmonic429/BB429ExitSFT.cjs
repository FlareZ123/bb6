'use strict';

const assert = require('node:assert/strict');

/** @typedef {[bigint,bigint]} State */
/** Exact 12-branch highLevelNext J-state transcription. @param {State} s @returns {State|null} */
function next([u,w]) {
  if (w >= 2n*u+3n) return [2n*u+3n,w-2n*u-3n];
  if (w === 2n*u+2n) return [0n,4n*u+18n];
  if (w === 2n*u+1n) return [11n,4n*u+2n];
  if (w === 2n*u) return [0n,4n*u+12n];
  const d=u-w/2n;
  if (w%2n===0n) {
    if (d===1n) return [0n,2n*w+12n];
    if (d%2n===0n) return [11n,2n*u+w-2n];
    return [0n,2n*u+w+10n];
  }
  if (d===1n) return null;
  if (d===2n) return [0n,2n*w+8n];
  if (d%2n===0n) return w===1n ? [11n,2n*u+10n] : [d+7n,2n*w-4n];
  return [d+3n,2n*w];
}

/** @param {State} s @param {number} n @returns {State|null} */
function run(s,n) {
  for (let i=0;i<n && s!==null;i++) s=next(s);
  return s;
}

/** @param {number} k @returns {bigint} */
function U(k) { return 3n*((1n<<BigInt(k))-1n); }
/** @param {number} j @returns {bigint} */
function V(j) { return 14n*(1n<<BigInt(j))-3n; }
/** @param {number} j @returns {bigint} */
function demandV(j) { return 2n*V(j)-BigInt(3*j+22); }

/** @returns {void} */
function checkAllExits() {
  let trials=0;
  const classes={regular:0,exceptionHigh:0,exceptionLow:0};
  for (let k=6;k<=94;k+=4) {
    const u=U(k),v=V(k-2);
    for (let r=2;r<3*k+10;r+=4) {
      const w=2n*u-4n-BigInt(r);
      const branch=r===3*k+4 ? 'exceptionHigh' : r===3*k+8 ? 'exceptionLow' : 'regular';
      const n=branch==='regular' ? 2*k+2 : branch==='exceptionHigh' ? 4*k+6 : 3*k+3;
      const z=BigInt(branch==='regular' ? 3*k+3-r : branch==='exceptionHigh' ? 6*k+35 : 3*k+5);
      const y=2n*U(k+1)+z+9n-demandV(k-2);
      const actual=run([u,w],n);
      assert.deepStrictEqual(actual,[v,y],'k='+k+' r='+r+' '+branch);
      assert.equal(y%4n,2n);
      assert(y+4n<=2n*v);
      classes[branch]++;
      trials++;
    }
  }
  console.log('PASS 920 all-residue U-even exits:',trials,classes);
}

/** @returns {void} */
function checkSyntheticEscapes() {
  let rays=0;
  for (let u=17n;u<1000n;u+=4n) {
    assert.deepStrictEqual(run([u,u+8n],4),[u+8n,u+16n]);
    assert(run([u,u+8n],256)!==null);
    rays++;
  }
  for (let k=3;k<=22;k++) {
    const root=9n*(1n<<BigInt(k))-BigInt(3*k+1);
    assert.deepStrictEqual(run([0n,root],k),[U(k),U(k)+8n]);
    assert(run([0n,root],256)!==null);
  }
  for (let k=1;k<=20;k++) {
    const root=42n*(1n<<BigInt(k))-BigInt(3*k+23);
    assert.deepStrictEqual(run([11n,root],k),[V(k),V(k)+8n]);
    assert(run([11n,root],256)!==null);
  }
  console.log('PASS synthetic ray finite regressions:',rays,'direct and 40 root inputs');
}

/** @returns {void} */
function checkRootPrefix() {
  assert.deepStrictEqual(run([0n,0n],79),[U(6),48n]);
  assert.deepStrictEqual(run([0n,0n],156),[U(6),356n]);
  assert.deepStrictEqual(run([0n,0n],170),[V(4),366n]);
  console.log('PASS actual blank-entry accelerated checkpoints 79, 156, 170');
}

checkAllExits();
checkSyntheticEscapes();
checkRootPrefix();
