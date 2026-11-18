#!/usr/bin/env node
// Experimental synchronization scan for the #623 canonical root orbit.
// The high-level recurrence is transcribed from
// im-results/agent8-623-inverse/root_mass_corridor_survey.js.
// This is a diagnostic replay, not a formal proof.
function evalA(a, k, m) {
  while (true) {
    if (k % 3n === 2n) return [a + 1n, k / 3n, m];
    if (a === 0n) return k % 3n === 0n ? null : [0n, k / 3n, m];
    if (k % 3n === 0n) return [a - 1n, k / 3n, m + 2n];
    k = k / 3n;
    m += 2n * k + 3n;
    a -= 1n;
  }
}
function drainB(a, b, d) {
  while (b !== 0n) {
    const next = evalA(a, b - 1n, d + 2n * b + 3n);
    if (next === null || next[1] >= b) return null;
    [a, b, d] = next;
  }
  return [a, d];
}
function highLevelNext(a, d) {
  if (a === 0n)
    return d % 2n === 1n ? drainB(d + 1n, 2n, 2n) : [d, 7n];
  if (d % 2n === 1n && a >= d + 5n)
    return drainB(a - d - 5n, d + 3n, 5n);
  if (d % 2n === 0n && a >= d + 3n)
    return drainB(a - d - 2n, d + 2n, 2n);
  if (a % 2n === 1n) return null;
  if (a === d + 2n) return drainB(0n, a, 2n);
  if (d % 2n === 1n) return drainB(d + 4n - a, a - 1n, 3n);
  const p = evalA(d + 1n - a, a, 2n * a + 5n);
  return p === null ? null : drainB(...p);
}
function stateData(a, d) {
  let q, p, s;
  if (a >= d) {
    q = d; p = a - d; s = d % 2n === 1n ? 'LO' : 'LE';
  } else {
    q = a; p = d - a; s = d % 2n === 1n ? 'RO' : 'RE';
  }
  const g = p - 3n*q;
  const gamma = {LO:18n, LE:10n, RO:2n, RE:4n}[s];
  return {q,g,z:2n*g-gamma,s};
}
function ellOf(q) {
  let ell = 0, p = 1n;
  while ((p - 1n)/2n < q + 3n) { ell++; p *= 3n; }
  return ell;
}
function digitsMod3(x, len) {
  const mod = 3n ** BigInt(len);
  let n = x % mod;
  if (n < 0n) n += mod;
  const ds = [];
  for (let i=0; i<len; i++) { ds.push(Number(n % 3n)); n /= 3n; }
  return ds;
}
function mod3(n) { const r = n % 3; return r < 0 ? r + 3 : r; }
function floor3(n) { let q = Math.trunc(n/3); if (n < 0 && n%3 !== 0) q--; return q; }

// Quantifies over every previous digit pair (9 possibilities) and every
// admissible initial carry pair for the selected branch.
function checkSync(word, branch) {
  const amin = branch === 'L' ? -2 : -4;
  const amax = branch === 'L' ? 2 : 1;
  let reference = null;
  for (let xp0=0; xp0<3; xp0++) for (let yp0=0; yp0<3; yp0++)
    for (let a0=amin; a0<=amax; a0++) for (let b0=-2; b0<=2; b0++) {
      let xp=xp0, yp=yp0, a=a0, b=b0, nz=false, not2=false;
      for (const [x,y] of word) {
        let tx,ty;
        if (branch === 'L') { tx=x-yp+a; ty=yp+b; }
        else { tx=-x-xp-yp+a; ty=xp+yp+b; }
        const ox=mod3(tx), oy=mod3(ty);
        a=floor3(tx); b=floor3(ty);
        if (ox !== 0) nz=true;
        if (ox !== 2) not2=true;
        xp=x; yp=y;
        if (a<amin || a>amax || b< -2 || b>2) return false;
      }
      if (!nz || !not2) return false;
      const end=[xp,yp,a,b];
      if (reference === null) reference=end;
      else if (end.some((v,i)=>v!==reference[i])) return false;
    }
  return true;
}
const maxStep = Number(process.argv[2] || 10000);
const emitBlocks = process.argv.includes('--emit-blocks');
let a=0n,d=7n;
let failL=0,failR=0,minLen=Infinity,maxLen=0,firstFailL=null,firstFailR=null;
let anchor16=null, states=0;
for (let n=0;n<=maxStep;n++) {
  if (n===16) anchor16=[a.toString(),d.toString()];
  if (n>=33) {
    const {q,z}=stateData(a,d), ell=ellOf(q);
    const B=Math.max(34*ell+140,36*ell+88);
    let k=0,pow=1; while(pow<=B){pow*=3;k++;}
    let j=0; pow=1n; const target=BigInt(B)**3n; while(pow<=target){pow*=3n;j++;}
    const xd=digitsMod3(z,j), yd=digitsMod3(6n*q,j);
    // The lower endpoint is k+1, one digit earlier than the older
    // fixed-boundary replay; previous input digits are quantified universally.
    const word=[]; for(let i=k+1;i<j-2;i++) word.push([xd[i],yd[i]]);
    minLen=Math.min(minLen,word.length); maxLen=Math.max(maxLen,word.length);
    if (emitBlocks) {
      console.log(`${n} ${word.length} ${word.map(([x,y]) => `${x}${y}`).join(' ')}`);
    } else {
      if(!checkSync(word,'L')) {failL++; if(firstFailL===null) firstFailL=n;}
      if(!checkSync(word,'R')) {failR++; if(firstFailR===null) firstFailR=n;}
    }
    states++;
  }
  if(n===maxStep) break;
  const next=highLevelNext(a,d);
  if(next===null) break;
  [a,d]=next;
}
if (!emitBlocks) console.log(JSON.stringify({states,anchor16,minLen,maxLen,failL,firstFailL,failR,firstFailR},null,2));
