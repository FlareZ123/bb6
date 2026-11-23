"use strict";

// Exact BigInt regression for Uniform343Shadow.md, no dependencies.
// All-n statements are proved algebraically in the accompanying note;
// this checks their symbolic coefficient equalities and two base trajectories.
function check(p, why) { if (!p) throw new Error(why); }
const pow2 = n => 1n << BigInt(n);
const ceilLog2 = x => { check(x > 0n, "positive log argument"); return (x - 1n).toString(2).length; };
const f = [
  {
    name: "I", n: 5362, period: 595056, a: 17n, b: 1058n, c: 636n,
    p: 491n, transient: [6, 2], initial: [5290n, 66515n],
    post: [21160n, 238409n], expectedCycles: 36
  },
  {
    name: "II", n: 9538, period: 703248, a: 87n, b: 1198n, c: 712n,
    p: 141n, transient: [8, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 2, 4],
    initial: [5990n, 71485n],
    post: [401982095360n, 4624852107897n], expectedCycles: 64
  }
];
function idealCycle() {
  let p = 249n, word = [], S = 0;
  do {
    let k = 1;
    while (pow2(k) * p < 343n) k++;
    const pNext = pow2(k) * p - 343n;
    check(1n <= pNext && pNext <= 342n && k <= 9, "ideal phase out of range");
    word.push(k); S += k; p = pNext;
    check(word.length <= 73, "unexpected reference period");
  } while (p !== 249n);
  check(word.length === 73 && S === 147, "reference cycle mismatch");
  return word;
}
function symbolic(fam) {
  // Numerator coefficients of (P,n,1) over a common denominator den.
  const den = 49n * fam.b;
  let D = [18n * fam.b - 196n * fam.a,
           14n * fam.b,
           48n * fam.b + 196n * fam.c];
  let N = [49n * (14n * fam.b - 28n * fam.a),
           98n * fam.b,
           49n * (28n * fam.c - fam.b)];
  function error(Q,p,expected) {
    const out = D.map((x,i) => Q * x - p * N[i]);
    check(out[0] === 0n, "leading P coefficient of rational offset not zero");
    check(out[1] === den*expected[0] && out[2] === den*expected[1],
      "polynomial error identity does not match the note");
  }
  let p = fam.p, Q = 21952n;
  error(Q,p,fam.initial);
  for (const k of fam.transient) {
    const pn = pow2(k) * p - Q;
    check(pn > 0n && pn < Q && k <= 8, "transient not an ideal parent digit");
    D = D.map((x,i) => pow2(k)*x - N[i] - (i === 2 ? den*(2n*BigInt(k)+1n) : 0n));
    N[2] += 2n*BigInt(k)*den;
    p = pn;
  }
  check(p === 15936n, "wrong transient destination");
  const out = D.map((x,i) => 343n*x - 249n*N[i]);
  check(out[0] === 0n && out[1] === den*fam.post[0] && out[2] === den*fam.post[1],
    "post-transient error polynomial does not match the note");
}
function actualState(fam) {
  const n = BigInt(fam.n), P = pow2(fam.n);
  const numer = fam.a*P - fam.c;
  check(numer % fam.b === 0n, "u not integral");
  const u = numer/fam.b;
  const defect = 18n*P - 196n*u + 14n*n + 48n;
  check(defect % 49n === 0n, "D not integral");
  const state = {
    D: defect / 49n,
    N: 14n*P - 28n*u + 2n*n - 1n,
    m: 14n*u - 2n*n - 3n
  };
  check(state.D > 4n && state.D%2n === 0n, "source D initial guard");
  check(state.N > P && state.N%2n === 1n && state.m > n+32n,
    "initial scale, oddness or remaining cost");
  check(state.N-state.D-7n >= 8n && (state.N-state.D-7n)%4n === 0n,
    "initial b source guard");
  return {P,state};
}
function sourceParent(s,k) {
  const K = BigInt(k);
  check(K > 0n && K <= s.m && s.D >= 4n &&
      s.D%2n === 0n && s.N%2n === 1n &&
      s.N-s.D-7n >= 8n && (s.N-s.D-7n)%4n === 0n,
      "source state guard");
  const Np = s.N + 2n*K, scaled = pow2(k)*s.D;
  check(scaled >= Np+1n && scaled <= 2n*Np-14n,
    "interval (A) failed");
  const Dp = scaled-Np-1n, mp = s.m-K;
  check(Dp >= 4n && Dp%2n === 0n && Np-Dp-7n >= 8n &&
      (Np-Dp-7n)%4n === 0n, "new parent source guard failed");
  return {D:Dp,N:Np,m:mp};
}
function proveBase(fam,word) {
  const {P,state:root} = actualState(fam);
  let state=root, p=fam.p;
  const e0 = 21952n*state.D - p*state.N;
  check(e0 === fam.initial[0]*BigInt(fam.n)+fam.initial[1],
    "transient initial error failed");
  const et = e0 + 89933248n + 1009792n;
  check(pow2(32)*et <= P, "uniform transient shadow bound failed");
  for (const k of fam.transient) {
    p = pow2(k)*p-21952n;
    state=sourceParent(state,k);
  }
  check(p === 15936n, "phase not 249/343");
  const eps = 343n*state.D-249n*state.N;
  check(eps === fam.post[0]*BigInt(fam.n)+fam.post[1],
    "post-transient epsilon mismatch");
  const E = eps+3152215n+17150n;
  const b=ceilLog2(E), r=Math.floor((fam.n-b)/147);
  check(r === fam.expectedCycles, "unexpected guaranteed base count");
  let cost=0,steps=0,phase=249n;
  for (let cycle=0;cycle<r;cycle++) {
    for (const k of word) {
      const nextP = pow2(k)*phase-343n;
      cost += k;
      check(pow2(cost)*E<=P,"sufficient uniform-stability inequality failed");
      state=sourceParent(state,k);
      phase=nextP;
      steps++;
    }
    check(phase === 249n, "reference cycle not returned");
  }
  check(cost === 147*r && steps === 73*r, "cycle count mismatch");
  return {
    family:fam.name, n:fam.n,
    transient:fam.transient,
    initialError:String(e0), postError:String(eps),
    E:String(E), ceilLog2E:b,
    uniformCycles:r, validReverseEdges:steps,
    validReverseCost:cost
  };
}
const word=idealCycle();
// All-n elementary side inequalities used in the note.
check(pow2(83-32)>6000n*83n+91015040n, "transient induction base");
for(const x of f) {
  symbolic(x);
  const n=BigInt(x.n),E0=x.post[0]*n+x.post[1]+3169365n;
  const eSlope = x.name==="I" ? pow2(15) : pow2(39);
  check(E0<=eSlope*n && x.post[0]<eSlope, "asymptotic bound");
}
console.log(JSON.stringify({referenceSymbols:word.length, referenceBitCost:147,
  // The word itself may be compared with Agent 50's reference cycle.
  referenceWord:word, tests:f.map(x=>proveBase(x,word))},null,2));
