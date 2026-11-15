// Exact-BigInt audit of the depth-14 affine inverse certificate for the
// long-burst branch-9/10 residue families. This is an experiment, not a proof.
// The Lean source of truth is BB429InverseKernelExtended.lean.

const allowedByN = {
  1:[4,8], 3:[1,5,9], 5:[2,10,14], 7:[7,11,15],
  9:[0,4], 11:[1,5,13], 13:[6,10,14], 15:[3,7,11],
  17:[0,12], 19:[1,9,13], 21:[2,6,10], 23:[3,7,15],
  25:[8,12], 27:[5,9,13], 29:[2,6,14], 31:[3,11,15]
};

const allowed8 = new Set([
  "0,0","0,2", "1,0","1,1","1,2", "2,2",
  "3,1","3,2","3,3", "4,2", "5,0","5,1","5,2","5,3",
  "6,2", "7,2","7,3"
]);

const mod = (x,m) => ((x % m) + m) % m;
const key = s => [s.A,s.a,s.B,s.b].join(",");

function bad(s) {
  const {A,a,B,b} = s;
  return (
    (A%8n===0n && B%4n===0n && !allowed8.has(`${mod(a,8n)},${mod(b,4n)}`)) ||
    (A%2n===0n && B%8n===0n && a>0n && a%2n===0n && b%8n!==2n) ||
    (A%8n===0n && B%8n===0n && a%8n===7n && b%8n===7n) ||
    (A%16n===0n && B%8n===0n && a%16n===1n && b%8n===6n) ||
    (A%16n===0n && B%8n===0n && a%16n===5n && b%8n===6n) ||
    (A%32n===0n && B%16n===0n && a%32n===5n && b%16n===1n) ||
    (A%16n===0n && B%8n===0n && a%16n===11n && ![2n,6n,7n].includes(b%8n)) ||
    (A%32n===0n && B%8n===0n && [19n,27n].includes(a%32n) && ![2n,7n].includes(b%8n)) ||
    (A%16n===0n && B%8n===0n && a>=33n && a%16n===9n && b%8n===5n) ||
    (A%32n===0n && B%8n===0n && a>=33n && a%32n===13n && b%8n===1n) ||
    (A%32n===0n && B%8n===0n && a>=61n && a%32n===5n && b%8n===1n)
  );
}

function odd(s) {
  return s.a>=13n && s.a%2n===1n && s.A%2n===0n && s.B%4n===0n;
}
function even(s) {
  return s.a>=6n && s.a%2n===0n && s.A%2n===0n && s.B%4n===0n;
}
function F(s) {
  return {A:s.A/2n, a:(s.a-3n)/2n, B:s.B+s.A, b:s.b+s.a};
}
function S(s) {
  return {A:s.A+s.B/4n, a:(4n*s.a+s.b-26n)/4n, B:s.B/2n, b:(s.b+4n)/2n};
}
function E(s) {
  return {A:s.A+s.B/4n, a:(4n*s.a+s.b-14n)/4n, B:s.B/2n, b:s.b/2n};
}

const memo = new Map();
function cert(depth,s) {
  const k = depth+":"+key(s);
  if (memo.has(k)) return memo.get(k);
  let result;
  if (bad(s)) result = true;
  else if (depth===0) result = false;
  else if (odd(s)) {
    result = cert(depth-1,F(s)) && (s.b%4n===2n ? cert(depth-1,S(s)) : true);
  } else if (even(s)) {
    result = s.b%4n===2n ? cert(depth-1,E(s)) : true;
  } else result = false;
  memo.set(k,result);
  return result;
}

// Every odd n in [19,529] occurs once for its n mod32 class.
const samples = [];
for (const n32 of Object.keys(allowedByN).map(Number)) {
  const n0 = n32 < 18 ? n32+32 : n32;
  const branch = n32%4===1 ? 9 : 10;
  const c = branch===9 ? 10n : 6n;
  const C = branch===9 ? 25n : 21n;
  for (let k=0;k<16;k++) {
    const n = n0+32*k;
    const nn = BigInt(n);
    for (const d16 of allowedByN[n32]) {
      for (let j=0;j<4;j++) {
        const d = d16+16*j;
        const dd = BigInt(d);
        const numerator = 2n*dd-3n*nn-C;
        if (numerator%4n!==0n) throw new Error(`nonintegral intercept n=${n} d=${d}`);
        const A = 64n*(2n**nn)+32n;
        const a = (2n**nn)*(dd+c)+numerator/4n;
        const B = 64n*((2n**(nn+1n))-1n);
        const b = 2n*(a-dd)+1n;
        const state = {A,a,B,b};
        if (A%32n!==0n || B%8n!==0n) throw new Error("coefficient divisibility failure");
        samples.push({n,d,n32,d16,branch,excluded:cert(14,state)});
      }
    }
  }
}

const classes = new Map();
for (const row of samples) {
  const k = `${row.n32},${row.d16}`;
  if (!classes.has(k)) classes.set(k,{n32:row.n32,d16:row.d16,branch:row.branch,total:0,excluded:0});
  const x = classes.get(k);
  x.total++;
  if (row.excluded) x.excluded++;
}
const summary = [...classes.values()].map(x => ({
  ...x,
  status: x.excluded===x.total ? "all" : x.excluded===0 ? "none" : "partial"
}));
console.log(JSON.stringify({
  depth:14,
  nRange:[19,529],
  samples:samples.length,
  excluded:samples.filter(x=>x.excluded).length,
  fullClasses:summary.filter(x=>x.status==="all").length,
  partialClasses:summary.filter(x=>x.status==="partial").length,
  untouchedClasses:summary.filter(x=>x.status==="none").length,
  memoStates:memo.size,
  classes:summary
},null,2));
