"use strict";

// Algebraic sanity checks for the cost recurrences derived in PrimitiveStepCost.md.
// This tests summation identities only; it does not compile Lean or prove
// the RLE soundness/cost-indexed semantics.

const dr0One = (c0, bot, S) => 6n*c0 + 6n*bot + 46n + S;
const dr0Sum = (q, c0, bot, S) => {
  let x = 0n;
  for (let i=0n; i<q; i++) x += dr0One(c0+4n*i, bot+q-i, S) + 4n;
  return x;
};
const dr0Formula = (q,c0,bot,S) =>
  6n*q*(c0+bot) + 15n*q*q + 41n*q + q*S;

const rnOne = (c0,bot,S) => 6n*c0 + 6n*bot + 61n + S;
const rnSum = (q,bot,S) => {
  let x = 0n;
  for (let i=0n; i<q; i++) x += rnOne(0n,bot+q-i,S+30n*i);
  return x;
};
const rnFormula = (q,bot,S) =>
  6n*q*bot + 18n*q*q + 49n*q + q*S;

const p1One = (r,bot,S) => 10n*r + 6n*bot + 75n + S;
const p1Sum = (q,r,bot,S) => {
  let x = 0n;
  for (let i=0n; i<q; i++) x += p1One(r,bot+q-i,S+i*(6n*r+48n));
  return x;
};
const p1Formula = (q,r,bot,S) =>
  q*(10n*r+6n*bot+6n*q+75n+S) + (6n*r+42n)*q*(q-1n)/2n;

const p2OneBound = (r,bot,S) =>
  15n*r*r + 6n*r*bot + 113n*r + 12n*bot + 165n + (r+2n)*S;
const p2SumBound = (q,r,bot,S) => {
  let x = 0n;
  for (let i=0n; i<q; i++)
    x += p2OneBound(r,bot+(q-i)*(r+1n),S+i*(24n*r+48n));
  return x;
};
const p2Formula = (q,r,bot,S) =>
  q*(15n*r*r+113n*r+165n)
  + (6n*r+12n)*(q*bot+(r+1n)*q*(q+1n)/2n)
  + (r+2n)*(q*S+(24n*r+48n)*q*(q-1n)/2n);

let checks = 0;
const failures = [];
const check = (name, lhs, rhs, params) => {
  checks++;
  if (lhs !== rhs) failures.push({name,params:params.map(String),lhs:String(lhs),rhs:String(rhs)});
};

for (let q=0n; q<=5n; q++) {
  for (let c0=0n; c0<=3n; c0++) {
    for (let bot=0n; bot<=4n; bot++) {
      for (let S=0n; S<=7n; S++) {
        check("clean_DR0_zeros",dr0Sum(q,c0,bot,S),dr0Formula(q,c0,bot,S),[q,c0,bot,S]);
        check("clean_RNIL_zero_pow",rnSum(q,bot,S),rnFormula(q,bot,S),[q,bot,S]);
        for (let r=0n; r<=4n; r++) {
          check("clean_P1_pow",p1Sum(q,r,bot,S),p1Formula(q,r,bot,S),[q,r,bot,S]);
          check("clean_P2_pow",p2SumBound(q,r,bot,S),p2Formula(q,r,bot,S),[q,r,bot,S]);
        }
      }
    }
  }
}

if (failures.length) {
  process.stderr.write(JSON.stringify({checks,failures},null,2)+"\\n");
  process.exitCode = 1;
} else {
  process.stdout.write(`passed ${checks} deterministic BigInt recurrence checks\\n`);
}
