// Exact modular reproduction of the dense seven-edge U/Q branch.
// All exponentiation is modular BigInt; no full 2^n integer is constructed.
const mod = (x,m) => ((x % m) + m) % m;
function powMod(base,exp,m) {
  let x=base%m, e=exp, out=1n;
  while (e>0n) {
    if ((e&1n)!==0n) out=out*x%m;
    x=x*x%m;
    e>>=1n;
  }
  return out;
}
const p3=k=>3n**BigInt(k);

function computePrefix(r) {
  const n=887n+13122n*r, M=p3(17);
  const Q=mod(
    28n*powMod(2n,n,M)-2n*n+15n
      -powMod(2n,3406n,M)*(2n*n+3n),
    M
  );
  if (Q%p3(7)!==0n) return {n,Q};
  const d1=Q/p3(7);
  const g1=mod(
    64n*d1-16n*powMod(2n,n-5n,p3(10))-2n*(n-5n)-5n,
    p3(10)
  );
  const out={n,Q,g1};
  if (g1%3n!==0n) return out;
  const d2=g1/3n;
  const g2=mod(
    4n*d2-16n*powMod(2n,n-6n,p3(9))-2n*(n-6n)-5n,
    p3(9)
  );
  out.g2=g2;
  if (g2%3n!==0n) return out;
  const d3=g2/3n;
  const g3=mod(
    4n*d3-16n*powMod(2n,n-7n,p3(8))-2n*(n-7n)-5n,
    p3(8)
  );
  out.g3=g3;
  if (g3%3n!==0n || g3%9n!==0n) return out;
  const d4=g3/9n;
  const g4=mod(
    8n*d4-16n*powMod(2n,n-8n,p3(6))-2n*(n-8n)-5n,
    p3(6)
  );
  out.g4=g4;
  if (g4%3n!==0n || g4%9n!==0n) return out;
  const d5=g4/9n;
  const g5=mod(
    8n*d5-16n*powMod(2n,n-10n,p3(4))-2n*(n-10n)-5n,
    p3(4)
  );
  out.g5=g5;
  if (g5%3n!==0n || g5%9n!==0n) return out;
  const d6=g5/9n;
  const g6=mod(
    8n*d6-16n*powMod(2n,n-11n,p3(2))-2n*(n-11n)-5n,
    p3(2)
  );
  out.g6=g6;
  if (g6%3n!==0n) return out;
  const d7=g6/3n;
  const g7=mod(
    4n*d7-16n*powMod(2n,n-12n,3n)-2n*(n-12n)-5n,
    3n
  );
  out.g7=g7;
  return out;
}

// Lift one base-3 digit at a time. Each condition has exactly one good lift.
let r=0n, modulus=1n;
const liftSteps=[
  ["G2 divisible by 3","g2",3n],
  ["G3 divisible by 3","g3",3n],
  ["G3 divisible by 9","g3",9n],
  ["G4 divisible by 3","g4",3n],
  ["G4 divisible by 9","g4",9n],
  ["G5 divisible by 3","g5",3n],
  ["G5 divisible by 9","g5",9n],
  ["G6 divisible by 3","g6",3n],
  ["G7 divisible by 3","g7",3n]
];
const lifts=[];
for (const [condition,field,divisor] of liftSteps) {
  const good=[];
  for(let a=0n;a<3n;a++) {
    const candidate=r+modulus*a;
    const values=computePrefix(candidate);
    const value=values[field];
    if(value!==undefined && value%divisor===0n) {
      good.push({a,candidate,value});
    }
  }
  if(good.length!==1) {
    throw new Error(`${condition}: expected one lift, found ${good.length}`);
  }
  r=good[0].candidate;
  modulus*=3n;
  lifts.push({
    condition,
    digit:good[0].a.toString(),
    residue:r.toString(),
    modulus:modulus.toString(),
    value:good[0].value.toString()
  });
}
if(r!==1618n || modulus!==p3(9)) {
  throw new Error("Unexpected seven-edge Hensel cylinder");
}
const main=computePrefix(r);
const {n,Q,g1,g2,g3,g4,g5,g6,g7}=main;
if(Q%p3(9)!==0n || Q%p3(10)===0n) throw new Error("Q valuation is not 9");
if(g1%3n!==0n || g1%9n===0n) throw new Error("G1 valuation is not 1");
if(g2%3n!==0n || g2%9n===0n) throw new Error("G2 valuation is not 1");
if(g3%9n!==0n || g3%27n===0n) throw new Error("G3 valuation is not 2");
if(g4%p3(4)!==0n || g4%p3(5)===0n) throw new Error("G4 valuation is not 4");
if(g5%p3(3)!==0n || g5%p3(4)===0n) throw new Error("G5 valuation is not 3");
if(g6%3n!==0n || g6%9n===0n) throw new Error("G6 valuation is not 1");
if(g7%3n!==0n) throw new Error("G7 is not divisible by 3");

// Exact coefficient bit lengths for X_i=A_i*2^n+B_i*n+C_i, i=0,...,6.
const bitLength=x=>(x<0n?-x:x).toString(2).length;
let B=-2n-(1n<<3407n), C=15n-3n*(1n<<3406n), E=0;
const coefficientBits=[{level:0,B:bitLength(B),C:bitLength(C)}];
const stages=[[4,9],[0,6],[0,7],[1,9],[1,11],[1,12]];
for(let i=0;i<stages.length;i++) {
  const [t,sigma]=stages[i];
  E=i===0?t+3:E+t+1;
  B=4n*(1n<<BigInt(t))*B-2n*p3(E);
  C=4n*(1n<<BigInt(t))*C-(2n*BigInt(t-sigma)+5n)*p3(E);
  coefficientBits.push({level:i+1,B:bitLength(B),C:bitLength(C)});
}
if(coefficientBits.some(x=>x.B>3427 || x.C>3427)) {
  throw new Error("Unexpected coefficient bound");
}

const limitingRatios=[
  [14336n,2187n],
  [44704n,6561n],
  [147680n,19683n],
  [1103168n,177147n],
  [12626560n,1594323n],
  [99988288n,14348907n],
  [340741280n,43046721n]
];
for(const [num,den] of limitingRatios) {
  if(5n*num<=31n*den || 100n*num>=793n*den) {
    throw new Error("A limiting band ratio is outside (6.2,7.93)");
  }
}
const bandParameters=[[4,9],[0,6],[0,7],[1,9],[1,11],[1,12],[0,12]];
for(const [t,sigma] of bandParameters) {
  if((1n<<BigInt(sigma))>=p3(t+1)*2048n) {
    throw new Error("A band scaling factor is not below 2^11");
  }
}
if(n<7000n) throw new Error("The explicit index is below the band-bound threshold");

console.log(JSON.stringify({
  r:r.toString(),
  classModulus:modulus.toString(),
  n:n.toString(),
  residues:{
    Q:Q.toString(),G1:g1.toString(),G2:g2.toString(),G3:g3.toString(),
    G4:g4.toString(),G5:g5.toString(),G6:g6.toString(),G7:g7.toString()
  },
  valuations:{Q:9,G1:1,G2:1,G3:2,G4:4,G5:3,G6:1,G7:"divisible by 3"},
  lifts,
  exponents:bandParameters,
  coefficientBitLengths:coefficientBits,
  limitingBandRatios:limitingRatios.map(([num,den])=>({num:num.toString(),den:den.toString()})),
  bandBound:"for n >= 7000, all seven normalized ratios differ from their limits by < 2^-62"
},null,2));
