#!/usr/bin/env node
/*
  Exact finite trace regression for D-start Cryptid low-E source rows.
  This is COMPUTATIONAL EVIDENCE, not a universal proof.

  D0 table: 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---
  0=A,1=B,2=C,3=D,4=E,5=F.
  State F at an intermediate moment is not a physical return unless the
  old left half-plane is entirely blank and the scanned symbol is zero.
*/
const table = [
  [[1, +1, 1], [0, +1, 4]],
  [[1, -1, 2], [0, +1, 0]],
  [[1, -1, 0], [1, -1, 3]],
  [[1, -1, 2], [1, -1, 5]],
  [[0, -1, 2], [0, -1, 1]],
  [[1, -1, 4], null],
];
function makeMachine(tape, state, head) {
  return { tape, state, head, halted: false };
}
function advance(c) {
  const ins = table[c.state][Number(c.tape.has(c.head))];
  if (ins === null) { c.halted = true; return; }
  const [write, direction, state] = ins;
  if (write) c.tape.add(c.head); else c.tape.delete(c.head);
  c.head += direction; c.state = state;
}
function physicalReturn(c) {
  return c.state === 5 && !c.tape.has(c.head) &&
    ![...c.tape].some(x => x < c.head);
}
function eLow(k,q) {
  const tape = new Set();
  // F/0 section with 3k+4 unary ones, then 0 (10)^q 0.
  const a = 3*k+4;
  for (let j=1; j<=a; j++) tape.add(j);
  for (let j=0; j<q; j++) tape.add(a+2+2*j);
  const c=makeMachine(tape,5,0);
  const limit=12*k*k+49*k+50+4*q;
  let firstF=null,firstPhysical=null;
  for (let t=1; t<=limit; t++) {
    advance(c);
    if (c.halted) throw new Error(`unexpected halt at k=${k}, q=${q}, t=${t}`);
    if (c.state===5 && firstF===null) firstF=t;
    if (physicalReturn(c) && firstPhysical===null) firstPhysical=t;
  }
  return {k,q,firstF,firstPhysical,expected:limit};
}
function cBase(m) {
  // Source cBase: C scanning 1, left= (10)^(m+2) 11, arbitrary right.
  const left=[];
  for(let j=0;j<m+2;j++) left.push(1,0);
  left.push(1,1);
  const tape=new Set([0]);
  left.forEach((bit,j)=>{if(bit)tape.add(-1-j)});
  const c=makeMachine(tape,2,0);
  advance(c); advance(c);
  return {m,stateAt2:c.state,leftOneCount:[...tape].filter(x=>x<c.head).length,
    scannedZeroAt2:!tape.has(c.head),physicalAt2:physicalReturn(c)};
}
let cases=0;
for(let k=0;k<=12;k++)for(let q=0;q<=12;q++){
  const x=eLow(k,q);
  if (x.firstPhysical!==x.expected ||
      x.firstF!==12*k*k+41*k+43+4*q)
    throw new Error("low-E mismatch: "+JSON.stringify(x));
  cases++;
}
for(let m=0;m<=12;m++){
  const x=cBase(m);
  if (x.stateAt2!==5 || x.leftOneCount<1 || x.physicalAt2)
    throw new Error("C-base mismatch: "+JSON.stringify(x));
}
console.log(JSON.stringify({
  machine:"D-start Cryptid D0",testedLowERows:cases,testedCBase:13,
  lowEFirstExample:eLow(0,0),
  lowEHighExample:eLow(12,12),cBaseExample:cBase(0),
  evidence:"finite exact simulation, not an all-parameter proof"
},null,2));
