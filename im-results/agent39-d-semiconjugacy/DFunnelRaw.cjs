'use strict';

/** Exact six-state D0 transition table: read-0,read-1 for each state. */
const TABLE = {
  A: [['1','R','B'],['0','R','E']],
  B: [['1','L','C'],['0','R','A']],
  C: [['1','L','A'],['1','L','D']],
  D: [['1','L','C'],['1','L','F']],
  E: [['0','L','C'],['0','L','B']],
  F: [['1','L','E'],null]
};

/** @typedef {{head: number, state: string, ones: Set<number>}} Machine */
/** @param {number} n @param {string} suffix @returns {Machine} */
function initial(n, suffix) {
  const ones = new Set();
  for (let i=0;i<n;i++) ones.add(i+1);
  for (let i=0;i<suffix.length;i++) if (suffix[i]==='1') ones.add(n+i+1);
  return {head:0,state:'F',ones};
}

/** @param {Machine} m @param {number} count @returns {Machine} */
function run(m,count) {
  for(let i=0;i<count;i++) {
    const b = m.ones.has(m.head) ? 1 : 0;
    const tr=TABLE[m.state][b];
    if (tr===null) throw Error('Unexpected raw halt before return');
    if(tr[0]==='1') m.ones.add(m.head);
    else m.ones.delete(m.head);
    m.head += tr[1]==='R' ? 1 : -1;
    m.state=tr[2];
  }
  return m;
}

/** @param {Machine} m @returns {string} */
function physical(m) {
  if(m.state!=='F' || m.ones.has(m.head)) throw Error('Wrong return head/state');
  const positions=[...m.ones].map(i=>i-m.head).sort((a,b)=>a-b);
  if(positions.some(i=>i<=0)) throw Error('Nonblank left of returned F');
  return positions.join(',');
}

/** @param {number} k @param {string} y @returns {string} */
function expected(k,y) {
  return physical(initial(8*k+11,y));
}

const TAILS=['','0','1','101','0110010','1111101','000101011'];
let cases=0; let largestSteps=0;
for(let k=0;k<=30;k++) {
  const tB=12*k*k+49*k+40;
  const tA=tB+4;
  for(const y of TAILS) {
    const B=run(initial(3*k+2,'011'+y),tB);
    const A=run(initial(3*k+3,'00'+y),tA);
    const b=physical(B),a=physical(A),want=expected(k,y);
    if(b!==a || a!==want) throw Error(`Collision failed for k=${k}, y=${y}`);
    cases++; largestSteps=Math.max(largestSteps,tA);
  }
}
console.log(JSON.stringify({machine:'1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---',
   collisionFamily:'I_(3k+2)(011 y) ~ I_(3k+3)(00 y)',kMax:30,tails:TAILS,
   checked:cases,maxRawStepsPerInput:largestSteps,exactDelay:4,status:'PASS'}));
