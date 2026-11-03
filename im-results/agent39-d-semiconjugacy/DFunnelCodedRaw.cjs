'use strict';

/** Standard six-state D0 raw machine transition rules. */
const TABLE = [
  [[1,1,1],[0,1,4]], [[1,-1,2],[0,1,0]],
  [[1,-1,0],[1,-1,3]], [[1,-1,2],[1,-1,5]],
  [[0,-1,2],[0,-1,1]], [[1,-1,4],null]
];
/** @param {number} n @param {string} suffix @returns {{pos:number,state:number,ones:Set<number>}} */
function input(n,suffix) {
  const ones=new Set();
  for(let i=1;i<=n;i++) ones.add(i);
  for(let i=0;i<suffix.length;i++) if(suffix[i]==='1') ones.add(n+1+i);
  return {pos:0,state:5,ones};
}
/** @param {{pos:number,state:number,ones:Set<number>}} tape @param {number} count */
function run(tape,count) {
  for(let i=0;i<count;i++) {
    const action=TABLE[tape.state][Number(tape.ones.has(tape.pos))];
    if(!action) throw Error('Raw halt before promised return');
    if(action[0]) tape.ones.add(tape.pos);
    else tape.ones.delete(tape.pos);
    tape.pos+=action[1];tape.state=action[2];
  }
  return tape;
}
/** @param {{pos:number,state:number,ones:Set<number>}} tape @returns {string} */
function snapshot(tape) {
  if(tape.state!==5 || tape.ones.has(tape.pos)) throw Error('Bad return state');
  const positions=[...tape.ones].map(x=>x-tape.pos).sort((a,b)=>a-b);
  if(positions.some(x=>x<=0)) throw Error('Nonblank left of head');
  return positions.join(',');
}
/** @param {number[]} word @param {number} m @returns {{code:string,weight:number,cost:number}} */
function coded(word,m) {
  let code='';let weight=0;let cost=0;
  for (const x of word) {
    if(x===0) {code+='10';weight++;cost+=2;m++;}
    else {code+='111';weight+=4;cost+=6*m+41;m+=4;}
  }
  return {code,weight,cost};
}
const TAILS=['','0','1','101','0110010'];
let passed=0;let maxRawSteps=0;let maxCodeLength=0;
for(let len=0;len<=7;len++) {
  for(let mask=0;mask<(1<<len);mask++) {
    const word=Array.from({length:len},(_,j)=>(mask>>j)&1);
    for(let k=0;k<=7;k++) {
      const {code,weight,cost}=coded(word,4*k+3);
      const timeB=12*k*k+49*k+40;
      const timeA=12*k*k+41*k+32+cost+2*(4*k+3+weight)+6;
      const delay=4+cost+2*weight;
      if(timeA-timeB!==delay) throw Error('Bad delay formula');
      for(const tail of TAILS) {
        const b=snapshot(run(input(3*k+2,'0'+'1'.repeat(2*weight+2)+tail),timeB));
        const a=snapshot(run(input(3*k+3,'0'+code+'0'+tail),timeA));
        const target=snapshot(input(8*k+11+2*weight,tail));
        if(b!==target || a!==target) throw Error(`Bad funnel at len=${len},mask=${mask},k=${k},tail=${tail}`);
        passed++;maxRawSteps=Math.max(maxRawSteps,timeA);maxCodeLength=Math.max(maxCodeLength,code.length);
      }
    }
  }
}
console.log(JSON.stringify({status:'PASS',machine:'1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---',
  testedMixedCodeLength:7,kMax:7,tails:TAILS,rawPairs:passed,maxRawSteps,maxCodeLength}));
