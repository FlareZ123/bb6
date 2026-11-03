'use strict';
const assert = require('node:assert/strict');

/** @typedef {readonly [number,number]} Pair */
/** @type {Array<[number,number,number] | null>} */
const rules = [];
const rle = '1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA';
for (const row of rle.split('_')) {
  for (const bit of [0,1]) {
    const code = row.slice(bit*3,bit*3+3);
    rules.push(code==='---' ? null : [Number(code[0]),code[1]==='R'?1:-1,code.charCodeAt(2)-65]);
  }
}

/** @param {number} u @param {number} w @returns {Pair|null} */
function next(u,w) {
  const m=Math.floor(w/2);
  if (w>=2*u+3) return [2*u+3,w-2*u-3];
  if (w===2*u+2) return [0,4*u+18];
  if (w===2*u+1) return [11,4*u+2];
  if (w===2*u) return [0,4*u+12];
  const d=u-m;
  if (w%2===0) {
    if (d===1) return [0,2*w+12];
    if (d%2===0) return [11,2*u+w-2];
    return [0,2*u+w+10];
  }
  if (d===1) return null;
  if (d===2) return [0,2*w+8];
  if (d%2===0) return w===1 ? [11,2*u+10]:[d+7,2*w-4];
  return [d+3,2*w];
}

/** @param {number} u @param {number} w @returns {boolean} */
function shield(u,w) {
  const x=u%6,y=w%6;
  return y===0 || y===4 ||
    (x===1 && (y===3 || y===5)) ||
    (x===3 && (y===1 || y===3)) ||
    (x===5 && (y===1 || y===5));
}

/** @param {number} u @param {number} w @returns {Set<number>} */
function tapeJ(u,w) {
  const left='11111'+'10'.repeat(u)+'1',right='1'.repeat(w+2)+'01';
  const tape=new Set();
  for(let i=0;i<left.length;i++) if(left[i]==='1')tape.add(i-left.length);
  for(let i=0;i<right.length;i++) if(right[i]==='1')tape.add(i);
  return tape;
}

/** @param {number} head @param {Set<number>} tape @returns {Pair|null} */
function decodeJ(head,tape) {
  if(!tape.size) return null;
  const a=[...tape],low=Math.min(...a),high=Math.max(...a);
  const h=head-low-6,w=high-head-3;
  if(h<0 || h%2 || w<0)return null;
  const u=h/2,expected=tapeJ(u,w);
  return a.length===expected.size && a.every(p=>expected.has(p-head)) ? [u,w]:null;
}

/** @param {Pair} seed @param {number} limit */
function rawMacro(seed,limit=100000) {
  let [u,w]=seed,q=0,head=0;
  const tape=tapeJ(u,w);
  for(let step=1;step<=limit;step++){
    const tr=rules[2*q+Number(tape.has(head))];
    if(tr===null) return [step,null];
    const [write,direction,to]=tr;
    if(write) tape.add(head);else tape.delete(head);
    head+=direction;q=to;
    if(q===0) {
      const mapped=decodeJ(head,tape);
      if(mapped!==null)return [step,mapped];
    }
  }
  throw new Error('raw bridge bound exceeded '+seed);
}

let x=20261103;
function random32(){x^=x<<13;x^=x>>>17;x^=x<<5;return x>>>0;}
for(let i=0;i<500000;i++) {
  const u=random32()%100000,w=random32()%100000;
  const out=next(u,w);
  assert.equal(out===null,w+1===2*u);
  if(out!==null){const rank=2*u+w,r2=2*out[0]+out[1];assert.ok(rank+3<=r2 && r2<=rank+31);}
  if(w>=2*u+3 && shield(u,w))assert.ok(shield(2*u+3,w-2*u-3));
  if(shield(u,w))assert.notEqual(w+1,2*u);
}
for(let u=0;u<6;u++) for(const w of [0,4]) {
  let a=u,b=w;const states=new Set();
  while(!states.has(a+','+b)) {
    states.add(a+','+b);
    assert.ok(shield(a,b));
    assert.notEqual((b+1)%6,(2*a)%6);
    [a,b]=[(2*a+3)%6,((b-2*a-3)%6+6)%6];
  }
}
// Independent raw simulation to the first accelerated section J(0,0) in 35 steps.
let state=0,head=0,tape=new Set();
for(let step=0;step<35;step++) {
  const [w,d,to]=rules[2*state+Number(tape.has(head))];
  if(w)tape.add(head);else tape.delete(head);
  state=to;head+=d;
}
assert.equal(state,0);
assert.deepEqual(decodeJ(head,tape),[0,0]);
const seeds=[[0,0],[0,12],[0,28],[3,9],[9,0],[9,16],[21,11],[23,18],[11,62],[25,37],[10,74],[0,1],[1,1],[2,3],[3,5],[5,9],[6,11],[8,3]];
for(const seed of seeds) {
  const [step,value]=rawMacro(seed);
  assert.deepEqual(value,next(...seed));
  console.log('raw macro '+seed.join(',')+' '+step+' primitive steps => '+(value?.join(',') ?? 'halt'));
}
let u=0,w=0,protectedCount=0,unprotectedCount=0;
const residues=[0,0,0],branches=new Map();
for(let i=0;i<3000000;i++){
  let kind;
  if(w>=2*u+3) kind=1;
  else if(w===2*u+2)kind=2;
  else if(w===2*u+1)kind=3;
  else if(w===2*u)kind=4;
  else if(w%2===0)kind=5;
  else kind=6;
  const after=next(u,w);
  assert.notEqual(after,null);
  if(kind!==1){assert.equal(after[1]%2,0); const r=after[1]%6;residues[r/2]++;if(r===2)unprotectedCount++;else protectedCount++;}
  [u,w]=after;
}
console.log(JSON.stringify({seed:20261103,randomChecks:500000,rawBridgeSeeds:seeds.length,rawBlankToJSteps:35,macroSteps:3000000,postTurnaroundResidues:{0:residues[0],2:residues[1],4:residues[2]},protectedCount,unprotectedCount,sourceRLE:rle,ok:true}));
