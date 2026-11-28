#!/usr/bin/env node
'use strict';
/*
 * Raw56 leaf17557 original six-state literal blank run, versus the complete
 * parameterized triad event substitution in Raw56LE17557EventSubstitution.lean.
 *
 * Each event is:
 *   ["AN",a,b,c,last] - ordinary A triad, b>=6
 *   ["AC",a,c,d,last] - A carry triad, b=5, immediate left one-run d
 *   ["B",a,b,last]   - B triad, 7-cell left runway
 * 'last' records that the rightmost one-run touched by this event is final.
 *
 * Finite replay, not an all-time theorem. External source proof of the
 * all-epoch event/substitution relation is still open.
 *
 * Run node 17557-event-substitution-census.js [maxN=11].
 * maxN=11 checks 17,235,271 primitive steps, 39,364 exact event records.
 */
const maxN = Number(process.argv[2] || 11);
if (!Number.isInteger(maxN) || maxN < 3 || maxN > 11) {
  throw Error('Choose integer checkpoint 3<=maxN<=11');
}
const T = n => 4*4**n+8*3**(n-1)-7*2**n-1;
const transitions = [
  [[1,1,1],[1,-1,0]], [[1,1,2],[1,1,1]],
  [[0,1,3],[0,1,2]], [[1,-1,3],[1,-1,4]],
  [[1,-1,5],[0,-1,4]], [[0,-1,0],null]
];
// Literal 1RB1LA_1RC1RB_0RD0RC_1LD1LE_1LF0LE_0LA--- .
const base = [
  ['AC',2,7,0,true], ['B',6,12,true],
  ['B',2,5,false], ['AC',2,8,0,false]
];
function expand(e) {
  const kind=e[0], a=e[1], b=e[2], c=e[3];
  const last=e[e.length-1], eps=Number(last);
  if (kind==='AN') return [
    ['AN',2*a+2,2*b+3,2*c+eps,last],
    ['B',2,2*c+eps+5,last],
    ['AC',2,2*c+eps+8,0,last]
  ];
  if (kind==='AC') return [
    ['AN',2*a+2,13,2*b+eps,last],
    ['B',2,2*b+eps+5,last],
    ['AC',2,2*b+eps+8,2*a+2*c+4,last]
  ];
  if (kind==='B') return [
    ['B',2*a+2,2*b+3+eps,last],
    ['B',2,5,false],
    ['AC',2,8,0,false]
  ];
  throw Error('Invalid event kind '+kind);
}
const expected={2:base};
for (let n=3;n<maxN;n++) expected[n]=expected[n-1].flatMap(expand);

let state=0,head=0,maxOne=0,returnCount=0,firstD=null,Dreads=[],prev=null;
const tape=new Set(),stats={};
function rightRuns(pos) {
  const out=[];
  for(let x=pos+1;x<=maxOne;) {
    while(x<=maxOne&&!tape.has(x))x++;
    let len=0;
    while(x<=maxOne&&tape.has(x)){len++;x++;}
    if(len)out.push(len);
  }
  return out;
}
function leftOnes(pos) {
  let count=0;
  while(tape.has(pos-1-count))count++;
  return count;
}
function finishTriad(time) {
  if(!prev)return;
  const [a,b,c]=prev.runs, pattern=Dreads.join('');
  const e = pattern==='101'
    ? (b>=6?['AN',a,b,c,prev.runs.length===3]
           : b===5?['AC',a,c,prev.left,prev.runs.length===3]:null)
    : pattern==='001'?['B',a,b,prev.runs.length===2]:null;
  if(!e)throw Error('Unrecognized triad at step '+prev.time+
                   ' Dreads='+pattern+' right='+JSON.stringify(prev.runs));
  const want=expected[prev.epoch][prev.index];
  if(JSON.stringify(e)!==JSON.stringify(want)) {
    throw Error('Full descriptor mismatch at epoch '+prev.epoch+
      ', local idx '+prev.index+', primitive step '+prev.time+
      ', actual='+JSON.stringify(e)+', predicted='+JSON.stringify(want));
  }
  const row=stats[prev.epoch]||(stats[prev.epoch]={matched:0,steps:0});
  row.matched++;
  row.steps+=time-prev.time;
  if(row.matched===expected[prev.epoch].length &&
    row.steps!==T(prev.epoch+1)-T(prev.epoch)) {
    throw Error('Epoch primitive-clock mismatch n='+prev.epoch);
  }
}
const started=Date.now();
for(let time=0;time<=T(maxN);time++){
  if(state===0&&!tape.has(head)&&time>=T(2)){
    if(returnCount%3===0){
      finishTriad(time);
      Dreads=[];
      let epoch=2;
      while(epoch+1<=maxN&&time>=T(epoch+1))epoch++;
      prev={time,epoch,index:stats[epoch]?.matched||0,
            runs:rightRuns(head),left:leftOnes(head)};
    }
    returnCount++;
    firstD=null;
  }
  if(time===T(maxN))break;
  const read=tape.has(head)?1:0;
  if(state===3&&firstD===null&&time>=T(2)){
    firstD=read;
    Dreads.push(read);
  }
  const action=transitions[state][read];
  if(!action)throw Error('Undefined F1 at primitive step '+time);
  const [write,direction,next]=action;
  if(write){tape.add(head);if(head>maxOne)maxOne=head;}
  else tape.delete(head);
  head+=direction;
  state=next;
}
if(state!==0||tape.has(head))throw Error('End is not A-on-blank');
let total=0;
for(let n=2;n<maxN;n++){
  const row=stats[n],needed=expected[n].length;
  if(!row||row.matched!==needed||row.steps!==T(n+1)-T(n)){
    throw Error('Incomplete epoch '+n);
  }
  total+=row.matched;
  console.log(JSON.stringify({epoch:n,events:row.matched,
    primitiveSteps:row.steps}));
}
console.log(JSON.stringify({status:'PASS literal original blank-source replay',
  checkpoint:maxN,total_events:total,primitive_steps:T(maxN),
  state,head,ones:tape.size,elapsed_ms:Date.now()-started}));
