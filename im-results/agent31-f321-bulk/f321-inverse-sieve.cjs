#!/usr/bin/env node
// Exact inverse-graph regression for the F321 counter map at the pinned upstream
// cryptids@c86f1586... source. No claim that finite tests prove infinitude.
"use strict";
const assert = require("node:assert/strict");

function inverse(a,d) {
  assert(Number.isSafeInteger(a) && a>=0 && Number.isSafeInteger(d) && d>=0);
  const out=[];
  if (d>=3 && d%2===1) out.push([a+(d-3)/2+2,(d-3)/2,"high"]);
  if (d===1 && a>=4 && a%2===0) {
    const x=(a-4)/2; out.push([x,x,"equal"]);
  }
  if (d>=1 && a>=6 && a%4===2) {
    const x=(a-6)/4; out.push([x,d+3*x,"far"]);
  }
  if ((d===1||d===2) && a>=10 && a%4===2) {
    const x=(a-6)/4;
    for (let y=x+1;y<=3*x;y++) if ((y-x)%2 === (d===2 ? 0 : 1))
      out.push([x,y,"middle"]);
  }
  return out;
}
function step(a,d) {
  if (a>=d+2) return [a-d-2,2*d+3];
  if (a===d+1) return null;
  if (a===d) return [2*a+4,1];
  if (d>=3*a+1) return [4*a+6,d-3*a];
  return [4*a+6,(d-a)%2===0?2:1];
}
function excluded(d) {
  if (d%2===0) return "even";
  if (d%8===1) return "1mod8";
  if (d%8===7) return "7mod8";
  if (d%8!==3) return null;
  let k=(d-3)/8,t=0;
  while(k%4===2) { k=(k-2)/4; ++t; }
  if(k%4===0)return "base4-zero";
  if(k%4===3 && t%2===0)return "base4-three-even-depth";
  return null;
}
function main(max=30000) {
  assert(Number.isSafeInteger(max)&&max>=1&&max<=1000000);
  // Check all ordered pairs in a bounded square against literal source map.
  for(let a=0;a<70;a++)for(let d=0;d<70;d++){
    const z=step(a,d);
    if(z!==null) assert(inverse(...z).some(([x,y])=>x===a&&y===d));
    for(const [x,y] of inverse(a,d))assert.deepEqual(step(x,y),[a,d]);
  }
  let count=0,counts={},maxDepth=0;
  for(let d=0;d<max;d++){
    const kind=excluded(d);if(!kind)continue;
    count++;counts[kind]=(counts[kind]||0)+1;
    // Explore the COMPLETE inverse ancestry. The 1 mod 8 family can
    // branch twice at its first gate, with both branches terminating;
    // requiring a unique inverse is invalid even for a correct theorem.
    const todo=[[d+1,d,0]],seen=new Set();
    while(todo.length) {
      const [a,b,depth]=todo.pop(),key=a+","+b;
      if(seen.has(key))continue;
      seen.add(key);
      assert(!(a===1&&b===1),"Excluded gate reached authentic seed");
      assert(depth<=64,"Unexpected unclosed predecessor tree");
      assert(seen.size<=512,"Unexpected branching complexity");
      maxDepth=Math.max(maxDepth,depth);
      for(const [x,y] of inverse(a,b))todo.push([x,y,depth+1]);
    }
  }
  return {testedTerminalParameters:max,excludedCount:count,observedFraction:count/max,counts,maxDepth};
}
if(require.main===module){
  const max=Number(process.argv[2]||30000);
  process.stdout.write(JSON.stringify(main(max),null,2)+"\n");
}
module.exports={step,inverse,excluded,main};
