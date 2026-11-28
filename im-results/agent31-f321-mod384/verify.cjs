#!/usr/bin/env node
"use strict";
const assert = require("node:assert/strict");
const M = 384, N = M*M, live = new Uint8Array(N), queue = new Int32Array(N);
let tail = 0, head = 0;
const mod = x => (x % M + M) % M;
function push(x,y) {const k=mod(x)*M+mod(y); if(!live[k]){live[k]=1;queue[tail++]=k;}}
push(6,1);
while(head<tail){
 const k=queue[head++],x=Math.floor(k/M),y=k%M;
 push(x-y-2,2*y+3); // high; guard intentionally dropped
 push(4*x+6,y-3*x); // far; guard intentionally dropped
 push(4*x+6,(x+y)%2 ? 1 : 2); // middle, parity retained
 if(x===y)push(2*x+4,1); // equal only if congruent
}
assert.equal(tail,7414);
const gates=[]; for(let d=0;d<M;d++)if(live[((d+1)%M)*M+d])gates.push(d);
assert.deepEqual(gates,[37,61,115,133,139,157,181,211,229,235,253,277,325,331,349]);
assert.equal(live[374*M+373],0);
let mask=0n;for(let k=0;k<N;k++)if(live[k])mask|=1n<<BigInt(k);
const hex=mask.toString(16);const fs=require("node:fs");
const lean=fs.readFileSync(__dirname+"/Mod384Graph.lean","utf8");
assert(lean.includes("def mask : Nat := 0x"+hex+"));
console.log(JSON.stringify({modulus:M,reachableResidues:tail,gateResidues:gates,excludedGateResidues:M-gates.length,checkedGraphBytes:Math.ceil(N/8)}));
