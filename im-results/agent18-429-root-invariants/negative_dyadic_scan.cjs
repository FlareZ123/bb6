#!/usr/bin/env node
"use strict";

/*
 * Experimental 2-adic negative-ray scan for the authentic #429
 * 29(mod32) odd-reset feeder.  NOT a proof of completeness or of BB(6).
 *
 * Source of Boolean semantics:
 *   im-results/agent33-429-24/BB429InverseKernel.lean
 *   im-results/agent6-harmonic429/BB429Mod8.lean
 *
 * The accepted Lean theorem BB429Kernel.cert_sound supplies soundness
 * for each checked affine certificate independently of this script.
 * For n=127+128*k, the terminal-burst equation gives
 * q=3*2^(n-5)-(3*k+4).  Thus at modulus M=2^E (E<=n-5),
 * q ≡ -(3*k+4) mod M.  We test the entire affine cylinder,
 * not the enormous concrete q and not a simulated root orbit.
 *
 * Usage:
 *     node negative_dyadic_scan.cjs [number_of_k] [modulus_exponent] [depth]
 * Example:
 *     node negative_dyadic_scan.cjs 1000000 64 100
 */

const N = Number(process.argv[2] ?? 100000);
const E = Number(process.argv[3] ?? 32);
const DEPTH = Number(process.argv[4] ?? 60);
if (!Number.isSafeInteger(N) || N<0 || N>10000000 ||
    !Number.isSafeInteger(E) || E<1 || E>100000 ||
    !Number.isSafeInteger(DEPTH) || DEPTH<0 || DEPTH>1024) {
  throw new Error("Expected N<=10e6, 1<=E<=100000, 0<=DEPTH<=1024");
}

const mod=(x,m)=>((x%m)+m)%m;
function allowed(a,b){
  const x=Number(mod(a,8n)), y=Number(mod(b,4n));
  return (x===0&&(y===0||y===2)) ||
    (x===1&&(y===0||y===1||y===2)) ||
    (x===2&&y===2) ||
    (x===3&&(y===1||y===2||y===3)) ||
    (x===4&&y===2) ||
    x===5 || (x===6&&y===2) ||
    (x===7&&(y===2||y===3));
}
function bad([A,a,B,b]){
  return (A%8n===0n&&B%4n===0n&&!allowed(a,b)) ||
    (A%2n===0n&&B%8n===0n&&a>0n&&a%2n===0n&&b%8n!==2n) ||
    (A%8n===0n&&B%8n===0n&&mod(a,8n)===7n&&mod(b,8n)===7n) ||
    (A%16n===0n&&B%8n===0n&&mod(a,16n)===1n&&mod(b,8n)===6n) ||
    (A%16n===0n&&B%8n===0n&&mod(a,16n)===5n&&mod(b,8n)===6n) ||
    (A%32n===0n&&B%16n===0n&&mod(a,32n)===5n&&mod(b,16n)===1n);
}
function cert(d,s){
  if (bad(s)) return true;
  if (d===0) return false;
  const [A,a,B,b]=s;
  if (a>=13n&&a%2n===1n&&A%2n===0n&&B%4n===0n){
    const f=[A/2n,(a-3n)/2n,B+A,b+a];
    return cert(d-1,f) &&
      (b%4n!==2n || cert(d-1,
        [A+B/4n,(4n*a+b-26n)/4n,B/2n,(b+4n)/2n]));
  }
  if (a>=6n&&a%2n===0n&&A%2n===0n&&B%4n===0n){
    return b%4n!==2n || cert(d-1,
      [A+B/4n,(4n*a+b-14n)/4n,B/2n,b/2n]);
  }
  return false;
}

const M=2n**BigInt(E);
let ruledOut=0;
let unknown=0;
const unknownIndices=[];
const started=Date.now();
for(let k=0;k<N;k++){
  const c=3n*BigInt(k)+4n, r=mod(-c,M);
  if(cert(DEPTH,[32n*M,32n*r+29n,64n*M,64n*r+55n])){
    ruledOut++;
  }else{
    unknown++;
    if(unknownIndices.length<100) unknownIndices.push(k);
  }
}
console.log(JSON.stringify({
  status:"EXPERIMENTAL, not a proof that all k are excluded",
  kRange:[0,N], modulusExponent:E, inverseDepth:DEPTH,
  certifiedCylinders:ruledOut, unknownCylinders:unknown,
  firstUnknownIndices:unknownIndices, elapsedMs:Date.now()-started
},null,2));
