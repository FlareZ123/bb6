"use strict";
const BASE=900900, EXPECTED_PER_J=218715580637067540n;
const C7=[6,3,1], Y7=[1,5,3], ALPHA11=[5,4,9,6,10,1,2,8,0,7];
const T1_NONCYL=[[8,9,29,30],[5,6,26,27],[17,18,38,39]];
const EXTRA=[[18,3,19n],[28,18,29n],[36,7,37n],[60,35,61n],[66,5,67n],[39,9,79n],[100,18,101n]];
const mod=(a,m)=>((a%m)+m)%m;
function powMod(a,e,m){let r=1%m;a%=m;while(e>0){if(e%2)r=r*a%m;a=a*a%m;e=Math.floor(e/2);}return r;}
function pct(n,d,digits=6){const scale=10n**BigInt(digits),z=(100n*n*scale+d/2n)/d;return (z/scale)+"."+String(z%scale).padStart(digits,"0")+"%";}
const weightAll=new Array(BASE),weightWithout19=new Array(BASE);
for(let w=0;w<BASE;w++){let all=1n,no19=1n;for(const [m,res,p] of EXTRA)if(w%m!==res){all*=p;if(p!==19n)no19*=p;}weightAll[w]=all;weightWithout19[w]=no19;}
let baseTotal=0n,t1Non=0n;const t1CylByJmod3=[0n,0n,0n];
let t2Resolved=0n,t2Cylinder=0n,t3Resolved=0n,t3Cylinder=0n;
let t4Resolved=0n,t4P5=0n,t4P7=0n,t4Both=0n;
for(let j=0;j<33;j++){
 const c11=mod(9-j,11);
 for(let w=0;w<BASE;w++){
  if(w%4===0&&w%5!==4)continue;
  if(w%3===1&&w%7!==C7[j%3])continue;
  if(w%10===2&&w%11!==c11)continue;
  if(w%12===9&&w%13!==12)continue;
  const wa=weightAll[w],w19=weightWithout19[w];baseTotal+=wa;
  if(w%3!==1){if(T1_NONCYL[j%3].includes(w%42))t1Non+=wa;}
  else t1CylByJmod3[j%3]+=wa;
  if(w%10===2)t2Cylinder+=wa;
  else if(w%11===mod(ALPHA11[w%10]-j,11))t2Resolved+=wa;
  if(w%18===3)t3Cylinder+=w19;else t3Resolved+=w19;
  const h7=mod(powMod(2,w+2,7)*(Y7[j%3]-w-1)-1,7);
  if(w%4!==0&&w%3!==1&&w%5===4&&h7===0)t4Resolved+=wa;
  else if(w%4===0&&w%3!==1&&h7===0)t4P5+=wa;
  else if(w%4!==0&&w%3===1&&w%5===4)t4P7+=wa;
  else if(w%4===0&&w%3===1)t4Both+=wa;
 }
}
if(baseTotal!==EXPECTED_PER_J*33n)throw new Error("Mismatch with Agent20's published first-level count");
const t1Numerator=49n*t1Non+2n*(t1CylByJmod3[0]+t1CylByJmod3[1]);
const t1Denominator=49n*baseTotal;
console.log(JSON.stringify({
 baseCandidateCountOverJmod33:String(baseTotal),
 t1:{numerator:String(t1Numerator),denominator:String(t1Denominator),share:pct(t1Numerator,t1Denominator)},
 t2:{resolvedOutside11Cylinder:String(t2Resolved),unresolved11Cylinder:String(t2Cylinder),resolvedShare:pct(t2Resolved,baseTotal),upperShare:pct(t2Resolved+t2Cylinder,baseTotal)},
 t3:{resolvedOutside19Cylinder:String(t3Resolved),unresolved19Cylinder:String(t3Cylinder),resolvedShare:pct(t3Resolved,baseTotal),upperShare:pct(t3Resolved+t3Cylinder,baseTotal)},
 t4:{resolvedOutsideBothCylinders:String(t4Resolved),unresolved5Only:String(t4P5),unresolved7Only:String(t4P7),unresolvedBoth:String(t4Both),resolvedShare:pct(t4Resolved,baseTotal),upperShare:pct(t4Resolved+t4P5+t4P7+t4Both,baseTotal)}
},null,2));
