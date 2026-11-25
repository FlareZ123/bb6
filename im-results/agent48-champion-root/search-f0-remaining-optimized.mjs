#!/usr/bin/env node
"use strict";
// Optimized deeper side-cycle search for the six F/0 siblings not closed by
// the 100/200 and 200/400 searches. Uses incremental cycle replay.

const names="ABCDEF";
const p6=["1RB",null,"1RC",null,"1LD","0RF","1RA","0LE","0LD","1RC",null,"0RE"];
const f0=10, candidates=["0LB","0LC","1LC","1RD","0LE","0RE"];
function parseMove(x){return {w:+x[0],d:x[1],q:names.indexOf(x[2])};}
function clone(c){return {q:c.q,h:c.h,ones:new Set(c.ones)};}
function step(t,c){const s=2*c.q+(c.ones.has(c.h)?1:0),m=t[s];if(m===null)return false;const z=parseMove(m);if(z.w)c.ones.add(c.h);else c.ones.delete(c.h);c.h+=z.d==="R"?1:-1;c.q=z.q;return true;}
function same(a,b){if(a.q!==b.q||a.h!==b.h||a.ones.size!==b.ones.size)return false;for(const x of a.ones)if(!b.ones.has(x))return false;return true;}
function classify(t,cap){const a={q:0,h:0,ones:new Set()},tor=clone(a),hare=clone(a);if(!step(t,hare))return {kind:"hole"};let n=1,p=1,r=1;while(!same(tor,hare)&&n<cap){if(p===r){Object.assign(tor,clone(hare));p*=2;r=0;}if(!step(t,hare))return {kind:"hole"};n++;r++;}return same(tor,hare)?{kind:"lasso"}:{kind:"cap"};}
function findSide(t,entryCap,periodCap,radiusCap){
 const starts=[];let c={q:0,h:0,ones:new Set()};
 for(let e=0;e<=entryCap;e++){starts.push(clone(c));if(e<entryCap&&!step(t,c))break;}
 for(let e=0;e<starts.length;e++){
  const start=starts[e],hist=[clone(start)],c2=clone(start);
  for(let p=1;p<=periodCap;p++){
   if(!step(t,c2))break;
   hist.push(clone(c2));
   const end=c2,delta=end.h-start.h,right=delta>=0;
   if(end.q!==start.q||delta===0)continue;
   let minH=Infinity,maxH=-Infinity;
   for(let j=0;j<p;j++){minH=Math.min(minH,hist[j].h);maxH=Math.max(maxH,hist[j].h);}
   const radius=right?Math.max(0,start.h-minH):Math.max(0,maxH-start.h);
   if(radius>radiusCap)continue;
   const boundary=right?start.h-radius:start.h+radius;
   const onSide=x=>right?x>=boundary:x<=boundary;
   let ok=true;
   for(const x of start.ones)if(onSide(x)&&!end.ones.has(x+delta)){ok=false;break;}
   if(!ok)continue;
   for(const y of end.ones)if(onSide(y-delta)&&!start.ones.has(y-delta)){ok=false;break;}
   if(ok)return {entry:e,period:p,right,boundary,delta};
  }
 }
 return null;
}
const out=[];
for(const move of candidates){const t=p6.slice();t[f0]=move;out.push({move,cap5m:classify(t,5_000_000),witness:findSide(t,300,600,600)});}
console.log(JSON.stringify({cap:5_000_000,sideCycleBounds:{entry:300,period:600,radius:600},outcomes:out},null,2));
