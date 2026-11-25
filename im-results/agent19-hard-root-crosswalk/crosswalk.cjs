// Reproduce the pinned hard-root crosswalk, without enumerating completions.
const fs = require("node:fs");
const path = require("node:path");
const roots = {
  "champion": "1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE",
  "C": "1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC",
  "P1": "1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE",
  "Sheep": "1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE",
  "D0": "1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---",
  "D1": "1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA",
  "D2": "1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---",
  "D3": "1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---",
  "A6": "1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---",
  "r1": "1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF",
  "r2": "1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA",
  "r3": "1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA",
  "r4": "1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---",
  "r5": "1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD",
  "r6": "1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF"
};
function compute(manifest, roots) {
 const letters="ABCDEF", removed=new Set([66,70,80,86,87,88,91,92,93,97,98,100,101,102,104,68,72,82,114]);
 function assert(b,msg){if(!b)throw Error(msg);}
 function canonical(e){let cut=2;for(const {move} of e.address){const d=letters.indexOf(move[2]);if(d>cut)return false;cut=Math.max(cut,d+1);}return true;}
 function perms(s){return s.length===0?[""]:[...s].flatMap((x,i)=>perms(s.slice(0,i)+s.slice(i+1)).map(t=>x+t));}
 function rename(t,p){const out=Array(12);for(let q=0;q<6;q++)for(let b=0;b<2;b++){const m=t[2*q+b];out[2*letters.indexOf(p[q])+b]=m==="H"?m:m.slice(0,2)+p[letters.indexOf(m[2])];}return out;}
 const canon=manifest.entries.filter(canonical), kept=canon.filter(e=>!removed.has(e.raw_residual_index));
 assert(manifest.entries.length===124&&canon.length===96&&kept.length===77,"roster counts");
 const records=[];
 for(const [name,table] of Object.entries(roots)){
  const t=table.replaceAll("_","").match(/.{3}/g).map(m=>m==="---"||m[2]==="Z"?"H":m);
  assert(t.length===12&&t.filter(m=>m==="H").length===1&&t[0]==="1RB","root table");
  let q=0,h=0,steps=0,cut=1;const tape=new Set(),seen=new Set(),path=[];
  while(seen.size<11&&steps<1000000){const b=Number(tape.has(h)),i=2*q+b,m=t[i];assert(m!=="H","early halt");if(!seen.has(i)){seen.add(i);const next=letters.indexOf(m[2]);assert(next<=cut,"not first-use canonical");cut=Math.max(cut,next+1);path.push({t:steps,slot:letters[q]+b,move:m});}if(m[0]==="1")tape.add(h);else tape.delete(h);h+=m[1]==="R"?1:-1;q=letters.indexOf(m[2]);steps++;}
  assert(seen.size===11&&cut===6,"incomplete prefix");
  const matches=[];
  for(const p of perms("CDEF").map(s=>"AB"+s)){const u=rename(t,p);for(const e of manifest.entries){if(e.table.every((m,i)=>m===null||m===u[i]))matches.push({raw:e.raw_residual_index,index:e.canonical_index,permutation:p,canonical:canonical(e),retained:canonical(e)&&!removed.has(e.raw_residual_index)});}}
  const retained=[...new Set(matches.filter(m=>m.retained).map(m=>m.raw))];assert(retained.length===1,"not unique retained cylinder");
  const parent=kept.find(e=>e.raw_residual_index===retained[0]);assert(parent.table.every((m,i)=>m===null||m===t[i]),"identity not compatible");
  const delays=[];
  for(let s=0;s<6;s++){let v=s,d=0;const visited=new Set();while(v!==0&&!visited.has(v)){visited.add(v);const m=t[2*v];if(m==="H"||m[0]!=="0")break;v=letters.indexOf(m[2]);d++;}if(v===0)delays.push({start:letters[s],delay:d});}
  const hi=t.indexOf("H");records.push({name,table,haltSlot:letters[Math.floor(hi/2)]+(hi%2),parent:{raw:parent.raw_residual_index,index:parent.canonical_index,table:parent.table},path,matches,delays,maxDelay:Math.max(...delays.map(x=>x.delay))});
 }
 return {counts:[124,96,78,77],removed:[...removed],records};
}
const manifest = JSON.parse(fs.readFileSync(process.argv[2] || path.join(__dirname,"../agent13-roster-convergence/canonical-124.json"),"utf8"));
console.log(JSON.stringify(compute(manifest,roots),null,2));
