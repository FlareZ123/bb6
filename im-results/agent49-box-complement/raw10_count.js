const {generate}=require("./raw10_search.js");
const fs=require("node:fs");
const source=fs.readFileSync(__dirname+"/Raw10Encoded.lean","utf8");
const old=[...source.matchAll(/^\[([0-9,]+)\],?$/gm)].map(m=>m[1].split(",").map(Number)).slice(0,-1);
const {side,halt}=generate();
const hrows=halt.map(w=>w.rows.map((v,i)=>i===w.slot?25:v));
const perms=[[3,4,5],[3,5,4],[4,3,5],[4,5,3],[5,3,4],[5,4,3]].map(p=>[0,1,2,...p]);
function rename(row,p){const a=Array(12).fill(0);row.forEach((v,i)=>{a[2*p[i>>1]+i%2]=v>=1&&v<=24?4*p[Math.floor((v-1)/4)]+(v-1)%4+1:v});return a}
function orbit(rows){return [...new Map(rows.flatMap(row=>perms.map(p=>rename(row,p))).map(row=>[row.join(","),row])).values()]}
function intersects(a,b){return a.every((x,i)=>x===0||b[i]===0||x===b[i])}
function mass(r){return 25n**BigInt(r.filter(v=>v===0).length)}
function disjointMass(rows){let total=0n;for(let i=0;i<rows.length;i++){for(let j=0;j<i;j++)if(intersects(rows[i],rows[j]))throw Error("overlap within a family");total+=mass(rows[i])}return total}
const a=orbit(old),b=orbit([...side.map(w=>w.rows),...hrows]);
const ma=disjointMass(a),mb=disjointMass(b);
let cross=0n,pairs=0;
for(const r of a)for(const s of b)if(intersects(r,s)){pairs++;cross+=mass(r.map((v,i)=>v||s[i]))}
console.log({old:a.length,shallow:b.length,oldMass:ma.toString(),shallowMass:mb.toString(),crossPairs:pairs,crossMass:cross.toString(),unionMass:(ma+mb-cross).toString(),remaining:(25n**10n-ma-mb+cross).toString()});
