'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {scan}=require('../agent5-weighted-tnf-queue/scan-q0-coarse-full.cjs');
const {search,solve}=require('../agent5-weighted-tnf-queue/q0-open-automata.cjs');
const route=require('../agent47-raw11-adapter/raw11-route.json');
const id=29,table='1RB0LB_1RC1LC_0LA0RD_------_------_------';
const witnesses=new Map([
 ['1RB0LB1RC1LC0LA0RD0RE1RD1RF---1LA1LF',[4,'run',true,1,3,34,17,79]],
 ['1RB0LB1RC1LC0LA0RD0RE1LF1RF---0LD1RA',[11,'ngram',false,1,1,67,40,417]],
 ['1RB0LB1RC1LC0LA0RD1LE0RE1LB1RF---1LB',[6,'run',true,2,3,49,23,142]],
 ['1RB0LB1RC1LC0LA0RD1RE0LA1RF---1LA0RA',[2,'lag3',false,1,1,10,14,51]],
 ['1RB0LB1RC1LC0LA0RD1RE0RA1RF---1LA0RA',[2,'lag3',false,1,1,11,14,46]],
]);
assert.equal(route.extra[id],table);
const used=new Set();
const searchPeriodic=t=>{
 const w=witnesses.get(t);if(!w)return null;
 const [k,kind,mirror,cap,depth,nl,nr,rows]=w;
 const c=solve(t,k,kind,mirror,100000,cap,depth);
 assert.ok(c,t);assert.deepEqual([c.left.push.length,c.right.push.length,c.rows.length],[nl,nr,rows]);used.add(t);return c;
};
const result=scan(table,{search,searchPeriodic,known:new Map(),cap:2000000,ms:Infinity});
assert.equal(used.size,5);
const {tree,...summary}=result;
assert.deepEqual(summary.stats,{nodes:186373,side:137896,auto:2411,far:1882,split:7767,last:36417,pump:0,open:0,cap:0,bound:886});
assert.equal(summary.opens.length,0);assert.equal(summary.pending.length,0);
const out=process.argv[2];assert.ok(out,'output directory required');fs.mkdirSync(out,{recursive:true});
fs.writeFileSync(path.join(out,'summary.json'),JSON.stringify({...summary,id,table},null,2)+'\n');
fs.writeFileSync(path.join(out,'tree.json'),JSON.stringify(tree));
console.log(JSON.stringify({id,table,stats:summary.stats}));
