/* RETRACTED for exact S-window proof use. This script uses the superseded max(34*ell+140,36*ell+88) envelope and is not source-faithful. See ../agent48-623-tight-window/s_window_boundary_phases.js and SWindowPostResetSynchronization.md. */
#!/usr/bin/env node
"use strict";
const fs=require("node:fs");
const path=require("node:path");
const reset=JSON.parse(fs.readFileSync(path.join(__dirname,"../agent32-623-phase-automaton/ResetPatternDFA.json"),"utf8"));
const sub=JSON.parse(fs.readFileSync(path.join(__dirname,"PairCarrySynchronizingSubsetDFA.json"),"utf8"));
const pair=JSON.parse(fs.readFileSync(path.join(__dirname,"../agent49-parity623/PostResetCarryPairClosure.json"),"utf8"));
const scc=JSON.parse(fs.readFileSync(path.join(__dirname,"NonSynchronizingSCCs.json"),"utf8"));
const accepting=new Set(reset.accepting_states);
const component=new Map();
for(const c of scc.scc_partition.recurrent_nonsingleton_components_detail)for(const id of c.state_ids)component.set(id,c.label);
function evalA(a,k,m){for(;;){const q=k/3n,r=k%3n;if(r===2n)return [true,a+1n,q,m];if(a===0n){if(r===0n)return [false];return [true,0n,q,m];}if(r===0n)return [true,a-1n,q,m+2n];a-=1n;m+=2n*q+3n;k=q;}}
function drainB(a,b,d){while(b>0n){const old=b,z=evalA(a,b-1n,d+2n*b+3n);if(!z[0])return null;[a,b,d]=[z[1],z[2],z[3]];if(b>=old)return null;}return [a,d];}
function next(a,d){if(a===0n)return d%2n===1n?drainB(d+1n,2n,2n):[d,7n];if(d%2n===1n&&a>=d+5n)return drainB(a-d-5n,d+3n,5n);if(d%2n===0n&&a>=d+3n)return drainB(a-d-2n,d+2n,2n);if(a%2n===1n)return null;if(a===d+2n)return drainB(0n,a,2n);if(d%2n===1n)return drainB(d+4n-a,a-1n,3n);const z=evalA(d+1n-a,a,2n*a+5n);return z[0]?drainB(z[1],z[2],z[3]):null;}
function stateOf(a,d){let q,p,sector;if(a>=d){q=d;p=a-d;sector=d%2n===1n?"LO":"LE";}else{q=a;p=d-a;sector=d%2n===1n?"RO":"RE";}const gamma={LO:18n,LE:10n,RO:2n,RE:4n}[sector];return {a,d,q,S:a+d,g:p-3n*q,sector,x:2n*(p-3n*q)-gamma,y:6n*q};}
function ellOf(v){let e=0,p=1n;while((p-1n)/2n<v+3n){e++;p*=3n;}return e;}
function floorDiv(a,b){let q=a/b,r=a%b;if(r!==0n&&a<0n)q-=1n;return q;}
function mod(a,b){let r=a%b;return r<0n?r+b:r;}
function pow3(k){return 3n**BigInt(k);}
function digitAt(x,i){return Number(mod(floorDiv(x,pow3(i)),3n));}
function windowOf(s){const ell=ellOf(s.S),B=Math.max(34*ell+140,36*ell+88);let k=0,p=1;while(p<=B){p*=3;k++;}let j=0,z=1n,target=BigInt(B)**3n;while(z<=target){z*=3n;j++;}return {k,j};}
function scanWindow(s,w){let q=reset.initial_state,firstEnd=null;const word=[];for(let i=w.k+2;i<w.j-2;i++){const a=digitAt(s.x,i)*3+digitAt(s.y,i);word.push(a);q=reset.transitions[q][a];if(firstEnd===null&&accepting.has(q))firstEnd=word.length;}if(firstEnd===null)throw new Error("no common reset");let id=sub.initial_state,firstSync=null;for(let i=firstEnd;i<word.length;i++){id=sub.image_subset_transitions[id][word[i]];if(firstSync===null&&sub.image_subset_states[id].length===1)firstSync=i-firstEnd+1;}const ps=sub.image_subset_states[id].map(q=>pair.states[q]);const L=new Set(ps.map(x=>x.L_state)).size,R=new Set(ps.map(x=>x.R_state)).size;const branch=s.g>0n?"L":"R";return {word,firstEnd,suffixLength:word.length-firstEnd,id,rank:sub.image_subset_states[id].length,firstSync,L,R,branch,active:branch==="L"?L:R};}
const states=[];let a=0n,d=7n;for(let n=0;n<=10001;n++){states.push(stateOf(a,d));if(n<10001){const z=next(a,d);if(!z)throw new Error("root recurrence stopped at D"+n);[a,d]=z;}}
const rows=[],rankHist={},resetHist={},componentHist={},depthHist={},hard=[];let last=-1,postCount=0,postFail=0,activeSingleton=0,bothAmbig=0;
for(let n=34;n<=10001;n++){const s=states[n],w=windowOf(s),r=scanWindow(s,w);rankHist[r.rank]=(rankHist[r.rank]||0)+1;resetHist[r.firstEnd]=(resetHist[r.firstEnd]||0)+1;if(r.rank>1){last=n;const c=component.get(r.id)||"transient";componentHist[c]=(componentHist[c]||0)+1;if(r.active===1)activeSingleton++;if(r.L>1&&r.R>1)bothAmbig++;rows.push({index:n,subset_state:r.id,rank:r.rank,component:c,branch:r.branch,L_projection:r.L,R_projection:r.R,active_branch_projection:r.active,first_reset_end:r.firstEnd,postreset_suffix_length:r.suffixLength});}else if(n>=5581){postCount++;if(r.firstSync===null)postFail++;else depthHist[r.firstSync]=(depthHist[r.firstSync]||0)+1;if(r.firstSync>=9&&hard.length<20)hard.push({index:n,first_sync_depth:r.firstSync,suffix_symbol_ids:r.word.slice(r.firstEnd)});}}
const result={schema:"bb6-conservative-s-window-residual-map/v1",status:"finite computational diagnostic; not an all-time invariant or BB(6) proof",root_orbit:{initial_state:"D(0,7)",scanned_window_states:["D(34)","D(10001)"],window_count:9968},window_definition:{ell:"least ell with (3^ell-1)/2 >= S+3",buffer:"B=max(34*ell+140,36*ell+88)",k:"least with 3^k>B",j:"least with 3^j>B^3",digit_positions:"k+2 through j-3 inclusive",symbol_encoding:"3*x_digit+y_digit"},reset_first_end_histogram:resetHist,postreset_subset_rank_histogram:rankHist,nonsynchronizing_windows:{count:rows.length,last_index:last,indices:rows.map(x=>x.index),component_histogram:componentHist,active_branch_projection_singleton:activeSingleton,active_branch_projection_ambiguous:rows.length-activeSingleton,both_branch_projections_ambiguous:bothAmbig,rows},eventual_finite_run:{start_index:5581,count:postCount,rank_one_failures:postFail,first_sync_depth_histogram:depthHist,max_first_sync_depth:Math.max(...Object.keys(depthHist).map(Number)),hard_cases:hard}};
if(rows.length!==81||last!==5580||postCount!==4421||postFail!==0||result.eventual_finite_run.max_first_sync_depth!==11)throw new Error("unexpected scan totals");
fs.writeFileSync(path.join(__dirname,"ConservativeSWindowResidualMap.json"),JSON.stringify(result,null,2)+"\n");
console.log(JSON.stringify({window_count:9968,rank_histogram:rankHist,non_sync:rows.length,last_non_sync:last,component_histogram:componentHist,post5581_count:postCount,post5581_sync_failures:postFail,max_sync_depth:result.eventual_finite_run.max_first_sync_depth,hard_cases:hard},null,2));
