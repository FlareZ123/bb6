// Replay exact selected parameter tuples, not the search portfolio.
// Usage: node im-results/agent46-raw13-cut/replayCoupled4BiDFA.js
const fs=require("fs"),path=require("path"),assert=require("assert"),cp=require("child_process");
const D=__dirname,bank=JSON.parse(fs.readFileSync(path.join(D,"coupled4-bidfa.json"),"utf8"));
const root=path.resolve(D,"../.."),file=path.join(root,bank.source.block_path);
const blob=cp.execFileSync("git",["hash-object",file],{encoding:"utf8"}).trim();
assert.equal(blob,bank.source.block_blob);
let source=fs.readFileSync(file,"utf8");
const lagSource="function lagDfa({lag,k,c0,c1,m0,m1}){const base=dfa([k,c0,c1,m0,m1]),mask=(1<<lag)-1,words=[[0,0]],ids=new Map([[\"0,0\",0]]),delta=[[-1,-1]];return {push:(x,b)=>{if(delta[x][b]>=0)return delta[x][b];let [w,a]=words[x];let v=[((w<<1)|b)&mask,base.push(a,b^(w>>(lag-1)))],key=v.join(\",\"),j=ids.get(key);if(j===undefined){j=words.length;ids.set(key,j);words.push(v);delta.push([-1,-1])}delta[x][b]=j;return j},finish:()=>delta.flat().map(x=>Math.max(0,x)),size:()=>words.length}}";
source=source.replace("function solve(",lagSource+"\nfunction solve(").replaceAll("blockDfa(left)","left.lag?lagDfa(left):blockDfa(left)").replaceAll("blockDfa(right)","right.lag?lagDfa(right):blockDfa(right)");
const m=new Function(source)();
for(const x of bank.records){const z=m.solve(x.table,...x.params,bank.source.cap);assert.equal(z.status,"ok");assert.deepEqual(z.dfa,x.dfa);assert.equal(z.states,x.states);assert.equal(z.edges,x.edges);console.log(x.table,x.states,x.edges)}
