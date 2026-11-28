// One eight-hole D1 sibling per process; output is candidate data, never a proof verdict.
const fs=require("fs"),path=require("path"),D=__dirname;
const read=f=>fs.readFileSync(path.join(D,f),"utf8");
const m=new Function(read("scanCoupled8.js"))(),s=new Function(read("searchCoupled5.js"))();
const bank=read("frontier-dfa-bank.txt").trim().split(/\s+/).map(x=>[...x].map(Number));
const lag=JSON.parse(read("replayCoupled4BiDFA.js").match(/const lagSource=(.*);/)[1]);
const solver=s.makeSolver(read("../agent25-raw43/discover_abstract.js"),lag);
const [mv,dir]=process.argv.slice(2);
if(!/^[01][LR][A-E]$/.test(mv)||mv==="0LA"||!dir)throw Error("invalid argument");
const i=12*Number(mv[0])+6*Number(mv[1]==="R")+mv.charCodeAt(2)-65;
const start=Date.now(),z=m.scan(i,bank);
delete z.tree;
const result={...z,...s.search(m,solver,z.open)};
fs.mkdirSync(dir,{recursive:true});
fs.writeFileSync(path.join(dir,"coupled8-"+mv+".json"),JSON.stringify(result)+"\n");
console.log(mv,JSON.stringify({counts:z.counts,mass:z.mass,certs:result.certs.length,
  unresolved:result.unresolved,last:result.last,ms:Date.now()-start}));
