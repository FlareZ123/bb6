// Deterministic candidate discovery on a single sibling's open exact tables.
// The returned DFA arrays are independently checked, not assumed correct.
function makeSolver(source,lagSource){
 source=source.replace("function solve(",lagSource+"\nfunction solve(").replaceAll("blockDfa(left)","left.lag?lagDfa(left):blockDfa(left)").replaceAll("blockDfa(right)","right.lag?lagDfa(right):blockDfa(right)");
 return new Function(source)();
}
function search(m,solver,raws){
 const params=[...solver.presets];
 for(const k of [8,12,16,24])for(const periods of [[1],[1,2],[1,2,3],[1,2,3,4]])for(const c of [1,2,3])for(const mm of [1,2,3])params.push({k,periods,c,m:mm});
 for(const lag of [2,3,4,5,6])for(const k of [2,3,4])for(const mm of [2,3,4,6])params.push({lag,k,c0:1,c1:1,m0:mm,m1:mm});
 let certs=[],unresolved=[],last=[];
 for(const raw of raws){
  const p=m.parse(raw),tape=new Set();let h=0,q=0,n=0;
  for(;n<200000;n++){let slot=2*q+Number(tape.has(h)),x=p[slot];if(x<0){last.push({table:raw,n,slot,holes:p.filter(v=>v<0).length});break}
   if(x>=12)tape.add(h);else tape.delete(h);h+=x%12>=6?1:-1;q=x%6}
  if(n<200000)continue;
  let found=false;
  for(const pp of params){const out=solver.solve(raw,pp,pp,10000);if(out.status==="ok"){certs.push({table:raw,...out});found=true;break}}
  if(!found)unresolved.push(raw)
 }
 return {certs,unresolved,last};
}
return {makeSolver,search};
