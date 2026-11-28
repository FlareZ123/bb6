#!/usr/bin/env node
'use strict';
// Deterministic raw-first-hole 25-way source-witness emitter.
// Search output is untrusted; resulting Lean zipCheck/NGram check is kernel-checked.
const fs=require('fs'),path=require('path');
const out=process.argv[2]||path.join(__dirname,'generated');
const W=Number(process.argv[3]||128),short=120,long=1600,second=process.argv[4]||'0RE',B=second==='0LA'?126:second==='0RA'?375:211;
fs.mkdirSync(out,{recursive:true});
const base=['1RB',null,'1RC','0RC','0RD',second,'1LD','1LB',null,null,null,null];
const enc=s=>s===null||s==='---'?-1:(s.charCodeAt(2)-65)*4+(s[1]==='R'?2:0)+Number(s[0]);
const fmt=v=>v<0?'---':`${v&1}${v&2?'R':'L'}${String.fromCharCode(65+(v>>2))}`;
const tab=p=>Array.from({length:6},(_,i)=>fmt(p[2*i])+fmt(p[2*i+1])).join('_');
const ps=base.map(enc),mass={last:0,cycle:0,ngram:0,hard:0};let nodes=0,queries=0,splits=0;
function run(p,T,W){let q=0,l=0n,r=0n,h=0,his=[];
  for(let t=0;t<=T;t++){
    let lo=h,hi=h;
    for(let i=his.length-1;i>=0&&i>=his.length-W;i--){
      const s=his[i];lo=Math.min(lo,s.h);hi=Math.max(hi,s.h);
      if(s.q!==q)continue;
      const d=h-s.h;
      if(d>=0&&r===s.r&&((l^s.l)&((1n<<BigInt(s.h-lo))-1n))===0n)
        return {kind:'cycle',entry:i,period:t-i,right:true,boundary:lo};
      if(d<=0&&l===s.l&&((r^s.r)&((1n<<BigInt(hi-s.h+1))-1n))===0n)
        return {kind:'cycle',entry:i,period:t-i,right:false,boundary:hi};
    }
    const j=q*2+Number(r&1n),m=p[j];
    if(m<0)return {kind:'hole',n:t,j};
    if(t===T)return {kind:'open'};
    his.push({q,l,r,h});
    const w=BigInt(m&1);
    if(m&2){l=(l<<1n)|w;r>>=1n;h++}
    else{r=((r>>1n)<<2n)|(w<<1n)|(l&1n);l>>=1n;h--}
    q=m>>2;
  }
}
function ngram(p,k,limit=200000){
  const K=2**k,M=K-1,H=K>>1;
  const edges=[new Uint8Array(K),new Uint8Array(K)];
  const waiting=[Array.from({length:K},()=>[]),Array.from({length:K},()=>[])];
  const seen=new Set(),todo=[];let fail=false,over=false;
  function add(s,l,r){let id=(s*K+l)*K+r;if(seen.has(id))return;seen.add(id);todo.push(id);if(p[s]<0)fail=true;if(todo.length>limit)over=true}
  function pop(id,e){let r=id%K,z=Math.floor(id/K),l=z%K,s=Math.floor(z/K),m=p[s],q=m>>2,w=m&1;
    if(m&2)add(2*q+(r&1),((l<<1)|w)&M,(r>>1)|(e*H));
    else add(2*q+(l&1),(l>>1)|(e*H),((r<<1)|w)&M)}
  function edge(d,x,e){if(edges[d][x]&(1<<e))return;edges[d][x]|=1<<e;
    for(const id of waiting[d][x]){pop(id,e);if(fail||over)break}}
  edges[0][0]=edges[1][0]=1;add(0,0,0);
  for(let i=0;i<todo.length&&!fail&&!over;i++){
    const id=todo[i],r=id%K,z=Math.floor(id/K),l=z%K,s=Math.floor(z/K),m=p[s],w=m&1;
    const R=Boolean(m&2),push=R?l:r,popx=R?r:l,d=R?1:0;
    edge(1-d,((push<<1)|w)&M,push>>(k-1));if(fail||over)break;
    waiting[d][popx].push(id);
    for(let e=0;e<2;e++)if(edges[d][popx]&(1<<e))pop(id,e);
  }
  return {ok:!fail&&!over,over,k,states:todo.length,edges,ids:todo};
}
function trie(xs){if(!xs.length)return '.empty';if(xs.length===1&&xs[0]===0)return '.leaf';
  return '(.branch '+trie(xs.filter(x=>!(x&1)).map(x=>x/2))+' '+trie(xs.filter(x=>x&1).map(x=>Math.floor(x/2)))+')'}
function natMask(edges){let n=0n;for(let i=0;i<edges.length;i++)n|=BigInt(edges[i])<<BigInt(2*i);return '0x'+n.toString(16)}
function tableDecl(name,p){return `def ${name} : PartialMachine := fun s => match s with\n`+
  p.map((m,j)=>`  | (${j>>1}, ${Boolean(j&1)}) => `+(m<0?'none':`some (some ⟨${Boolean(m&1)},${Boolean(m&2)},${m>>2}⟩)`)).join('\n')+'\n  | _ => none\n'}
const fixed={
  '1RB0LE_1RC0RC_0RD0RE_1LD1LB_1LF1LC_1LA---':['BB6.Agent16Raw44M4.table','BB6.Agent16Raw44M4.never'],
  '1RB1LF_1RC0RC_0RD0RE_1LD1LB_0LA1LE_---0LA':['BB6.Agent16Raw44M5.table','BB6.Agent16Raw44M5.never'],
  '1RB1LF_1RC0RC_0RD0RE_1LD1LB_0LA1LE_---0RE':['BB6.Agent16Raw44M6.table','BB6.Agent16Raw44M6.never'],
  '1RB---_1RC0RC_0RD0RE_1LD1LB_---0RF_0RD1RD':['BB6.Agent16Raw44B1RC_C1RE.table','BB6.Agent16Raw44B1RC_C1RE.never']
};
const fixed0LA={
  '1RB1LE_1RC0RC_0RD0LA_1LD1LB_0RB0LF_1RA---':['BB6.Agent16Raw44M3.table','BB6.Agent16Raw44M3.never'],
  '1RB1LF_1RC0RC_0RD0LA_1LD1LB_1RA---_0RB0LE':['BB6.Agent16Raw44M3Swap.table','BB6.Agent16Raw44M3Swap.never']
};
const fixed0RA={
  '1RB0LE_1RC0RC_0RD0RA_1LD1LB_0LF---_1LA1LB':['BB6.Agent16Raw44M1.table','BB6.Agent16Raw44M1.never'],
  '1RB1RE_1RC0RC_0RD0RA_1LD1LB_---0RF_0RC0RE':['BB6.Agent16Raw44M2.table','BB6.Agent16Raw44M2.never'],
  '1RB0LF_1RC0RC_0RD0RA_1LD1LB_1LA1LB_0LE---':['BB6.Agent16Raw44M1Swap.table','BB6.Agent16Raw44M1Swap.never'],
  '1RB1RF_1RC0RC_0RD0RA_1LD1LB_0RC0RF_---0RE':['BB6.Agent16Raw44M2Swap.table','BB6.Agent16Raw44M2Swap.never']
};
function slot(j){return `(${j>>1}, ${Boolean(j&1)})`}
function move(m){return `⟨${Boolean(m&1)},${Boolean(m&2)},${m>>2}⟩`}
const imports=second==='0RA'?'import Raw44CutBase\nimport Raw44B1RC_C1RA_M1Growth\nimport Raw44B1RC_C1RA_M1SwapGrowth\nimport Raw44B1RC_C1RA_M2Growth\nimport Raw44B1RC_C1RA_M2SwapGrowth\n':second==='0LA'?'import Raw44CutBase\nimport Raw44B1RC_C1LA_M3Growth\nimport Raw44B1RC_C1LA_M3SwapGrowth\n':'import Raw44CutBase\nimport Raw44B1RC_C1RE_M4Growth\nimport Raw44B1RC_C1RE_M5Growth\nimport Raw44B1RC_C1RE_M6Growth\nimport Raw44B1RC_C1RE_TwoHoleGrowth\n';
const root=run(ps,short,64);if(root.kind!=='hole')throw Error('No root hole: '+JSON.stringify(root));
const first=root.j;
fs.writeFileSync(path.join(out,'Raw44CutBase.lean'),`import ZipThreeHoleAudit\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent16Raw44Cut\nopen BB6Coverage BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent13BlankDelay\n${tableDecl('parent',ps)}theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide\ntheorem parent_nohalt : weightedTNFNoAssignedHalt parent := by\n  intro slot\n  rcases slot with ⟨q,b⟩\n  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega\n  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide\nend BB6.Agent16Raw44Cut\n`);
const children=[],stats=[];
for(let ix=0;ix<24;ix++){
  const m=(ix%6)*4+((Math.floor(ix/6)%2)*2)+Math.floor(ix/12);ps[first]=m;
  const ngCases=[];let hardCount=0;
  function visit(holes){nodes++;
    let z=run(ps,short,64);
    if(z.kind==='open')z=run(ps,long,W);
    if(z.kind==='hole'){
      queries++;
      if(holes===1){mass.last++;return `.last ${z.n} ${slot(z.j)}`}
      splits++;const kids=[];for(let j=0;j<24;j++){
        const a=(j%6)*4+((Math.floor(j/6)%2)*2)+Math.floor(j/12);
        ps[z.j]=a;kids.push(visit(holes-1));
      }ps[z.j]=-1;
      return `.split ${z.n} ${slot(z.j)} (byMove [\n${kids.join(',\n')}\n])`;
    }
    if(z.kind==='cycle'){mass.cycle++;return `.cycle ${z.entry} ${z.period} ${z.right} (${z.boundary})`}
    for(let k=1;k<=8;k++){
      const ng=ngram(ps,k);
      if(ng.ok){const i=ngCases.length;ngCases.push({i,p:[...ps],ng});mass.ngram++;
        return `.proven BB6.Agent16Raw44Cut.NG${String(ix).padStart(2,'0')}.p${i} BB6.Agent16Raw44Cut.NG${String(ix).padStart(2,'0')}.never${i}`}
      if(ng.over)break;
    }
    const pkey=tab(ps);if(!(pkey in (second==='0RA'?fixed0RA:second==='0LA'?fixed0LA:fixed)))throw Error('Unexpected hard leaf: '+pkey);
    const a=(second==='0RA'?fixed0RA:second==='0LA'?fixed0LA:fixed)[pkey];mass.hard++;hardCount++;return `.proven ${a[0]} ${a[1]}`;
  }
  const tree=visit(4);ps[first]=-1;
  const tag=String(ix).padStart(2,'0');
  let ngText=`import NGramCertificate\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace BB6.Agent16Raw44Cut.NG${tag}\nopen BB6Coverage BB6.Agent1NGram\n`;
  for(const {i,p,ng} of ngCases){
    let K=2**ng.k,rows=Array.from({length:12},()=>[]);
    for(const id of ng.ids){let row=Math.floor(id/(K*K));rows[row].push(id%(K*K))}
    ngText+=`\n${tableDecl('p'+i,p)}def c${i} : Cert := ⟨${ng.k-1}, ${natMask(ng.edges[0])}, ${natMask(ng.edges[1])}, #[${rows.map(trie).join(',')}]⟩\n`;
    ngText+=`theorem ok${i} : check p${i} c${i} = true := by decide +kernel\n`;
    ngText+=`theorem never${i} (m : Machine) (hm : compatible p${i} m) : NeverHalts m := never p${i} c${i} ok${i} m hm\n`;
  }
  ngText+=`end BB6.Agent16Raw44Cut.NG${tag}\n`;
  fs.writeFileSync(path.join(out,`Raw44CutNG${tag}.lean`),ngText);
  const kid=`${imports}import Raw44CutNG${tag}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent16Raw44Cut\nopen BB6Coverage BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent13BlankDelay\ndef kid${tag} : Audit :=\n${tree}\ntheorem kid${tag}_checked : zipCheck ${B} (refine parent ${slot(first)} (some ${move(m)})) kid${tag} = true := by decide +kernel\n#print axioms kid${tag}_checked\nend BB6.Agent16Raw44Cut\n`;
  fs.writeFileSync(path.join(out,`Raw44CutKid${tag}.lean`),kid);
  children.push(tag);stats.push({ix,ng:ngCases.length,hard:hardCount,size:kid.length,ngSize:ngText.length});
}
const proofOrder=Array.from({length:6},(_,q)=>[q,q+6,q+12,q+18]).flat().map(x=>String(x).padStart(2,'0'));
const assembled=`import Raw44CutBase\n${children.map(i=>`import Raw44CutKid${i}`).join('\n')}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent16Raw44Cut\nopen BB6Coverage BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent13BlankDelay\ndef kids : Move → Audit := byMove [${children.map(i=>`kid${i}`).join(',')}]\ndef tree : Audit := .split ${root.n} ${slot(first)} kids\ntheorem kids_checked (mv : Move) :\n  zipCheck ${B} (refine parent ${slot(first)} (some mv)) (kids mv) = true := by\n  rcases mv with ⟨w,r,q⟩\n  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega\n  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl\n  all_goals cases w <;> cases r\n${proofOrder.map(i=>`  · exact kid${i}_checked`).join('\n')}\ntheorem checked : zipCheck ${B} parent tree = true := by\n  change (zipQueryOK ${B} parent ${root.n} ${slot(first)} && allMoves (fun mv => zipCheck ${B} (refine parent ${slot(first)} (some mv)) (kids mv))) = true\n  simp only [Bool.and_eq_true]\n  exact ⟨by decide, allMoves_of _ kids_checked⟩\nnoncomputable def certified : WeightedTNFCertificate ${B} parent 6 :=\n  certifiedZip ${B} parent tree parent_root parent_nohalt checked\ntheorem weighted_bound (m : Machine) (hm : compatible parent m) : WeightedBound ${B} m :=\n  certified.sound m hm\n#print axioms checked\n#print axioms weighted_bound\nend BB6.Agent16Raw44Cut\n`;
fs.writeFileSync(path.join(out,'Raw44CutAssembled.lean'),assembled);
console.log(JSON.stringify({out,root,nodes,splits,queries,mass,stats},null,2));
