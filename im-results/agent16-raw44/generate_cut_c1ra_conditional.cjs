#!/usr/bin/env node
// Conditional C1=1RA parent certification generated from the original
// finite source-checker. Exactly six F0/E0 one-hole cylinders are explicit
// universally quantified NeverHalts hypotheses. No sorry/axiom is inserted.
'use strict';
// Deterministic raw-first-hole 25-way source-witness emitter.
// Search output is untrusted; resulting Lean zipCheck/NGram check is kernel-checked.
const fs=require('fs'),path=require('path');
const out=process.argv[2]||path.join(__dirname,'generated');
const W=Number(process.argv[3]||128),short=120,long=1600,second='1RA',B=211;
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
const fixed0RF={
 '1RB0LF_1RC0RC_0RD0RF_1LD1LB_1LA---_1LE1LC':['BB6.Agent16Raw44M4RF.table','BB6.Agent16Raw44M4RF.never'],
 '1RB1LE_1RC0RC_0RD0RF_1LD1LB_---0LA_0LA1LF':['BB6.Agent16Raw44M5RF.table','BB6.Agent16Raw44M5RF.never'],
 '1RB1LE_1RC0RC_0RD0RF_1LD1LB_---0RF_0LA1LF':['BB6.Agent16Raw44M6RF.table','BB6.Agent16Raw44M6RF.never'],
 '1RB---_1RC0RC_0RD0RF_1LD1LB_0RD1RD_---0RE':['BB6.Agent16Raw44B1RC_C1RF.table','BB6.Agent16Raw44B1RC_C1RF.never']
};
const fixed1RA={
  '1RB1RE_1RC0RC_0RD1RA_1LD1LB_---0RF_0RC0RE':['BB6.Agent16Raw44B1RC_C1R_A1RE.table','BB6.Agent16Raw44B1RC_C1R_A1RE.never'],
  '1RB1RF_1RC0RC_0RD1RA_1LD1LB_0RC0RF_---0RE':['BB6.Agent16Raw44B1RC_C1R_A1RF.table','BB6.Agent16Raw44B1RC_C1R_A1RF.never'],
  '1RB0RE_1RC0RC_0RD1RA_1LD1LB_---0RF_0RD0RE':['BB6.Agent16Raw44B1RC_C1R_A1ZeroRE.table','BB6.Agent16Raw44B1RC_C1R_A1ZeroRE.never'],
  '1RB0RF_1RC0RC_0RD1RA_1LD1LB_0RD0RF_---0RE':['BB6.Agent16Raw44B1RC_C1R_A1ZeroRF.table','BB6.Agent16Raw44B1RC_C1R_A1ZeroRF.never'],
  '1RB0RE_1RC0RC_0RD1RA_1LD1LB_---0RF_0RC0RA':['BB6.Agent16Raw44C1RA_A1ZeroRE_F0RC.table','BB6.Agent16Raw44C1RA_A1ZeroRE_F0RC.never'],
  '1RB0RF_1RC0RC_0RD1RA_1LD1LB_0RC0RA_---0RE':['BB6.Agent16Raw44C1RA_A1ZeroRF_F0RC.table','BB6.Agent16Raw44C1RA_A1ZeroRF_F0RC.never'],
  '1RB1LE_1RC0RC_0RD1RA_1LD1LB_0LF0LA_---0LE':['BB6.Agent16Raw44Cut.hard0','h0'],
  '1RB1LF_1RC0RC_0RD1RA_1LD1LB_---0LF_0LE0LA':['BB6.Agent16Raw44Cut.hard1','h1'],
  '1RB1LE_1RC0RC_0RD1RA_1LD1LB_1LF0LA_---1LC':['BB6.Agent16Raw44Cut.hard2','h2'],
  '1RB1LF_1RC0RC_0RD1RA_1LD1LB_---1LC_1LE0LA':['BB6.Agent16Raw44Cut.hard3','h3'],
  '1RB1LE_1RC0RC_0RD1RA_1LD1LB_1LF0LA_---1LE':['BB6.Agent16Raw44Cut.hard4','h4'],
  '1RB1LF_1RC0RC_0RD1RA_1LD1LB_---1LF_1LE0LA':['BB6.Agent16Raw44Cut.hard5','h5']
};
const hardKeys=Object.keys(fixed1RA).filter(k => /^h[0-5]$/.test(fixed1RA[k][1]));
const hardDefs=hardKeys.map((t,i) => tableDecl('hard'+i,t.replaceAll('_','').match(/.../g).map(enc))).join('\n');
if(hardKeys.length!==6 || hardKeys.some((t,i)=>fixed1RA[t][1]!=='h'+i))
  throw Error('Conditional hard-key ordering mismatch');
const fixed0RA={
  '1RB0LE_1RC0RC_0RD0RA_1LD1LB_0LF---_1LA1LB':['BB6.Agent16Raw44M1.table','BB6.Agent16Raw44M1.never'],
  '1RB1RE_1RC0RC_0RD0RA_1LD1LB_---0RF_0RC0RE':['BB6.Agent16Raw44M2.table','BB6.Agent16Raw44M2.never'],
  '1RB0LF_1RC0RC_0RD0RA_1LD1LB_1LA1LB_0LE---':['BB6.Agent16Raw44M1Swap.table','BB6.Agent16Raw44M1Swap.never'],
  '1RB1RF_1RC0RC_0RD0RA_1LD1LB_0RC0RF_---0RE':['BB6.Agent16Raw44M2Swap.table','BB6.Agent16Raw44M2Swap.never']
};
function slot(j){return `(${j>>1}, ${Boolean(j&1)})`}
function move(m){return `⟨${Boolean(m&1)},${Boolean(m&2)},${m>>2}⟩`}
const imports="import Raw44CutBase\nimport Raw44B1RC_C1R_A1RE_Growth\nimport Raw44B1RC_C1R_A1RF_Symmetry\nimport Raw44B1RC_C1R_A1ZeroRE_Growth\nimport Raw44B1RC_C1R_A1ZeroRF_Symmetry\nimport Raw44B1RC_C1RA_A1ZeroRE_F0RC_Growth\nimport Raw44B1RC_C1RA_A1ZeroRF_F0RC_Symmetry\n";
const root=run(ps,short,64);if(root.kind!=='hole')throw Error('No root hole: '+JSON.stringify(root));
const first=root.j;
fs.writeFileSync(path.join(out,'Raw44CutBase.lean'),`import ZipThreeHoleAudit\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent16Raw44Cut\nopen BB6Coverage BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent13BlankDelay\n${tableDecl('parent',ps)}theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide\ntheorem parent_nohalt : weightedTNFNoAssignedHalt parent := by\n  intro slot\n  rcases slot with ⟨q,b⟩\n  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega\n  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide\n${hardDefs}\nend BB6.Agent16Raw44Cut\n`);
const hs="(h0 : ∀ m : Machine, compatible hard0 m → NeverHalts m) (h1 : ∀ m : Machine, compatible hard1 m → NeverHalts m) (h2 : ∀ m : Machine, compatible hard2 m → NeverHalts m) (h3 : ∀ m : Machine, compatible hard3 m → NeverHalts m) (h4 : ∀ m : Machine, compatible hard4 m → NeverHalts m) (h5 : ∀ m : Machine, compatible hard5 m → NeverHalts m)",has="h0 h1 h2 h3 h4 h5";
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
    for(let k=1;k<=10;k++){
      const ng=ngram(ps,k);
      if(ng.ok){const i=ngCases.length;ngCases.push({i,p:[...ps],ng});mass.ngram++;
        return `.proven BB6.Agent16Raw44Cut.NG${String(ix).padStart(2,'0')}.p${i} BB6.Agent16Raw44Cut.NG${String(ix).padStart(2,'0')}.never${i}`}
      if(ng.over)break;
    }
    const pkey=tab(ps);if(!(pkey in fixed1RA))throw Error('Unexpected hard leaf: '+pkey);
    const a=fixed1RA[pkey];mass.hard++;hardCount++;return `.proven ${a[0]} ${a[1]}`;
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
  const kid=`${imports}import Raw44CutNG${tag}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent16Raw44Cut\nopen BB6Coverage BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent13BlankDelay\ndef kid${tag} ${hs} : Audit :=\n${tree}\ntheorem kid${tag}_checked ${hs} : zipCheck ${B} (refine parent ${slot(first)} (some ${move(m)})) (kid${tag} ${has}) = true := by decide +kernel +revert\n#print axioms kid${tag}_checked\nend BB6.Agent16Raw44Cut\n`;
  fs.writeFileSync(path.join(out,`Raw44CutKid${tag}.lean`),kid);
  children.push(tag);stats.push({ix,ng:ngCases.length,hard:hardCount,size:kid.length,ngSize:ngText.length});
}
const proofOrder=Array.from({length:6},(_,q)=>[q,q+6,q+12,q+18]).flat().map(x=>String(x).padStart(2,'0'));
const assembled=`import Raw44CutBase\n${children.map(i=>`import Raw44CutKid${i}`).join('\n')}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent16Raw44Cut\nopen BB6Coverage BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent13BlankDelay\ndef kids ${hs} : Move → Audit := byMove [${children.map(i=>`kid${i} ${has}`).join(',')}]\ndef tree ${hs} : Audit := .split ${root.n} ${slot(first)} (kids ${has})\ntheorem kids_checked ${hs} (mv : Move) :\n  zipCheck ${B} (refine parent ${slot(first)} (some mv)) ((kids ${has}) mv) = true := by\n  rcases mv with ⟨w,r,q⟩\n  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega\n  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl\n  all_goals cases w <;> cases r\n${proofOrder.map(i=>`  · exact kid${i}_checked ${has}`).join('\n')}\ntheorem checked ${hs} : zipCheck ${B} parent (tree ${has}) = true := by\n  change (zipQueryOK ${B} parent ${root.n} ${slot(first)} && allMoves (fun mv => zipCheck ${B} (refine parent ${slot(first)} (some mv)) ((kids ${has}) mv))) = true\n  simp only [Bool.and_eq_true]\n  exact ⟨by decide, allMoves_of _ (kids_checked ${has})⟩\nnoncomputable def certified ${hs} : WeightedTNFCertificate ${B} parent 6 :=\n  certifiedZip ${B} parent (tree ${has}) parent_root parent_nohalt (checked ${has})\ntheorem weighted_bound ${hs} (m : Machine) (hm : compatible parent m) : WeightedBound ${B} m :=\n  (certified ${has}).sound m hm\n#print axioms checked\n#print axioms weighted_bound\nend BB6.Agent16Raw44Cut\n`;
fs.writeFileSync(path.join(out,'Raw44CutAssembled.lean'),assembled);
console.log(JSON.stringify({out,root,nodes,splits,queries,mass,stats},null,2));
