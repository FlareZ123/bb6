// Reconstruct exact sparse stack relation and emit original-source kernel checks.
function closure(m,L,R){let dfa=[L,R],edges=dfa.map(x=>x.map(()=>[])),waiting=dfa.map(x=>x.map(()=>[]));edges[0][0].push([0,0]);edges[1][0].push([0,0]);let seen=new Set(["0,0,0,0"]),todo=[[0,0,0,0]];function add(q,a,l,r){if(!m[2*q+a])throw Error("halt");let key=[q,a,l,r].join(",");if(!seen.has(key)){seen.add(key);todo.push([q,a,l,r])}}function pop(st,b,i){let[q,a,l,r]=st,v=m[2*q+a]-1,w=v>>1&1,n=v>>2;if(v&1)add(n,b,L[l][w],i);else add(n,b,i,R[r][w])}for(let t=0;t<todo.length;t++){let st=todo[t],[q,a,l,r]=st,v=m[2*q+a]-1;if(v<0)throw Error("halt");let d=v&1?0:1,w=v>>1&1,old=d?r:l,x=d?l:r,j=dfa[d][old][w];if(!edges[d][j].some(([b,i])=>b===w&&i===old)){edges[d][j].push([w,old]);for(let st2 of waiting[d][j])pop(st2,w,old)}waiting[1-d][x].push(st);for(const[b,i] of edges[1-d][x])pop(st,b,i)}return {states:todo,edges}}
function emit(data){let out=`import TwoSidedAutomata\nimport Box17AuditCore\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent13.Box33D17V22RunSummary\nopen BB6Coverage BB6.Agent4Automata\nopen Box17 (index decode)\n`;
function trie(xs){if(!xs.length)return ".empty";if(xs.length===1&&xs[0]===0)return ".leaf";return `(.branch ${trie(xs.filter(x=>!(x%2)).map(x=>x>>1))} ${trie(xs.filter(x=>x%2).map(x=>x>>1))})`}
for(const[id,d] of Object.entries(data)){let {states,edges}=closure(d.machine,d.L,d.R);if(states.length!==d.count)throw Error("count");let ss=[d.L,d.R].map((D,s)=>{let E=edges[s].map(xs=>"["+xs.sort((a,b)=>a[0]-b[0]||a[1]-b[1]).map(([b,i])=>`(${!!b},${i})`).join(",")+"]");return `⟨#[${E.join(",")}],#[${D.map(([a,b])=>`(${a},${b})`).join(",")}]⟩`});let rows=Array.from({length:12},(_,i)=>trie(states.filter(([q,a])=>q*2+a===i).map(([q,a,l,r])=>r+d.R.length*l).sort((a,b)=>a-b)));
out+=`\nnamespace M${id}\ndef codes : List (Fin 25) := [${d.machine.join(",")}]\ndef partialTable : PartialMachine := fun s => some (decode (codes.getD (index s).val 0))\ndef cert : Cert := ⟨${ss.join(",")},#[${rows.join(",")}]⟩\n`;
for(let i=0;i<12;i++)out+=`theorem checked_row_${i} : (row cert (${i>>1} : Fin 6) ${!!(i&1)}).all\n    (fun j => stateStepOK partialTable cert (${i>>1} : Fin 6) ${!!(i&1)} (j / cert.right.edges.size) (j % cert.right.edges.size)) = true := by decide\n`;
out+=`theorem left_nonempty : decide (0 < cert.left.edges.size) = true := by decide
theorem right_nonempty : decide (0 < cert.right.edges.size) = true := by decide
theorem left_seed : (cert.left.pop 0).contains (false,0) = true := by decide
theorem right_seed : (cert.right.pop 0).contains (false,0) = true := by decide
theorem start_state : stateOK cert 0 false 0 0 = true := by decide
theorem rows_checked :
  (List.finRange 6).all (fun q => BB6.Agent1NGram.bits.all (fun a =>
    (row cert q a).all
      (fun i => stateStepOK partialTable cert q a
        (i / cert.right.edges.size) (i % cert.right.edges.size)))) = true := by
  simp [BB6.Agent1NGram.bits, List.finRange, ${Array.from({length:12},(_,i)=>"checked_row_"+i).join(", ")}]
theorem checked : check partialTable cert = true := by
  unfold check
  rw [left_nonempty, right_nonempty, left_seed, right_seed, start_state, rows_checked] <;> rfl
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m :=
  BB6.Agent4Automata.never partialTable cert checked m hm
#print axioms compatible_never
end M${id}\n`;
}
return out+"end BB6.Agent13.Box33D17V22RunSummary\n";}
const fs=require("fs"),path=require("path");process.stdout.write(emit(JSON.parse(fs.readFileSync(path.join(__dirname,"d17v22-run-summary.json"),"utf8"))));
