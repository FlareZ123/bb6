// Untrusted finite-path generator; every block exit is rechecked by Lean.
// The opaque markers 8 and 9 are never read. No extrapolation from large p.
// Uses the same block conventions and proof emitter as generate_raw140_variant_loops.js.
const fs=require("fs"), path=require("path");
function exits(f){
 const t=tables[f],e={};
 for(let q=0;q<6;q++)for(let d=0;d<2;d++)for(let a=0;a<8;a++){
  let p=d?0:2,b=a,r=q,k=0;
  while(p>=0&&p<3&&k<145){let c=t[2*r+((b>>p)&1)];if(c===24)break;
   b=(b&~(1<<p))|(((c>>1)&1)<<p);r=c>>2;p+=(c&1)?1:-1;k++}
  if(p<0||p>=3)e[[q,d,a]]=[r,p>=3?1:0,b,k];
 }return e;
}
function add(a,b){return [a[0]+b[0],a[1]+b[1]]}
function count(s){return s===undefined?[0,1]:s.startsWith("p")?[1,s.length===1?0:+s.slice(2)]:[0,+s]}
function ct(c){if(!c[0])return ""+c[1];if(c[0]!==1)throw Error("bad count "+c);return c[1]?"(p+"+c[1]+")":"p"}
function push(S,a,c){if(!S.length&&a===0)return;if(S.length&&Array.isArray(S[0])&&S[0][0]===a){S[0]=[a,add(S[0][1],c)];return}S.unshift([a,c]);}
function parse(s){let S=[];for(let a of s.trim().split(/ +/).filter(Boolean).reverse()){if(a==="X"||a==="Y")S.unshift(a);else{let [b,c]=a.split("^");push(S,+b,count(c))}}return S}
function pop(S,a,c){let A=S.slice();if(!A.length){if(a!==0||c[0]||c[1]!==1)throw Error("bad blank");return A}if(!Array.isArray(A[0])||A[0][0]!==a)throw Error("bad pop "+JSON.stringify({S,a,c}));let d=[A[0][1][0]-c[0],A[0][1][1]-c[1]];if(d.some(x=>x<0))throw Error("negative symbolic");A.shift();if(d[0]||d[1])A.unshift([a,d]);return A}
function fmt(S){if(!S.length)return "[]";if(typeof S[0]==="string"){if(S.length!==1)throw Error("marker internal");return S[0]}let [a,c]=S[0],R=fmt(S.slice(1));if(c[0])return S.length===1?"(U "+a+" "+ct(c)+")":"(U "+a+" "+ct(c)+" ++ "+R+")";return "("+Array(c[1]).fill("S "+a).join(" :: ")+" :: "+R+")"}
function cfg(q,d,L,R){return "boundary "+q+" "+(d?"true":"false")+" "+fmt(L)+" "+fmt(R)}
function rule(name,table,L0,R0,q,d,L1,R1,q1,d1,seq){
 let L=parse(L0),R=parse(R0),start=cfg(q,d,L,R),costs=[],body=[],E=exits(table),M="M"+table;
 for(let [i,tok] of seq.trim().split(/ +/).entries()){let [src,n]=tok.split("^"),c=count(n),a=+src[2];if(q!=="ABCDEF".indexOf(src[0])||d!==(src[1]==="R"?1:0))throw Error(name+" state "+tok);let e=E[[q,d,a]];if(!e)throw Error(name+" undefined "+tok);let [r,z,b,k]=e,pre=cfg(q,d,L,R),LL=d?L:pop(L,a,c),RR=d?pop(R,a,c):R,LL1=LL.slice(),RR1=RR.slice();push(z?LL1:RR1,b,c);let post=cfg(r,z,LL1,RR1),lemma,co;
 if(n!==undefined){if(q!==r||d!==z)throw Error("bad sweep");lemma="sweep"+src[1]+" "+M+" "+q+" (S "+a+") (S "+b+") "+k+" "+ct(c)+" "+fmt(LL)+" "+fmt(RR)+" (by rfl)";co="("+ct(c)+"*"+k+")"}else{lemma="step"+src[1]+" "+M+" "+q+" "+r+" "+(z?"true":"false")+" (S "+a+") (S "+b+") "+k+" "+fmt(LL)+" "+fmt(RR)+" (by rfl)";co=""+k}
 body.push("  have h"+i+" : run "+M+" "+co+" ("+pre+") = some ("+post+") := by\n    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using "+lemma);costs.push(co);L=LL1;R=RR1;q=r;d=z;
 }
 let goal=cfg(q1,d1,parse(L1),parse(R1));if(cfg(q,d,L,R)!==goal)throw Error(name+" got "+cfg(q,d,L,R)+" expected "+goal);
 let vars=(seq.includes("^p")?" (p : Nat)":"")+([L0,R0].join(" ").includes("X")?" (X : List Sym)":"")+([L0,R0].join(" ").includes("Y")?" (Y : List Sym)":"");
 let sum=costs.join("+"),expr="h0";for(let i=1;i<costs.length;i++)expr="(join "+expr+" h"+i+")";
 return "theorem "+name+vars+" : run "+M+" ("+sum+") ("+start+") = some ("+goal+") := by\n"+body.join("\n")+"\n  exact "+expr+"\n";
}

const variants=[[31,21,12,2,4,"1226666667",408],[35,21,9,1,0,"112",31],[37,21,17,1,2,"12267",83],[40,21,10,1,2,"12267",87],[41,21,18,1,3,"112267",115],[42,21,3,1,0,"125",37],[43,21,7,2,4,"1226662667",404],[44,21,11,1,2,"12267",81],[45,21,15,1,3,"122667",137],[46,21,19,2,4,"1226666667",410],[74,23,8,2,4,"1226662667",406],[83,23,18,1,2,"12267",85],[85,23,7,2,3,"122666667",338]];
const tables=Object.fromEntries(variants.map(([id,a,f])=>[id,[7,a,11,12,15,1,6,18,4,17,f,24]]));
tables.base=[7,24,11,12,15,1,6,18,4,17,24,24];
function findPath(id,k,n,head=0){
  let q=head,d=1,L=[8,...(head===4?[1]:Array(k).fill(3))],R=[9,...("115".repeat(n)).split("").map(Number).reverse()],cost=0,seq=[];
  const E=exits(id);
  for(let i=0;i<2000;i++){
    const S=d?R:L,b=S.at(-1);
    if(b===8||b===9){
      if(b!==9||q!==4||d!==1||L[0]!==8||R.length!==1||L.at(-1)!==1)throw Error("opaque context read: "+id);
      return {prefix:L.slice(1).reverse().join(""),cost,seq:seq.join(" ")};
    }
    S.pop();const e=E[[q,d,b]];if(!e)throw Error("missing exit "+id);
    const [r,z,y,t]=e;seq.push("ABCDEF"[q]+(d?"R":"L")+b);
    q=r;d=z;cost+=t;(d?L:R).push(y);
  }
  throw Error("path limit "+id);
}
function words(s){return s.split("").join(" ");}
function cons(s,x){return s.split("").map(c=>"S "+c+" :: ").join("")+x;}
function emit(){
  let defs="def Mbase : Table := base\n";
  let rules=[];
  for(let [id,a,f,n,k,prefix,cost] of variants){
    const x=findPath(id,k,n);
    if(x.prefix!==prefix||x.cost!==cost)throw Error("mismatch "+id);
    const tr=c=>"some ⟨"+((c&2)?"true":"false")+","+((c&1)?"true":"false")+","+Math.floor(c/4)+"⟩";
    defs+="def M"+id+" : Table := fill ("+tr(a)+") ("+tr(f)+")\n";
    rules.push(rule("transfer"+id,id,words("3".repeat(k))+" X",words("115".repeat(n))+" Y",0,1,words(prefix)+" X","Y",4,1,x.seq));
  }
  const b=findPath("base",0,1,4);
  if(b.prefix!=="1133"||b.cost!==45)throw Error("base loop");
  rules.push(rule("erTriplet","base","1 X","1 1 5 Y",4,1,"1 1 3 3 X","Y",4,1,b.seq));
  let more=`
def trip : Nat → List Sym
  | 0 => []
  | n+1 => S 1 :: S 1 :: S 5 :: trip n

def bank : Nat → List Sym
  | 0 => []
  | n+1 => bank n ++ [S 1,S 3,S 3]

theorem erMany (M : Table) (ext : Extends M) (n : Nat) (X Y : List Sym) :
    run M (45*n) (boundary 4 true (S 1 :: X) (trip n ++ Y)) =
      some (boundary 4 true (S 1 :: (bank n ++ X)) Y) := by
  induction n generalizing X with
  | zero => simp [trip,bank,run]
  | succ n ih =>
    have h0 : run M 45 (boundary 4 true (S 1 :: X)
        (S 1 :: S 1 :: S 5 :: (trip n ++ Y))) =
        some (boundary 4 true (S 1 :: S 1 :: S 3 :: S 3 :: X) (trip n ++ Y)) :=
      run_ext M ext _ _ _ (erTriplet X (trip n ++ Y))
    have h1 := ih (S 1 :: S 3 :: S 3 :: X)
    simpa only [trip,bank,List.cons_append,List.append_assoc,List.nil_append,
      show 45+45*n=45*(n+1) by omega] using join h0 h1
`;
  for(let [id,a,f,j,k,prefix,cost] of variants){
    more+="\ntheorem transferMany"+id+" (n : Nat) (X Y : List Sym) :\n    run M"+id+" ("+cost+"+45*n) (boundary 0 true ("+cons("3".repeat(k),"X")+") (trip "+j+" ++ (trip n ++ Y))) =\n      some (boundary 4 true (S 1 :: (bank n ++ ("+cons(prefix.slice(1),"X")+"))) Y) := by\n  have h0 := transfer"+id+" X (trip n ++ Y)\n  have h1 := erMany M"+id+" (fill_extends _ _) n ("+cons(prefix.slice(1),"X")+") Y\n  simpa only [trip,List.cons_append,List.nil_append] using join h0 h1\n";
  }
  return "import Raw140ExtraCore\nnamespace Raw140VariantTransfer\nopen BB6BlockFAR Raw140Orbit Raw140Extra\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"+defs+rules.join("\n")+more+"\n"+variants.map(v=>"#print axioms transferMany"+v[0]).join("\n")+"\n#print axioms erMany\nend Raw140VariantTransfer\n";
}
if(require.main===module)fs.writeFileSync(path.join(__dirname,"Raw140VariantTransfer.lean"),emit());
