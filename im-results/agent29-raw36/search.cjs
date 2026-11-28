
// Search candidate certificates for literal partial six-state tables.
// A cutoff is an OPEN leaf, never a nonhalting verdict.
function makeSearch(codes, opts={}) {
  const decode=a=>a<0?'---':String(a/12|0)+(a%12>=6?'R':'L')+'ABCDEF'[a%6];
  const show=p=>p.map(decode).join('').match(/.{6}/g).join('_');
  const parse=s=>s.replaceAll('_','').match(/.{3}/g).map(a=>a==='---'?-1:(+a[0])*12+(a[1]==='R'?6:0)+'ABCDEF'.indexOf(a[2]));
  const prep=code=>{const rev=+code[0],D=[...code.slice(1)].map(x=>parseInt(x,36)),d=D.length/2,N=6*d+1,H=N-1,inv=Array.from({length:d},()=>[]);for(let i=0;i<D.length;i++)inv[D[i]].push([i>>1,i%2]);return {code,rev,D,d,N,H,inv}};
  const valid=code=>/^[01]0[0-9a-z]+$/.test(code)&&code.length%2===1&&Math.max(...[...code.slice(1)].map(x=>parseInt(x,36)))<(code.length-1)/2;
  const bank=[...new Set(codes)].filter(valid).map(prep);
  function far(p,c) {
    const {rev,D,d,N,H,inv}=c,wide=H>=31;
    const bit=i=>wide?1n<<BigInt(i):1<<i,zero=wide?0n:0,one=bit(0),halt=bit(H),T=Array(2*N).fill(zero),rules=[];
    T[H]=T[N+H]=halt;
    for(let l=0;l<d;l++)for(let q=0;q<6;q++)for(let a=0;a<2;a++){
      const mv=p[2*q+a],dst=a*N+6*l+q;
      if(mv<0){T[dst]=halt;continue}
      const w=mv>=12?1:0,r=mv%12>=6?1:0,nxt=mv%6;
      if(r!==rev)T[dst]=bit(6*D[2*l+w]+nxt);
      else for(const [j,b] of inv[l])rules.push([dst,b*N+6*j+nxt,w*N]);
    }
    for(;;){
      let z=halt,zz;do{zz=z;for(let j=0;j<N;j++)if(T[j]&z)z|=bit(j);if(z&one)return null}while(z!==zz);
      let changed=false;
      for(const [dst,src,off] of rules){let v=T[dst],b=T[src];while(b){const m=b&-b;const k=wide?m.toString(2).length-1:31-Math.clz32(m);v|=T[off+k];b^=m}if(v!==T[dst]){T[dst]=v;changed=true}}
      if(!changed)return c.code;
    }
  }
  const makeClassifier=(L,period)=>{
    const O=L+2,W=2*L+5,FULL=(1n<<BigInt(W))-1n,bits=Array.from({length:W},(_,i)=>1n<<BigInt(i)),above=bits.map(x=>FULL^(x-1n)),below=bits.map(x=>2n*x-1n);
    return p=>{let q=0,h=O,t=0n,tr=[],prev=Array.from({length:6},()=>[]);
      for(let n=0;n<=L;n++){const s=2*q+Number((t&bits[h])!==0n);if(p[s]<0)return ['hole',n,s];
        let low=h,high=h,i=n-1;
        for(let jdx=prev[q].length-1;jdx>=0;jdx--){const j=prev[q][jdx];if(n-j>period)break;
          while(i>=j){low=Math.min(low,tr[i][0]);high=Math.max(high,tr[i][0]);i--}
          const [h0,t0]=tr[j],d=h-h0;
          if(d>=0&&((t0^(t>>BigInt(d)))&above[low])===0n)return ['cycle',j,n-j,true,low-O];
          if(d<=0&&((t0^(t<<BigInt(-d)))&below[high])===0n)return ['cycle',j,n-j,false,high-O];
        }
        tr.push([h,t]);prev[q].push(n);
        const a=p[s];t=a>=12?t|bits[h]:t&~bits[h];h+=a%12>=6?1:-1;q=a%6;
      }return ['open'];
    }
  };
  const short=makeClassifier(opts.short||160,opts.period||80),long=makeClassifier(opts.long||2000,opts.longPeriod||256);
  const pow25=n=>25n**BigInt(n);
  function run(parent,emit=false) {
    const p=typeof parent==='string'?parse(parent):parent.slice();
    const stats={nodes:0,split:0,cycle:0,far:0,last:0,open:0,halt:0,score:0};
    const mass={halt:0n,nonhalt:0n,open:0n};const opens=[],used={};
    function walk(){
      ++stats.nodes;if(opts.maxNodes&&stats.nodes>opts.maxNodes)throw Error('node limit; no exhaustive result');
      const holes=p.filter(x=>x===-1).length;let a=short(p);
      if(a[0]==='open'){
        for(const c of bank){const code=far(p,c);if(code){stats.far++;mass.nonhalt+=pow25(holes);used[code]=(used[code]||0)+1;return emit?['far',code]:null}}
        a=long(p);
      }
      if(a[0]==='cycle'){stats.cycle++;mass.nonhalt+=pow25(holes);return emit?a:null}
      if(a[0]==='open'){stats.open++;mass.open+=pow25(holes);opens.push(show(p));return emit?['open',show(p)]:null}
      const [,n,s]=a;
      if(!holes)throw Error('hole count');
      stats.halt++;stats.score=Math.max(stats.score,n+6);mass.halt+=pow25(holes-1);
      if(holes===1){stats.last++;mass.nonhalt+=24n;return emit?['last',n,s]:null}
      stats.split++;const kids=[];
      for(let b=0;b<24;b++){p[s]=b;const kid=walk();if(emit)kids.push(kid)}
      p[s]=-1;return emit?['split',n,s,kids]:null;
    }
    const expected=pow25(p.filter(x=>x===-1).length),tree=walk();
    if(mass.halt+mass.nonhalt+mass.open!==expected)throw Error('partition mass');
    return {parent:show(p),stats,mass:Object.fromEntries(Object.entries(mass).map(([k,v])=>[k,String(v)])),expected:String(expected),opens,used,...(emit?{tree}:{})};
  }
  return {run,parse,show,decode,short,long,far,bank};
}

module.exports = { makeSearch };
