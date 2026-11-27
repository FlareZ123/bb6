const fs=require('fs');
const lag=`function lagDfa(params){
 const {lag:k,r,c0,c1,m0,m1}=params,mask=2**k-1,words=[[0,[]]],ids=new Map([['0;',0]]),delta=[[-1,-1]];
 function push(i,b){if(delta[i][b]>=0)return delta[i][b];const [raw,v]=words[i],d=b^((raw>>(k-1))&1),raw2=((raw<<1)|b)&mask;let w;
 if(!v.length)w=d?[1,1]:[];
 else if(v[0]===d){const c=d?c1:c0,m=d?m1:m0;let n=v[1]+1;if(n===c+m)n=c;w=[d,n,...v.slice(2)]}
 else w=[d,1,...v].slice(0,2*r);
 let key=raw2+';'+w.join(','),j=ids.get(key);if(j===undefined){j=words.length;ids.set(key,j);words.push([raw2,w]);delta.push([-1,-1])}delta[i][b]=j;return j}
 return {push,finish:()=>delta.flat().map(x=>Math.max(0,x)),size:()=>words.length}
}
function chunkDfa(params){
 const {width,k,c,m}=params,words=[[0,0,[]]],ids=new Map([["0,0,",0]]),delta=[[-1,-1]];
 function push(i,b){if(delta[i][b]>=0)return delta[i][b];let [n,w,r]=words[i];if(i===0&&!b)return 0;w=2*w+b;n++;if(n===width){if(r[0]===w){let a=r[1]+1;if(a===c+m)a=c;r=[w,a,...r.slice(2)]}else r=[w,1,...r].slice(0,2*k);n=0;w=0}let key=n+","+w+","+r.join(","),j=ids.get(key);if(j===undefined){j=words.length;ids.set(key,j);words.push([n,w,r]);delta.push([-1,-1])}delta[i][b]=j;return j}
 return {push,finish:()=>delta.flat().map(x=>Math.max(0,x)),size:()=>words.length};
}
`;
const s=fs.readFileSync(process.argv[2],'utf8').replace('function solve(',lag+'\nfunction solve(').replace('Array.isArray(left)?dfa(left):blockDfa(left)','Array.isArray(left)?dfa(left):left.lag?lagDfa(left):left.width?chunkDfa(left):blockDfa(left)').replace('Array.isArray(right)?dfa(right):blockDfa(right)','Array.isArray(right)?dfa(right):right.lag?lagDfa(right):right.width?chunkDfa(right):blockDfa(right)');
const {solve}=Function(s)();
const queries=JSON.parse(fs.readFileSync(0,'utf8'));
const records=queries.map(({id,table,p})=>{
 const z=solve(table,p,p,30000);
 if(z.status!=='ok')throw Error('witness mismatch '+id);
 return {id,table,...z};
});
process.stdout.write(JSON.stringify(records));
