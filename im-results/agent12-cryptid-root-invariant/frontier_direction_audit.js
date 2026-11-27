// Constant-length symbolic trace audit: unspecified tape cells are UNKNOWN,
// not silently zero. Every read must be determined by the clause's prefix.
const machine="1RB---0RC0RE1RD1RF1LE0LB1RC0LD1RC1RA";
const clauses=[
 // name, state, K physical prefix outward, L physical prefix outward,
 // left/right blank beyond prefix?, raw defined transitions, expected mode.
 ["ELempty","E","","",true,false,1,"C"],
 ["ELlast0","E","0","",true,false,1,"C"],
 ["EL0cons","E","0","",false,false,1,"C"],
 ["EL1","E","10","",false,false,2,"E"],
 ["EL2","E","110","10",false,false,7,"E"],
 ["ELhigh","E","111","",false,false,5,"D"],
 ["DRempty","D","110","",false,true,8,"E"],
 ["DR0","D","110","10",false,false,4,"D"],
 ["DRlast1","D","110","110",false,true,28,"E"],
 ["DRsucc","D","110","11",false,false,3,"C"],
 ["CRempty1","C","10","",false,true,9,"E"],
 ["CRemptyhigh","C","11","",false,true,21,"E"],
 ["CR0","C","","10",false,false,2,"C"],
 ["CRlast1","C","","110",false,true,33,"E"],
 ["CR10","C","","11010",false,false,5,"C"],
 ["CRlast11","C","","110110",false,true,25,"E"],
 ["CR11cons","C","","1101101",false,false,25,"E"],
 ["CR1high","C","","110111",false,false,15,"D"],
 ["CRhalt","C","","111",false,false,2,"A"]
];
function trace([name,q,l,r,lb,rb,n,end]){
 let tape=new Map(),head=q==="E"?-1:0,initial=head,ds="";
 for(let i=0;i<l.length;i++)tape.set(-1-i,+l[i]);
 for(let i=0;i<r.length;i++)tape.set(i,+r[i]);
 for(let i=0;i<n;i++){
  let bit=tape.get(head);
  if(bit===undefined&&((head<0&&lb)||(head>=0&&rb)))bit=0;
  if(bit===undefined)throw Error(name+": unknown read "+head+" after "+ds);
  let j=6*(q.charCodeAt()-65)+3*bit,rule=machine.slice(j,j+3);
  if(rule==="---")throw Error(name+": premature halt");
  tape.set(head,+rule[0]);ds+=rule[1];head+=rule[1]==="R"?1:-1;q=rule[2];
 }
 if(q!==end)throw Error(name+": unexpected end");
 return {name,n,ds,headDelta:head-initial,cutDelta:head+(end==="E"?1:0)}
}
module.exports={clauses,trace};
if(require.main===module)console.log(JSON.stringify(clauses.map(trace),null,2));