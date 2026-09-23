// Execute the actual layout renderer without a browser or network. This DOM only supplies presentation primitives.
const fs = require('fs'), vm = require('vm'), assert = require('assert'), path = require('path');
class Element {
  constructor(tag) { this.tag=tag; this.children=[]; this.attrs={}; this.style={}; this.dataset={};
    this.classList={add(){},remove(){},toggle(){},contains(){return false}}; }
  append(...xs) { this.children.push(...xs); }
  appendChild(x) { this.children.push(x); return x; }
  setAttribute(k,v) { this.attrs[k]=String(v); }
  addEventListener() {}
  querySelectorAll() { return []; }
  replaceChildren(...xs) { this.children=xs; }
}
const document={createElement:t=>new Element(t),createTextNode:t=>String(t),getElementById:()=>new Element('div'),
  querySelectorAll:()=>[],documentElement:{dataset:{}},body:new Element('body')};
const context={document,Node:Element,HTMLElement:Element,console,URL,URLSearchParams,Date,Math,JSON,
  location:{hash:'#bases',search:''},localStorage:{getItem:()=>null,setItem(){}},
  window:{addEventListener(){},scrollTo(){},matchMedia:()=>({matches:false})},
  setTimeout(){},clearTimeout(){},setInterval(){},ResizeObserver:class {observe(){}},
  requestAnimationFrame:f=>f()};
let source=fs.readFileSync(path.join(__dirname,'../dashboard.html'),'utf8').match(/<script>([\s\S]*?)<\/script>/)[1];
source=source.replace(/\nrefresh\(\);\s*$/,'\n');
vm.createContext(context);vm.runInContext(source,context);
const parts=['base','reasoning','direction','catalogue','working','delta'].map((part,i)=>({part,sid:'s'+i,
  own:10000,context:(i+1)*10000,forked:part==='delta',entry:{warm:true},purposes:['steering']}));
const roles=[{role:'reviewer',base:'xhigh',on:true,forks:'layer-reviewer',placement:'above changes',origin_sid:'s5',origin_context:60000,
  layer:{name:'layer-reviewer',context:65000,entry:{warm:true}},layer_own:5000},
  {role:'investigator',base:'xhigh',on:true,forks:'churn-investigator',placement:'below changes',origin_sid:'s4',origin_context:50000,
   layer:{name:'layer-investigator',context:55000,entry:{warm:true}},layer_own:5000,
   churn:{name:'churn-investigator',entry:{warm:true}},churn_own:2000}];
const data={bases:[{who:'xhigh',parts,deltas:true,forks:'delta',staleness:{}}],roles,held:[],kb:null,
  projected:{xhigh:{valid:true,stable:10000,layer:30000,total:40000,at:Date.now()/1000,
    parts:[{part:'stable',tokens:10000},{part:'direction',tokens:10000},{part:'catalogue',tokens:10000},{part:'working',tokens:10000}]}},
  role_messages:{reviewer:500,investigator:500},rules:{project_every:600}};
const rendered=context.organization(data);
const text=JSON.stringify(rendered);
for (const name of ['reference reasoning','catalogue','above changes','below changes','unmeasured']) assert(text.includes(name),name);
assert(!text.includes('NaN'));
data.roles[0].origin_sid='earlier';
assert(JSON.stringify(context.organization(data)).includes('earlier parent'));
data.projected.xhigh={valid:false,error:'missing source'};
assert.doesNotThrow(()=>context.organization(data));
console.log('Console layout: named parts, role placement, historical parents and unknown projections passed.');
