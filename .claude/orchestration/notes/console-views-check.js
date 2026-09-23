// Render every view of the console with its actual script over answers the real server gave (a JSON map from each
// request to its answer, written by console-views-check.py), in a stand-in DOM, and say what each view showed wrong:
// a view that failed ("Could not read the run"), text that reads NaN, undefined, null or [object …], an exception.
// Requests the map lacks are listed as missing, for the driver to ask the server and run again.
//   node console-views-check.js ANSWERS.json VIEW...        (a VIEW is a hash: now, sessions/fix-278, tasks/251)
const fs = require('fs'), vm = require('vm'), path = require('path');
const [answersFile, ...views] = process.argv.slice(2);
const answers = JSON.parse(fs.readFileSync(answersFile, 'utf8'));
const missing = new Set(), problems = [];

class Node {}
class Text extends Node { constructor(t) { super(); this.data = String(t); } get textContent() { return this.data; } }
const ids = {};
class El extends Node {
  constructor(tag) {
    super(); this.tagName = String(tag).toUpperCase(); this.children = []; this.attrs = {}; this.style = {cssText: ''};
    this.dataset = {}; this.listeners = {}; this.parentNode = null; this.value = ''; this.open = false;
    const set = new Set();
    this.classList = {set, add: (...c) => c.forEach(x => set.add(x)), remove: (...c) => c.forEach(x => set.delete(x)),
      toggle: (c, on) => { if (on === undefined) on = !set.has(c); on ? set.add(c) : set.delete(c); return on; },
      contains: c => set.has(c)};
  }
  set className(v) { this.classList.set.clear(); String(v).split(/\s+/).filter(Boolean).forEach(x => this.classList.set.add(x)); }
  get className() { return [...this.classList.set].join(' '); }
  set id(v) { this.attrs.id = v; ids[v] = this; } get id() { return this.attrs.id; }
  adopt(x) { const c = x instanceof Node ? x : new Text(x); c.parentNode = this; return c; }
  append(...xs) { for (const x of xs) this.children.push(this.adopt(x)); }
  prepend(...xs) { this.children.unshift(...xs.map(x => this.adopt(x))); }
  appendChild(x) { this.append(x); return x; }
  replaceChildren(...xs) { this.children = []; this.append(...xs); }
  replaceWith(x) { if (this.attrs.id) { ids[this.attrs.id] = x; x.attrs.id = x.attrs.id || this.attrs.id; } }
  setAttribute(k, v) { this.attrs[k] = String(v); if (k === 'id') ids[v] = this; if (k === 'class') this.className = v; }
  getAttribute(k) { return this.attrs[k]; }
  addEventListener(t, f) { (this.listeners[t] = this.listeners[t] || []).push(f); }
  querySelectorAll() { return []; } querySelector() { return null; }
  focus() {} blur() {} scrollIntoView() {} setSelectionRange() {}
  set textContent(v) { this.children = [new Text(v)]; } get textContent() { return this.children.map(c => c.textContent).join(''); }
}
const header = {};
for (const id of ['pills', 'nav', 'main', 'toast', 'jump', 'jumplist', 'pause']) { header[id] = new El('div'); header[id].id = id; }
const updatedBox = new El('div'); header.updated = new El('span'); header.updated.id = 'updated'; updatedBox.append(header.updated);
const document = {
  createElement: t => new El(t), createElementNS: (ns, t) => new El(t), createTextNode: t => new Text(t),
  getElementById: id => ids[id] || null, querySelectorAll: () => [], documentElement: {dataset: {}}, body: new El('body'),
  activeElement: null};
const location = {hash: '', search: '', reload() { problems.push('the page asked to reload itself'); }};
function key(url) {  // a request as the map keys it: its path and its parameters in order, the token left out
  const u = new URL(url, 'http://console');
  const params = [...u.searchParams.entries()].filter(([k]) => k !== 'token').sort();
  return u.pathname + (params.length ? '?' + params.map(([k, v]) => `${k}=${v}`).join('&') : '');
}
async function fetch(url, options) {
  if (options && options.method === 'POST') throw new Error('a view posted a control');
  const k = key(url);
  if (!(k in answers)) { missing.add(k); throw new Error('not in the map: ' + k); }
  const [status, body] = answers[k];
  return {ok: status < 400, status, json: async () => body};
}
const context = {document, Node, HTMLElement: El, console, URL, URLSearchParams, Date, Math, JSON, Number, String, Object, Array,
  Set, Map, Promise, Error, RegExp, location, fetch, confirm: () => false,
  localStorage: {getItem: () => null, setItem() {}},
  window: {addEventListener() {}, scrollTo() {}, scrollY: 0, getSelection: () => '', matchMedia: () => ({matches: false})},
  getComputedStyle: () => ({getPropertyValue: () => '#888'}),
  setTimeout: () => 0, clearTimeout() {}, setInterval() {}, ResizeObserver: class { observe() {} },
  requestAnimationFrame: f => f()};
context.window.getSelection = () => '';
let source = fs.readFileSync(path.join(__dirname, '../dashboard.html'), 'utf8').match(/<script>([\s\S]*?)<\/script>/)[1];
source = source.replace(/\nrefresh\(\);\s*$/, '\n');
vm.createContext(context);
vm.runInContext(source + '\nthis.__refresh = refresh;', context);

function texts(n, out) {
  if (n instanceof Text) out.push(n.data);
  else if (n && n.children) { for (const k of ['title', 'aria-label']) if (n.attrs[k]) out.push(n.attrs[k]); n.children.forEach(c => texts(c, out)); }
  return out;
}
(async () => {
  const report = {};
  for (const view of views) {
    location.hash = '#' + view;
    const before = missing.size;
    try { await context.__refresh(); } catch (e) { problems.push(`${view}: threw ${e && e.stack || e}`); }
    const shown = texts(ids.main, []), header = texts(ids.pills, []).concat(texts(ids.nav, []));
    const said = [];
    if (shown.some(t => /Could not read the run/.test(t))) said.push('failed: ' + shown.join(' ').match(/Could not read the run.{0,400}/)[0]);
    for (const t of shown.concat(header)) {
      if (/\bNaN\b|\bundefined\b|\[object |^null$|\bInfinity\b/.test(t)) said.push('reads: ' + JSON.stringify(t.slice(0, 160)));
    }
    report[view] = {texts: shown.length, words: shown.join(' ').split(/\s+/).length, problems: [...new Set(said)].slice(0, 12),
                    missing: missing.size > before};
  }
  console.log(JSON.stringify({missing: [...missing], problems, report}));
})();
