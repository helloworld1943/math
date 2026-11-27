"use strict";
const element = id => document.getElementById(id);
let accepted = null, sourceAccepted = "", focus = 0, selected = 0;
let generation = 0, timer = null, controller = null;
const scope = () => element("graph-mode").value;
const graph = () => accepted[scope()];
function status(state, text) {
  document.body.dataset.state = state;
  element("status").dataset.state = state;
  element("status").textContent = text;
}
function provenance() {
  element("provenance").textContent = accepted
    ? sourceAccepted === element("source").value ? "Reports match the current source." : "Showing the previous successful proposal, NOT the current source."
    : "No checked result yet.";
}
function label(node) {
  if (node.kind === "Sort") return `Sort(${node.text})`;
  return node.text === null ? node.kind : `${node.kind}: ${node.text}`;
}
function closure(data, root) {
  const byId = new Map(data.nodes.map(node => [node.id, node])), visited = new Set(), pending = [root];
  while (pending.length) {
    const id = pending.pop();
    if (visited.has(id)) continue;
    visited.add(id);
    pending.push(...byId.get(id).outputs.filter(target => target !== null));
  }
  return data.nodes.filter(node => visited.has(node.id));
}
function select(id) {
  selected = id;
  const node = graph().nodes.find(node => node.id === id);
  if (!node) throw new Error("Selected node does not belong to this graph");
  element("inspector-title").textContent = `${scope()} / n${id} / position ${node.position}`;
  element("kind").textContent = node.kind;
  element("value").textContent = node.text === null ? "vacant (None)" : JSON.stringify(node.text);
  element("bytes").textContent = node.value === null ? "None" : JSON.stringify(node.value);
  element("slots").textContent = JSON.stringify(node.childSlots);
  element("type").textContent = node.type || "Not a typed expression";
  element("constraints").textContent = [
    node.alias ? `TypeDef: ${node.definition} (no runtime storage)` : "",
    node.formalCheck ? "formal check, no execution" : "",
    node.contract ? "named complete-contract implementation" : "",
    node.const ? "const field/binding" : "",
  ].filter(Boolean).join(" / ") || "None";
  element("links").replaceChildren();
  if (!node.outputs.length) element("links").textContent = "No output slots";
  node.outputs.forEach((target, slot) => {
    const button = document.createElement("button"); button.type = "button";
    button.textContent = `${slot} -> ${target === null ? "None" : `n${target}`}`; button.disabled = target === null;
    button.addEventListener("click", () => { focus = target; draw(); select(target); });
    element("links").append(button);
  });
  for (const node of element("graph").querySelectorAll("[data-node]"))
    node.classList.toggle("selected", Number(node.dataset.node) === id);
}
function draw() {
  if (!accepted) return;
  const data = graph();
  if (!data.nodes.some(node => node.id === focus)) focus = data.nodes[0].id;
  const nodes = element("full").checked ? data.nodes : closure(data, focus);
  element("array").replaceChildren();
  for (const node of nodes) {
    const cell = document.createElement("li"), position = document.createElement("span"), button = document.createElement("button");
    cell.dataset.node = node.id; position.textContent = node.position; button.type = "button"; button.textContent = node.id === 0 ? "root" : `n${node.id}`;
    button.addEventListener("click", () => select(node.id)); cell.append(position, button); element("array").append(cell);
  }
  element("graph-title").textContent = scope() === "theory" ? "Verified judgment graph" : "Source grammar graph";
  element("graph-note").textContent = scope() === "theory"
    ? "Verified named judgments: Sort leaves carry numeric levels and Annotation nodes link names to checked types. CheckedType leaves display transparent alias definitions. Separate nodes may be semantically equal."
    : "The source grammar retains category wrappers and token occurrence descriptions. The checker resolves these without modifying this graph.";
  drawNodGraph(element("graph"), nodes, {label, final: focus, selected, onSelect: select});
}
function reportButton(caption, id, mode) {
  const button = document.createElement("button"); button.type = "button"; button.textContent = `${caption}: n${id}`;
  button.dataset.target = id; button.dataset.graph = mode;
  button.addEventListener("click", () => {
    element("graph-mode").value = mode; focus = id; selected = id; draw(); select(id);
  });
  return button;
}
function render() {
  element("reports").replaceChildren();
  for (const [index, report] of accepted.theory.reports.entries()) {
    const row = document.createElement("article"); row.className = "report"; row.dataset.report = index;
    const heading = document.createElement("strong"); heading.textContent = `${report.term} : ${report.type}`;
    const normal = document.createElement("p"); normal.className = "hint"; normal.textContent = `Normal: ${report.normal} : ${report.normalType}`;
    const buttons = document.createElement("div"); buttons.className = "report-buttons";
    for (const [caption, id] of [["Term",report.node],["Type",report.typeNode],["Normal term",report.normalNode],["Normal type",report.normalTypeNode],["Annotation",report.annotation]])
      buttons.append(reportButton(caption, id, "theory"));
    buttons.append(reportButton("Source", report.source, "syntax"));
    row.append(heading, normal, buttons); element("reports").append(row);
  }
  const reports = accepted.theory.reports;
  element("summary").textContent = `${reports.length} checked named judgments\n${accepted.syntax.nodes.length} source nodes\n${accepted.theory.nodes.length} judgment nodes`;
  element("graph-mode").value = "theory";
  focus = reports.length ? reports[reports.length - 1].annotation : 0; selected = focus;
  draw(); select(selected); provenance();
}
async function build() {
  clearTimeout(timer); controller?.abort(); controller = new AbortController();
  const source = element("source").value, own = ++generation;
  status("pending", "Tokenize -> compose -> resolve binders -> check universes and dependent types...");
  provenance();
  try {
    const response = await fetch("/api/theory", {method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({source}),signal:controller.signal});
    const result = await response.json();
    if (own !== generation || source !== element("source").value) return;
    if (!response.ok || !result.ok) {
      status("error", `${result.error.stage || "request"}${result.error.line ? ` at ${result.error.line}:${result.error.column}` : ""}: ${result.error.message}\nProposal rejected; previous result retained.`);
      provenance(); return;
    }
    accepted = result; sourceAccepted = source; render();
    status("success", "Accepted: annotations, declaration types, and dependent applications checked.");
  } catch (error) {
    if (error.name === "AbortError" || own !== generation) return;
    status("error", `Cannot check this source: ${error.message}. Verify the local server.`);
    provenance();
  }
}
element("source").addEventListener("input", () => {
  clearTimeout(timer); controller?.abort(); generation++; provenance();
  status("pending", "Source changed; check again.");
  if (element("auto").checked) timer = setTimeout(build, 500);
});
element("source").addEventListener("keydown", event => { if ((event.ctrlKey || event.metaKey) && event.key === "Enter") {event.preventDefault();build();} });
element("check").addEventListener("click", build);
element("auto").addEventListener("change", () => {clearTimeout(timer);if(element("auto").checked)build();});
element("full").addEventListener("change", draw);
element("graph-mode").addEventListener("change", () => {
  if (!accepted) return;
  focus = scope() === "syntax" ? accepted.syntax.final : accepted.theory.reports.at(-1)?.annotation || 0;
  selected = focus; draw(); select(selected);
});
async function load() {
  try {
    const response = await fetch("/theory_example.nod");
    if (!response.ok) throw new Error(`Example request failed (${response.status})`);
    element("source").value = await response.text(); await build();
  } catch (error) { status("error", `Cannot load example: ${error.message}`); }
}
element("load-example").addEventListener("click", load);
load();
