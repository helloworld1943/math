"use strict";
const el = id => document.getElementById(id);
let accepted = null, selected = 0, timer = null, generation = 0, controller = null;
let acceptedSource = "";
function status(state, message) {
  el("status").dataset.state = state;
  el("status").textContent = message;
  document.body.dataset.state = state;
}
function provenance() {
  el("provenance").textContent = !accepted ? "No successful proposal has been accepted."
    : el("source").value === acceptedSource ? "Graph and output match the current source."
      : "Showing the previous successful graph and output, NOT the current source.";
}
function nodeLabel(node) {
  if (node.token) return node.text;
  if (["name", "integer", "boolean"].includes(node.kind)) {
    const token = accepted.nodes.find(candidate => candidate.id === node.children[0]);
    return `${node.kind}: ${token.text}`;
  }
  if (node.kind === "binary" || node.kind === "unary") {
    const operator = accepted.nodes.find(candidate => candidate.id === node.children[node.kind === "binary" ? 1 : 0]);
    return `${node.kind}: ${operator.text}`;
  }
  return node.kind;
}
function select(id) {
  selected = id;
  const node = accepted.nodes.find(node => node.id === id);
  if (!node) throw new Error("Missing selected graph node");
  el("inspector-title").textContent = `n${node.id} / ${node.kind} / position ${node.position}`;
  el("kind").textContent = node.token ? `Token.${node.kind}` : `Composer.${node.kind}`;
  el("location").textContent = `${node.line}:${node.column}`;
  el("value").textContent = node.text === null ? "vacant (None)" : JSON.stringify(node.text);
  el("bytes").textContent = node.value === null ? "None" : JSON.stringify(node.value);
  el("type").textContent = node.type || "Not a typed expression";
  el("binding").textContent = node.binding === null ? "None" : `n${node.binding} (semantic annotation)`;
  el("child-slots").textContent = JSON.stringify(node.childSlots);
  el("links").replaceChildren();
  if (!node.outputs.length) el("links").textContent = "No output slots";
  node.outputs.forEach((target, slot) => {
    const button = document.createElement("button");
    button.type = "button";
    button.textContent = `${slot} -> ${target === null ? "None" : `n${target}`}`;
    button.disabled = target === null;
    button.addEventListener("click", () => select(target));
    el("links").append(button);
  });
  for (const group of el("graph").querySelectorAll("[data-node]"))
    group.classList.toggle("selected", Number(group.dataset.node) === id);
}
function draw() {
  if (!accepted) return;
  const all = el("show-tokens").checked;
  const nodes = accepted.nodes.filter(node => all || (!node.token && node.kind !== "TokenSequence"));
  drawNodGraph(el("graph"), nodes, {
    label: nodeLabel, final: accepted.final, selected, onSelect: select,
  });
  select(selected);
}
function render() {
  el("output").textContent = accepted.output.length ? accepted.output.join("\n") : "(no print output)";
  el("variables").replaceChildren();
  for (const [name, value] of Object.entries(accepted.variables)) {
    const span = document.createElement("span"); span.textContent = `${name} = ${value}`; el("variables").append(span);
  }
  if (!Object.keys(accepted.variables).length) el("variables").textContent = "None";
  el("functions").replaceChildren();
  for (const fn of accepted.functions) {
    const span = document.createElement("span");
    span.textContent = `${fn.name}(${fn.parameters.map(([name, type]) => `${type} ${name}`).join(", ")}) ${fn.returns}`;
    el("functions").append(span);
  }
  if (!accepted.functions.length) el("functions").textContent = "None";
  el("metrics").textContent = `${accepted.tokens.length} token occurrences / ${accepted.nodes.length} graph nodes / ${accepted.steps} execution steps / final n${accepted.final}`;
  el("tokens").replaceChildren(); el("array").replaceChildren();
  for (const node of accepted.nodes) {
    const cell = document.createElement("li"), position = document.createElement("span"), button = document.createElement("button");
    cell.dataset.node = node.id; position.textContent = node.position; button.type = "button";
    button.textContent = node.id === 0 ? "root" : `n${node.id}`; button.className = node.id === accepted.final ? "final" : "";
    button.addEventListener("click", () => select(node.id)); cell.append(position, button); el("array").append(cell);
    if (node.token) {
      const occurrence = document.createElement("li"), tokenButton = document.createElement("button"), category = document.createElement("b"), text = document.createElement("span");
      occurrence.dataset.node = node.id; tokenButton.type = "button"; category.textContent = node.kind; text.textContent = node.text;
      tokenButton.append(category, text); tokenButton.title = `n${node.id} at ${node.line}:${node.column}`;
      tokenButton.addEventListener("click", () => select(node.id)); occurrence.append(tokenButton); el("tokens").append(occurrence);
    }
  }
  el("graph-empty").hidden = true; draw(); provenance();
}
async function build() {
  clearTimeout(timer);
  controller?.abort();
  controller = new AbortController();
  const own = ++generation, source = el("source").value;
  status("pending", "Tokenize -> compose -> check -> execute...");
  provenance();
  try {
    const response = await fetch("/api/run", {method: "POST", headers: {"Content-Type": "application/json"}, body: JSON.stringify({source}), signal: controller.signal});
    const result = await response.json();
    if (own !== generation || source !== el("source").value) return;
    if (!response.ok || !result.ok) {
      const error = result.error;
      status("error", `${error.stage || "request"}${error.line ? ` at ${error.line}:${error.column}` : ""}: ${error.message}\nProposal rejected. Previous successful results are unchanged.`);
      provenance(); return;
    }
    accepted = result; acceptedSource = source; selected = result.final;
    render(); status("success", "Accepted: syntax, semantic checks, and execution succeeded.");
  } catch (error) {
    if (error.name === "AbortError" || own !== generation) return;
    status("error", `Cannot complete the request: ${error.message}. Check that the local Nod server is running.`);
    provenance();
  }
}
el("source").addEventListener("input", () => {
  clearTimeout(timer); controller?.abort(); generation++; provenance();
  status("pending", el("auto").checked ? "Source changed; waiting to build..." : "Source changed. Click Build & run.");
  if (el("auto").checked) timer = setTimeout(build, 500);
});
el("source").addEventListener("keydown", event => { if ((event.ctrlKey || event.metaKey) && event.key === "Enter") { event.preventDefault(); build(); } });
el("run").addEventListener("click", build);
el("show-tokens").addEventListener("change", draw);
el("auto").addEventListener("change", () => { clearTimeout(timer); if (el("auto").checked) build(); });
async function loadExample() {
  try {
    const response = await fetch("/example.nod");
    if (!response.ok) throw new Error(`Example request failed (${response.status})`);
    el("source").value = await response.text(); await build();
  } catch (error) { status("error", `Cannot load example: ${error.message}`); }
}
el("example").addEventListener("click", loadExample);
loadExample();
