"use strict";
const element = id => document.getElementById(id);
const stage = document.body.dataset.stage;
let definitions = null, example = null, exampleSource = "", selected = null, chosenRule = null;
let timer = null, generation = 0, controller = null;
const transferred = new URLSearchParams(location.hash.slice(1)).get("source");
if (transferred !== null) element("source").value = transferred;

function message(state, text) {
  document.body.dataset.state = state;
  element("status").dataset.state = state;
  element("status").textContent = text;
}
function provenance() {
  element("provenance").textContent = !example ? "No successful stage result yet."
    : exampleSource === element("source").value ? "The generated graph matches this source."
      : "Showing the previous successful stage result, NOT the current source.";
  element("next-stage").hash = new URLSearchParams({source: element("source").value}).toString();
}
function closure(graph, final) {
  const byId = new Map(graph.nodes.map(node => [node.id, node])), reached = new Set(), pending = [final];
  while (pending.length) {
    const id = pending.pop();
    if (reached.has(id)) continue;
    reached.add(id);
    for (const target of byId.get(id).outputs) if (target !== null) pending.push(target);
  }
  return graph.nodes.filter(node => reached.has(node.id));
}
function label(node, graph) {
  if (node.label) return node.label;
  if (node.token) return `${node.kind}: ${node.text}`;
  if (["name", "integer", "boolean"].includes(node.kind)) {
    return `${node.kind}: ${graph.nodes.find(candidate => candidate.id === node.children[0]).text}`;
  }
  if (node.kind === "binary" || node.kind === "unary") {
    const operator = graph.nodes.find(candidate => candidate.id === node.children[node.kind === "binary" ? 1 : 0]);
    return `${node.kind}: ${operator.text}`;
  }
  return node.kind;
}
function relatedRule(node) {
  if (!definitions) return null;
  if (selected?.panel === "rule") {
    const own = definitions[stage].rules.find(rule => rule.symbol === node.id);
    if (own) return {stage, rule: own};
    const token = node.kind === "TokenCategory" && definitions.tokenizer.rules.find(rule => rule.name === node.text);
    return token ? {stage: "tokenizer", rule: token} : null;
  }
  if (node.token) {
    const rule = definitions.tokenizer.rules.find(rule => rule.name === node.kind);
    return rule ? {stage: "tokenizer", rule} : null;
  }
  const rule = definitions.grammar.rules.find(rule => rule.name === node.kind)
    || definitions.grammar.rules.find(rule => rule.actions.includes(node.kind));
  return rule ? {stage: "grammar", rule} : null;
}
function select(panel, id) {
  const graph = panel === "rule" ? definitions[stage].graph : example;
  const node = graph.nodes.find(node => node.id === id);
  if (!node) throw new Error("Missing selected stage node");
  selected = {panel, id};
  element("inspector-title").textContent = `${panel} / n${id} / ${node.kind} / position ${node.position}`;
  element("inspector-graph").textContent = panel === "rule" ? `${stage} rule-definition graph` : `${stage} generated-example graph`;
  element("kind").textContent = node.kind;
  element("value").textContent = node.text === null ? "vacant (None)" : JSON.stringify(node.text);
  element("bytes").textContent = node.value === null ? "None" : JSON.stringify(node.value);
  element("child-slots").textContent = JSON.stringify(node.childSlots);
  element("links").replaceChildren();
  if (!node.outputs.length) element("links").textContent = "No output slots";
  node.outputs.forEach((target, slot) => {
    const button = document.createElement("button");
    button.type = "button"; button.textContent = `${slot} -> ${target === null ? "None" : `n${target}`}`;
    button.disabled = target === null; button.addEventListener("click", () => select(panel, target));
    element("links").append(button);
  });
  const related = relatedRule(node);
  element("related").disabled = !related;
  element("related").textContent = related ? `Open ${related.stage} rule: ${related.rule.name}` : "No related rule for this node";
  element("related").onclick = related ? () => {
    if (related.stage !== stage) {
      location.href = `/${related.stage}.html#${new URLSearchParams({source: element("source").value, rule: related.rule.name})}`;
    } else {
      if (related.rule.helper) { element("helpers").checked = true; populateRules(related.rule.name); }
      else element("rule-picker").value = related.rule.name;
      showRule();
    }
  } : null;
  for (const area of ["rule", "example"]) for (const group of element(`${area}-graph`).querySelectorAll("[data-node]"))
    group.classList.toggle("selected", area === panel && Number(group.dataset.node) === id);
}
function array(panel, nodes) {
  const container = element(`${panel}-array`);
  container.replaceChildren();
  for (const node of nodes) {
    const cell = document.createElement("li"), position = document.createElement("span"), button = document.createElement("button");
    cell.dataset.node = node.id; position.textContent = node.position; button.type = "button"; button.textContent = node.id === 0 ? "root" : `n${node.id}`;
    button.addEventListener("click", () => select(panel, node.id)); cell.append(position, button); container.append(cell);
  }
}
function drawExample() {
  if (!example) return;
  const all = element("show-tokens").checked;
  const nodes = example.nodes.filter(node => all || (!node.token && node.kind !== "TokenSequence") || node.id === example.final);
  array("example", nodes);
  drawNodGraph(element("example-graph"), nodes, {
    label: node => label(node, example), final: example.final,
    selected: selected?.panel === "example" ? selected.id : null, onSelect: id => select("example", id),
  });
}
function showRule() {
  const rule = definitions[stage].rules.find(rule => rule.name === element("rule-picker").value);
  if (!rule) throw new Error("Unknown rule selection");
  chosenRule = rule;
  const graph = definitions[stage].graph, nodes = closure(graph, rule.node);
  element("rule-source").textContent = rule.source;
  element("rule-facts").textContent = stage === "tokenizer"
    ? `${rule.patternKind === "str" ? "Literal" : "Regular expression"} / priority ${rule.priority} / ${rule.ignored ? "skip; no token node emitted" : "emit token occurrence"}`
    : `${rule.alternatives.length} compiled alternatives / actions: ${[...new Set(rule.actions)].join(", ")}${rule.helper ? " / generated repetition helper" : ""}`;
  array("rule", nodes);
  drawNodGraph(element("rule-graph"), nodes, {label: node => node.label, final: rule.node, selected: rule.node, onSelect: id => select("rule", id)});
  select("rule", rule.node);
}
function populateRules(preferred) {
  const helpers = element("helpers")?.checked || false;
  const rules = definitions[stage].rules.filter(rule => !rule.helper || helpers);
  element("rule-picker").replaceChildren();
  for (const rule of rules) {
    const option = document.createElement("option"); option.value = rule.name;
    option.textContent = `${rule.name}${rule.ignored ? " (skip)" : ""}${rule.helper ? " (generated)" : ""}`;
    element("rule-picker").append(option);
  }
  if (rules.some(rule => rule.name === preferred)) element("rule-picker").value = preferred;
}
async function build() {
  clearTimeout(timer); controller?.abort(); controller = new AbortController();
  const own = ++generation, source = element("source").value;
  message("pending", stage === "tokenizer" ? "Scanning raw text..." : "Tokenizing, then applying grammar composers to the token stream...");
  provenance();
  try {
    const response = await fetch(stage === "tokenizer" ? "/api/tokenize" : "/api/parse", {
      method: "POST", headers: {"Content-Type": "application/json"},
      body: JSON.stringify({source}), signal: controller.signal,
    });
    const result = await response.json();
    if (own !== generation || source !== element("source").value) return;
    if (!response.ok || !result.ok) {
      const error = result.error;
      message("error", `${error.stage || "request"}${error.line ? ` at ${error.line}:${error.column}` : ""}: ${error.message}\nPrevious successful stage result retained.`);
      provenance(); return;
    }
    example = result; exampleSource = source;
    element("example-count").textContent = `${result.tokens.length} token occurrences / ${result.nodes.length} total nodes / final n${result.final}`;
    element("tokens").replaceChildren();
    for (const id of result.tokens) {
      const node = result.nodes.find(node => node.id === id);
      const cell = document.createElement("li"), button = document.createElement("button"), category = document.createElement("b"), text = document.createElement("span");
      cell.dataset.node = id; button.type = "button"; category.textContent = node.kind; text.textContent = node.text;
      button.title = `n${id} at ${node.line}:${node.column}`; button.append(category, text); button.addEventListener("click", () => select("example", id));
      cell.append(button); element("tokens").append(cell);
    }
    drawExample(); select("example", example.final); provenance();
    message("success", stage === "tokenizer" ? "Tokenization succeeded. Grammar, typing, and runtime were not checked." : "Grammar composition succeeded. Types, names, and runtime were not checked.");
  } catch (error) {
    if (error.name === "AbortError" || own !== generation) return;
    message("error", `Cannot build this stage: ${error.message}. Check the local Nod server.`);
    provenance();
  }
}
element("source").addEventListener("input", () => {
  clearTimeout(timer); controller?.abort(); generation++; provenance();
  message("pending", element("auto").checked ? "Source changed; waiting..." : "Source changed. Click the stage build button.");
  if (element("auto").checked) timer = setTimeout(build, 450);
});
element("source").addEventListener("keydown", event => { if ((event.ctrlKey || event.metaKey) && event.key === "Enter") { event.preventDefault(); build(); } });
element("build").addEventListener("click", build);
element("auto").addEventListener("change", () => { clearTimeout(timer); if (element("auto").checked) build(); });
element("show-tokens").addEventListener("change", drawExample);
element("rule-picker").addEventListener("change", showRule);
element("helpers")?.addEventListener("change", () => { populateRules(chosenRule?.name); showRule(); });
async function initialize() {
  try {
    const response = await fetch("/api/rules");
    if (!response.ok) throw new Error(`Rule request failed (${response.status})`);
    definitions = await response.json();
    const requested = new URLSearchParams(location.hash.slice(1)).get("rule");
    if (stage === "grammar" && definitions.grammar.rules.some(rule => rule.name === requested && rule.helper)) element("helpers").checked = true;
    populateRules(requested || (stage === "tokenizer" ? "INTEGER" : "declaration"));
    showRule();
    element("rule-status").textContent = `${definitions[stage].rules.length} definitions exported from the actual parser configuration.`;
  } catch (error) {
    element("rule-status").dataset.error = "true";
    element("rule-status").textContent = `Cannot load rule definitions: ${error.message}. Reload after starting the local server.`;
  }
  await build();
}
initialize();
