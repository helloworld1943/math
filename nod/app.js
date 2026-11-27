"use strict";
const el = id => document.getElementById(id);
let accepted = null, selected = 0, timer = null, generation = 0, controller = null;
let acceptedSource = "";
let acceptedPackages = "";
const graphData = () => accepted.packageGraphs ? accepted.packageGraphs[el("package-graph").value] : accepted;
function status(state, message) {
  el("status").dataset.state = state;
  el("status").textContent = message;
  document.body.dataset.state = state;
}
function provenance() {
  el("provenance").textContent = !accepted ? "No successful proposal has been accepted."
    : el("source").value === acceptedSource && el("packages").value === acceptedPackages ? "Graph and output match the current sources."
      : "Showing the previous successful graph and output, NOT the current source.";
}
function nodeLabel(node) {
  if (node.token) return node.text;
  if (["name", "integer", "boolean"].includes(node.kind)) {
    const token = graphData().nodes.find(candidate => candidate.id === node.children[0]);
    return `${node.kind}: ${token.text}`;
  }
  if (node.kind === "binary" || (node.kind === "unary" && node.children.length === 2)) {
    const operator = graphData().nodes.find(candidate => candidate.id === node.children[node.kind === "binary" ? 1 : 0]);
    return `${node.kind}: ${operator.text}`;
  }
  return node.kind;
}
function select(id) {
  selected = id;
  const node = graphData().nodes.find(node => node.id === id);
  if (!node) throw new Error("Missing selected graph node");
  el("inspector-title").textContent = `n${node.id} / ${node.kind} / position ${node.position}`;
  el("kind").textContent = node.token ? `Token.${node.kind}` : `Composer.${node.kind}`;
  el("location").textContent = `${node.line}:${node.column}`;
  el("value").textContent = node.text === null ? "vacant (None)" : JSON.stringify(node.text);
  el("bytes").textContent = node.value === null ? "None" : JSON.stringify(node.value);
  el("type").textContent = node.type || "Not a typed expression";
  el("constraints").textContent = [
    node.const ? "const" : "", node.constructor === true ? `${node.unnamed === true ? "unnamed " : ""}constructor` : "",
    node.sort !== undefined ? `Sort(${node.sort})` : "", node.dependent ? "dependent fields" : "",
    node.generator === true ? "proposition generator -> Prop" : "",
    node.evidenceTarget ? `evidence target: ${node.evidenceTarget}` : "",
    node.static === true ? "class static function" : "",
    node.contract === true ? "named TypeDef contract implementation" : "",
    node.alias === true ? `TypeDef ${node.name} = ${node.definition} (no runtime storage)` : "",
    node.formalCheck === true ? "formally checked without execution" : "",
  ].filter(Boolean).join(" / ") || "None";
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
  const data = graphData();
  const nodes = data.nodes.filter(node => all || (!node.token && node.kind !== "TokenSequence"));
  drawNodGraph(el("graph"), nodes, {
    label: nodeLabel, final: data.final, selected, onSelect: select,
  });
  select(selected);
}
function render() {
  el("result-heading").textContent = accepted.theory ? "Type-theory judgments" : "Execution output";
  el("output").textContent = accepted.output.length ? accepted.output.join("\n") : "(no print output)";
  el("variables").replaceChildren();
  for (const [name, value] of Object.entries(accepted.variables)) {
    const span = document.createElement("span"); span.textContent = `${name} = ${typeof value === "object" && value !== null ? value.nil ? `${value.type}(nil) [object ${value.object}]` : JSON.stringify(value) : value}`; el("variables").append(span);
  }
  if (!Object.keys(accepted.variables).length) el("variables").textContent = "None";
  el("functions").replaceChildren();
  for (const fn of accepted.functions) {
    const span = document.createElement("span");
    const result = fn.generator === true ? "Prop / Sort(0)" : fn.procedure === true ? "[no result]" : fn.returns;
    const role = fn.generator === true ? `${fn.unnamed === true ? "unnamed " : ""}proposition generator`
      : fn.constructor === true ? `${fn.unnamed === true ? "unnamed " : ""}constructor`
        : fn.contract === true ? "named TypeDef contract" : fn.procedure === true ? `${fn.static ? "static " : ""}procedure` : fn.static === true ? "class static function" : fn.implicit ? "implicit shallow copy" : "instance method";
    span.textContent = `${fn.name}(${fn.parameters.map(([name, type]) => `${name}:${type}`).join(", ")}) ${result} [${role}]`;
    el("functions").append(span);
  }
  if (!accepted.functions.length) el("functions").textContent = "None";
  el("classes").replaceChildren();
  for (const classInfo of accepted.classes || []) {
    const span = document.createElement("span");
    span.textContent = `${classInfo.name}${classInfo.evidenceTarget ? ` -> ${classInfo.evidenceTarget} [evidence specification]` : `:Sort(${classInfo.sort})`} { ${classInfo.fields.map(field => `${field.const ? "const " : ""}${field.name}:${field.type}`).join("; ")} }${classInfo.constructors.length ? ` / constructors: ${classInfo.constructors.join(", ")}` : ""}`;
    if (classInfo.aliases?.length)
      span.textContent += ` / checked aliases (no storage): ${classInfo.aliases.map(alias => `${alias.public ? "public " : ""}TypeDef ${alias.name}:${alias.type}`).join("; ")}`;
    el("classes").append(span);
  }
  if (!accepted.classes?.length) el("classes").textContent = "None";
  el("propositions").replaceChildren();
  for (const proposition of accepted.generatedPropositions || []) {
    const span = document.createElement("span");
    const fields = Object.entries(proposition.fields).map(([name, value]) => `${name}:${value}`).join("; ");
    span.textContent = `${proposition.type}:Prop / Sort(${proposition.sort}) / schema: ${proposition.schema} { ${fields} } / evidence specifications: ${proposition.evidenceSpecifications.join(", ") || "None"}`;
    if (proposition.aliases?.length)
      span.textContent += ` / specialized type aliases (not values): ${proposition.aliases.map(alias => `${alias.name}:${alias.type}`).join("; ")}`;
    el("propositions").append(span);
  }
  if (!accepted.generatedPropositions?.length) el("propositions").textContent = "None";
  el("objects").textContent = accepted.objects?.length ? JSON.stringify(accepted.objects, null, 2) : "No runtime class objects.";
  el("package-graph").replaceChildren();
  for (const name of Object.keys(accepted.packageGraphs || {"": accepted})) {
    const option = document.createElement("option"); option.value = name; option.textContent = name || "(default)";
    el("package-graph").append(option);
  }
  el("package-graph").value = accepted.package || "";
  renderGraph(); provenance();
}
function renderGraph() {
  const data = graphData();
  selected = data.final;
  el("metrics").textContent = `${data.tokens.length} token occurrences / ${data.nodes.length} source graph nodes / ${accepted.theory ? `${accepted.theory.nodes.length} type-expression nodes` : `${accepted.steps} execution steps`} / final n${data.final}`;
  el("tokens").replaceChildren(); el("array").replaceChildren();
  for (const node of data.nodes) {
    const cell = document.createElement("li"), position = document.createElement("span"), button = document.createElement("button");
    cell.dataset.node = node.id; position.textContent = node.position; button.type = "button";
    button.textContent = node.id === 0 ? "root" : `n${node.id}`; button.className = node.id === data.final ? "final" : "";
    button.addEventListener("click", () => select(node.id)); cell.append(position, button); el("array").append(cell);
  }
  for (const [index, id] of data.tokens.entries()) {
      const node = data.nodes.find(node => node.id === id), position = data.occurrences[index];
      const occurrence = document.createElement("li"), tokenButton = document.createElement("button"), category = document.createElement("b"), text = document.createElement("span");
      occurrence.dataset.node = node.id; occurrence.dataset.occurrence = index; tokenButton.type = "button"; category.textContent = node.kind; text.textContent = node.text;
      tokenButton.append(category, text); tokenButton.title = `Occurrence ${index}: n${id} at ${position.line}:${position.column}`;
      tokenButton.addEventListener("click", () => select(node.id)); occurrence.append(tokenButton); el("tokens").append(occurrence);
  }
  el("graph-empty").hidden = true; draw(); provenance();
}
async function build() {
  clearTimeout(timer);
  controller?.abort();
  controller = new AbortController();
  const own = ++generation, source = el("source").value, packageText = el("packages").value;
  status("pending", "Tokenize -> compose -> check -> execute...");
  provenance();
  try {
    const packages = JSON.parse(packageText);
    const response = await fetch("/api/run", {method: "POST", headers: {"Content-Type": "application/json"}, body: JSON.stringify({source, packages}), signal: controller.signal});
    const result = await response.json();
    if (own !== generation || source !== el("source").value || packageText !== el("packages").value) return;
    if (!response.ok || !result.ok) {
      const error = result.error;
      status("error", `${error.stage || "request"}${error.line ? ` at ${error.line}:${error.column}` : ""}: ${error.message}\nProposal rejected. Previous successful results are unchanged.`);
      provenance(); return;
    }
    accepted = result; acceptedSource = source; acceptedPackages = packageText; selected = result.final;
    render(); status("success", result.theory
      ? "Accepted: type-theory declarations and annotations checked. No imperative execution was performed."
      : "Accepted: syntax, semantic checks, and execution succeeded.");
  } catch (error) {
    if (error.name === "AbortError" || own !== generation) return;
    status("error", `Cannot complete the request: ${error.message}. Check that the local Nod server is running.`);
    provenance();
  }
}
function sourceChanged() {
  clearTimeout(timer); controller?.abort(); generation++; provenance();
  status("pending", el("auto").checked ? "Source changed; waiting to build..." : "Source changed. Click Build & run.");
  if (el("auto").checked) timer = setTimeout(build, 500);
}
el("source").addEventListener("input", sourceChanged);
el("packages").addEventListener("input", sourceChanged);
el("source").addEventListener("keydown", event => { if ((event.ctrlKey || event.metaKey) && event.key === "Enter") { event.preventDefault(); build(); } });
el("run").addEventListener("click", build);
el("show-tokens").addEventListener("change", draw);
el("auto").addEventListener("change", () => { clearTimeout(timer); if (el("auto").checked) build(); });
el("package-graph").addEventListener("change", renderGraph);
async function loadExample() {
  try {
    const response = await fetch("/example.nod");
    if (!response.ok) throw new Error(`Example request failed (${response.status})`);
    el("source").value = await response.text(); el("packages").value = "{}"; await build();
  } catch (error) { status("error", `Cannot load example: ${error.message}`); }
}
el("example").addEventListener("click", loadExample);
el("dependent-example").addEventListener("click", async () => {
  try {
    const response = await fetch("/dependent_example.nod");
    if (!response.ok) throw new Error(`Example request failed (${response.status})`);
    el("source").value = await response.text(); el("packages").value = "{}"; await build();
  } catch (error) { status("error", `Cannot load dependent-classInfo example: ${error.message}`); }
});
el("proposition-example").addEventListener("click", async () => {
  try {
    const response = await fetch("/proposition_example.nod");
    if (!response.ok) throw new Error(`Example request failed (${response.status})`);
    el("source").value = await response.text(); el("packages").value = "{}"; await build();
  } catch (error) { status("error", `Cannot load proposition/evidence example: ${error.message}`); }
});
el("package-example").addEventListener("click", async () => {
  try {
    const response = await fetch("/package_example.json");
    if (!response.ok) throw new Error(`Example request failed (${response.status})`);
    const example = await response.json();
    el("source").value = example.source; el("packages").value = JSON.stringify(example.packages, null, 2);
    el("packages").closest("details").open = true; await build();
  } catch (error) { status("error", `Cannot load package example: ${error.message}`); }
});
loadExample();
