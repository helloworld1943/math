"use strict";
function drawNodGraph(graph, nodes, {label, final, selected, onSelect}) {
  const element = (tag, attrs = {}, text = null) => {
    const node = document.createElementNS("http://www.w3.org/2000/svg", tag);
    for (const [key, value] of Object.entries(attrs)) node.setAttribute(key, String(value));
    if (text !== null) node.textContent = text;
    return node;
  };
  const visible = new Set(nodes.map(node => node.id)), depths = new Map(), layers = new Map(), layout = new Map();
  for (const node of nodes) {
    const targets = node.outputs.filter(target => target !== null && visible.has(target));
    const depth = targets.length ? 1 + Math.max(...targets.map(target => depths.get(target))) : 0;
    depths.set(node.id, depth);
    if (!layers.has(depth)) layers.set(depth, []);
    layers.get(depth).push(node.id);
  }
  const heights = new Map(nodes.map(node => [node.id, Math.max(56, node.outputs.filter(target => visible.has(target)).length * 12 + 16)]));
  const height = Math.max(280, ...[...layers.values()].map(ids => ids.reduce((sum, id) => sum + heights.get(id) + 32, 30)));
  const width = Math.max(650, layers.size * 185 + 30);
  for (const [depth, ids] of layers) {
    const total = ids.reduce((sum, id) => sum + heights.get(id) + 32, 0);
    let y = (height - total) / 2;
    for (const id of ids) {
      layout.set(id, [90 + depth * 185, y + heights.get(id) / 2 + 16]);
      y += heights.get(id) + 32;
    }
  }
  graph.replaceChildren();
  graph.setAttribute("viewBox", `0 0 ${width} ${height}`);
  graph.setAttribute("width", width); graph.setAttribute("height", height);
  const arrowId = `${graph.id}-arrow`;
  const defs = element("defs"), marker = element("marker", {id: arrowId, markerWidth: 7, markerHeight: 7, refX: 6, refY: 3.5, orient: "auto"});
  marker.append(element("path", {d: "M0 0 L7 3.5 L0 7 Z", fill: "#729c86"}));
  defs.append(marker); graph.append(defs);
  for (const node of nodes) {
    const targets = node.outputs.map((target, slot) => [target, slot]).filter(([target]) => target !== null && visible.has(target));
    targets.forEach(([target, slot], n) => {
      const [x, y] = layout.get(node.id), [tx, ty] = layout.get(target);
      const start = x - 68, end = tx + 68, curve = (start + end) / 2, port = y + (n - (targets.length - 1) / 2) * 12;
      graph.append(element("path", {d: `M${start} ${port} C${curve} ${port} ${curve} ${ty} ${end} ${ty}`, class: `edge${slot === 0 ? " context" : ""}`, "marker-end": `url(#${arrowId})`, "data-source": node.id, "data-target": target, "data-slot": slot}));
      graph.append(element("text", {x: start - 11, y: port + 3, class: "edge-label"}, slot));
    });
  }
  for (const node of nodes) {
    const [x, y] = layout.get(node.id), h = heights.get(node.id);
    const caption = label(node), short = caption.length > 21 ? caption.slice(0, 18) + "..." : caption;
    const group = element("g", {class: `node${node.token ? " token" : ""}${node.id === final ? " final" : ""}${node.id === selected ? " selected" : ""}`, transform: `translate(${x} ${y})`, "data-node": node.id, tabindex: 0, role: "button", "aria-label": `Inspect n${node.id}, ${caption}`});
    group.append(element("title", {}, caption), element("rect", {x: -66, y: -h / 2, width: 132, height: h, rx: 8}), element("text", {y: -7}, `n${node.id}${node.id === final ? " / final" : ""}`), element("text", {y: 13, class: "small"}, short));
    group.addEventListener("click", () => onSelect(node.id));
    group.addEventListener("keydown", event => { if (["Enter", " "].includes(event.key)) { event.preventDefault(); onSelect(node.id); } });
    graph.append(group);
  }
}
