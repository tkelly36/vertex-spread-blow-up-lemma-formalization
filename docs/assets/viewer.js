
let tablet = null;
let nodeNames = [];
let activeNode = "";
const BUILD_INFO_ROUTE = "build-info";

const $ = (id) => document.getElementById(id);

function escapeHtml(value) {
  return String(value || "")
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#39;");
}

function nodeExists(name) {
  return tablet && tablet.nodes && Object.prototype.hasOwnProperty.call(tablet.nodes, name);
}

function nodeHref(name) {
  return `#${encodeURIComponent(name)}`;
}

function kindBadge(kind) {
  return `<span class="badge">${escapeHtml(kind || "node")}</span>`;
}

function nodeLink(name, extraClass = "") {
  const node = tablet.nodes[name];
  const active = name === activeNode ? " active" : "";
  return `<a class="node-link${active} ${extraClass}" href="${nodeHref(name)}"><span class="node-name">${escapeHtml(name)}</span>${kindBadge(node ? node.kind : "")}</a>`;
}

function compactNodeAnchor(name) {
  const active = name === activeNode ? " active" : "";
  return `<a class="${active}" href="${nodeHref(name)}">${escapeHtml(name)}</a>`;
}

function renderNodeReferences(escaped) {
  return escaped.replace(/\\noderef\{([A-Za-z0-9_']+)\}/g, (_m, name) => {
    if (!nodeExists(name)) return `<span class="missing-ref">${escapeHtml(name)}</span>`;
    return `<a class="node-ref" href="${nodeHref(name)}">${escapeHtml(name)}</a>`;
  });
}

function stripOuterEnv(raw) {
  const text = String(raw || "").trim();
  const match = text.match(/^\\begin\{([A-Za-z*]+)\}(?:\[[^\]]*\])?([\s\S]*)\\end\{\1\}$/);
  if (!match) return { env: "", body: text };
  return { env: match[1], body: match[2].trim() };
}

function stripLatexLabels(text) {
  return String(text || "").replace(/\\label\{[^{}]*\}/g, "");
}

function renderTextChunk(text) {
  const tokens = [];
  const protect = (html) => {
    const key = `%%TRELLIS_HTML_TOKEN_${tokens.length}%%`;
    tokens.push(html);
    return key;
  };
  let source = stripLatexLabels(text);
  source = source
    .replace(/\\noderef\{([A-Za-z0-9_']+)\}/g, (_m, name) => {
      if (!nodeExists(name)) return protect(`<span class="missing-ref">${escapeHtml(name)}</span>`);
      return protect(`<a class="node-ref" href="${nodeHref(name)}">${escapeHtml(name)}</a>`);
    })
    .replace(/\\(?:emph|textit)\{([^{}]*)\}/g, (_m, inner) => protect(`<em>${escapeHtml(inner)}</em>`))
    .replace(/\\textbf\{([^{}]*)\}/g, (_m, inner) => protect(`<strong>${escapeHtml(inner)}</strong>`))
    .replace(/\\'([A-Za-z])/g, (_m, letter) => {
      const accents = {
        a: "&aacute;", e: "&eacute;", i: "&iacute;", o: "&oacute;", u: "&uacute;", y: "&yacute;",
        A: "&Aacute;", E: "&Eacute;", I: "&Iacute;", O: "&Oacute;", U: "&Uacute;", Y: "&Yacute;"
      };
      return protect(accents[letter] || escapeHtml(letter));
    })
    .replace(/``/g, '"')
    .replace(/''/g, '"')
    .replace(/\\([%&_#$])/g, "$1")
    .replace(/~/g, " ");
  let escaped = escapeHtml(source);
  tokens.forEach((html, index) => {
    escaped = escaped.replaceAll(`%%TRELLIS_HTML_TOKEN_${index}%%`, html);
  });
  return escaped;
}

function renderInlineTexContent(text) {
  const parts = String(text || "").split(/(\\\([\s\S]*?\\\))/g);
  return parts.map((part) => {
    if (!part) return "";
    if (part.startsWith("\\(") && part.endsWith("\\)")) {
      return escapeHtml(part);
    }
    const collapsed = part.replace(/\s*\n\s*/g, " ");
    return renderTextChunk(collapsed);
  }).join("");
}

function normalizeDisplayMath(text) {
  return stripLatexLabels(text).replace(
    /(\\begin\{aligned\})([\s\S]*?)(\\tag\{[^}]+\})(\s*\\end\{aligned\})/g,
    (_match, begin, body, tag, end) => `${begin}${body}${end}${tag}`
  );
}

function renderTexParagraphs(body) {
  const parts = String(body || "").split(/(\\\[[\s\S]*?\\\])/g);
  return parts.map((part) => {
    if (!part || !part.trim()) return "";
    if (part.startsWith("\\[") && part.endsWith("\\]")) {
      return `<div class="math-block">${escapeHtml(normalizeDisplayMath(part))}</div>`;
    }
    return part
      .split(/\n\s*\n/g)
      .map((paragraph) => paragraph.trim())
      .filter(Boolean)
      .map((paragraph) => `<p>${renderInlineTexContent(paragraph)}</p>`)
      .join("");
  }).join("");
}

function splitLatexItems(body) {
  const matches = Array.from(String(body || "").matchAll(/\\item(?:\[[^\]]*\])?/g));
  if (!matches.length) return [];
  return matches.map((match, index) => {
    const start = match.index + match[0].length;
    const end = index + 1 < matches.length ? matches[index + 1].index : body.length;
    return body.slice(start, end).trim();
  }).filter(Boolean);
}

function renderLatexList(env, body) {
  const tag = env === "enumerate" ? "ol" : "ul";
  const items = splitLatexItems(body);
  if (!items.length) return renderTexParagraphs(body);
  return `<${tag} class="latex-list">${items.map((item) => `<li>${renderTexBody(item)}</li>`).join("")}</${tag}>`;
}

function renderTexBody(body) {
  const text = stripLatexLabels(body);
  const pattern = /\\begin\{(enumerate|itemize)\}(?:\[[^\]]*\])?([\s\S]*?)\\end\{\1\}/g;
  let html = "";
  let lastIndex = 0;
  let match = null;
  while ((match = pattern.exec(text)) !== null) {
    html += renderTexParagraphs(text.slice(lastIndex, match.index));
    html += renderLatexList(match[1], match[2]);
    lastIndex = match.index + match[0].length;
  }
  html += renderTexParagraphs(text.slice(lastIndex));
  return html;
}

function renderTex(raw) {
  if (!raw || !raw.trim()) return `<div class="empty">No TeX content.</div>`;
  const { env, body } = stripOuterEnv(raw);
  const rendered = renderTexBody(body);
  const title = env ? `<div class="tex-env-title">${escapeHtml(env[0].toUpperCase() + env.slice(1))}</div>` : "";
  return `<div class="tex-render">${title}<div class="tex-body">${rendered || renderInlineTexContent(body)}</div></div>`;
}

// Matches one Lean identifier, including namespace dots and the unicode
// letters/digits/subscripts Lean allows, so a linkable ASCII node name is
// never matched as a mere prefix of a longer identifier (e.g. `Hole₁`).
const LEAN_IDENT_RE = /[\p{L}_][\p{L}\p{N}_']*(?:\.[\p{L}_][\p{L}\p{N}_']*)*/gu;

// Linkify node names in raw (unescaped) Lean text. Working on the raw text
// and escaping segment-by-segment sidesteps the escapeHtml quirk that a
// prime in an identifier becomes `&#39;` in escaped text. Only whole
// identifier tokens (or the leading segment of a dotted token, for
// references like `NodeName.aux`) are linked, so node names that are
// prefixes of other names never match inside them.
function linkifyLean(raw, linkNames) {
  const text = String(raw);
  let html = "";
  let last = 0;
  for (const match of text.matchAll(LEAN_IDENT_RE)) {
    const token = match[0];
    html += escapeHtml(text.slice(last, match.index));
    last = match.index + token.length;
    let target = "";
    if (linkNames.has(token)) {
      target = token;
    } else {
      const head = token.split(".", 1)[0];
      if (head !== token && linkNames.has(head)) target = head;
    }
    if (target) {
      const rest = token.slice(target.length);
      html += `<a class="lean-ref" href="${nodeHref(target)}">${escapeHtml(target)}</a>${escapeHtml(rest)}`;
    } else {
      html += escapeHtml(token);
    }
  }
  html += escapeHtml(text.slice(last));
  return html;
}

// `linkNames` (a Set of node names) is only passed for node Lean content
// (statements/proofs); #print axioms output, stderr, and build-info TOML
// call this without it and stay unlinkified.
function renderLean(raw, linkNames) {
  if (!raw || !raw.trim()) return `<div class="empty">No Lean content.</div>`;
  const body = linkNames && linkNames.size
    ? linkifyLean(raw, linkNames)
    : escapeHtml(raw);
  return `<pre><code>${body}</code></pre>`;
}

// Long pill rows (a heavily-used lemma is imported by hundreds of nodes)
// collapse behind a "+N more" toggle so the page head stays readable.
const PILL_LIMIT = 24;

function pillRow(labelHtml, pills) {
  if (!pills.length) return "";
  const head = pills.slice(0, PILL_LIMIT).join("");
  const rest = pills.slice(PILL_LIMIT);
  const restHtml = rest.length
    ? `<span class="pill-rest" hidden>${rest.join("")}</span><button type="button" class="pill pill-more">+${rest.length} more</button>`
    : "";
  return `<div class="links-row">${labelHtml}${head}${restHtml}</div>`;
}

function nodePillAnchors(names) {
  return (names || []).filter(nodeExists).map((name) => `<a class="pill" href="${nodeHref(name)}">${escapeHtml(name)}</a>`);
}

function renderLinks(label, names) {
  const pills = nodePillAnchors(names);
  if (!pills.length) return "";
  return pillRow(`<span class="pill pill-label">${escapeHtml(label)}</span>`, pills);
}

function renderNodePills(names) {
  return pillRow("", nodePillAnchors(names));
}

function renderTextPills(names) {
  const filtered = (names || []).filter(Boolean);
  if (!filtered.length) return "";
  return `<div class="links-row">${filtered.map((name) => `<span class="pill">${escapeHtml(name)}</span>`).join("")}</div>`;
}

function mathlibDocsUrl(moduleName) {
  return `https://leanprover-community.github.io/mathlib4_docs/${encodeURIComponent(moduleName).replaceAll(".", "/")}.html`;
}

function renderMathlibPills(names) {
  const pills = (names || []).filter(Boolean).map((name) => `<a class="pill" href="${mathlibDocsUrl(name)}" target="_blank" rel="noopener">${escapeHtml(name)}</a>`);
  return pillRow("", pills);
}

function renderInfoTable(rows) {
  const body = rows
    .filter((row) => row && row.length === 2)
    .map(([label, value]) => `<tr><th>${escapeHtml(label)}</th><td>${value}</td></tr>`)
    .join("");
  return `<table class="info-table"><tbody>${body}</tbody></table>`;
}

function renderInlineCode(value) {
  return `<code>${escapeHtml(value || "")}</code>`;
}

function renderStringList(items) {
  const filtered = (items || []).filter(Boolean);
  if (!filtered.length) return `<span class="empty">None</span>`;
  return `<ul class="build-info-list">${filtered.map((item) => `<li>${renderInlineCode(item)}</li>`).join("")}</ul>`;
}

function extractNodeReferences(text) {
  const refs = [];
  const pattern = /\\noderef\{([A-Za-z0-9_']+)\}/g;
  let match = null;
  while ((match = pattern.exec(String(text || ""))) !== null) {
    refs.push(match[1]);
  }
  return refs;
}

function directDependencies(node) {
  const seen = new Set();
  const add = (name) => {
    if (name && name !== node.name && nodeExists(name)) seen.add(name);
  };
  (node.imports || []).forEach(add);
  extractNodeReferences(node.tex_statement).forEach(add);
  extractNodeReferences(node.tex_proof).forEach(add);
  return Array.from(seen).sort((a, b) => a.localeCompare(b));
}

function renderSemanticClosureNote() {
  return `
    <div class="closure-note">
      <p>These are the additional nodes whose statements must be read to verify that the Lean statement of this node genuinely corresponds to its claimed natural-language mathematical meaning. This list is generated by Trellis's Lean semantic-payload walk: starting at the node's Lean declaration, theorem/axiom/etc. types are walked, definition types and values are walked, inductive types and constructors are walked, theorem proof bodies are not walked, external Mathlib constants stop at the boundary, and generated constants are collapsed to their top-level tablet node.</p>
    </div>
  `;
}

function renderSourceLinks(node) {
  const links = [];
  if (node.github_tex_url) links.push(`<a href="${escapeHtml(node.github_tex_url)}">TeX source</a>`);
  if (node.github_lean_url) links.push(`<a href="${escapeHtml(node.github_lean_url)}">Lean source</a>`);
  return links.join("");
}

function renderNodePanel(name, opts = {}) {
  const node = tablet.nodes[name];
  if (!node) return "";
  const header = opts.root
    ? ""
    : `<div class="node-panel-header"><h3><a href="${nodeHref(name)}">${escapeHtml(name)}</a></h3>${kindBadge(node.kind)}</div>`;
  const isDefinition = node.kind === "definition";
  // Node names cited by this node's Lean text link to their nodes. The safe
  // link set is the node's Tablet imports: exactly what the Lean is entitled
  // to cite, and already filtered to names that exist as nodes.
  const leanLinkNames = new Set((node.imports || []).filter(nodeExists));
  const leanMain = isDefinition && node.lean_proof
    ? `${node.lean_statement}\n-- BODY\n${node.lean_proof}`
    : node.lean_statement;
  const texHeading = isDefinition ? "TeX Definition" : "TeX Statement";
  const leanHeading = isDefinition ? "Lean Definition" : "Lean Statement";
  const leanProofLines = node.lean_proof ? node.lean_proof.split("\n").length : 0;
  const proofMetaParts = [];
  if (node.tex_proof) proofMetaParts.push("natural language");
  if (node.lean_proof) proofMetaParts.push(`Lean, ${leanProofLines} line${leanProofLines === 1 ? "" : "s"}`);
  const proofMeta = proofMetaParts.length
    ? `<span class="proof-summary-meta">${escapeHtml(proofMetaParts.join(" + "))}</span>`
    : "";
  // One disclosure for both proof registers: on a wide screen they sit in
  // side-by-side columns (each capped to the viewport and independently
  // scrollable, so Lean and natural language can be read against each
  // other); on a narrow screen the columns stack via the .subgrid rules.
  const proofBlocks = isDefinition ? "" : `
      <details class="proof"${opts.openProofs ? " open" : ""}>
        <summary>Proof${proofMeta}</summary>
        <div class="subgrid proof-columns">
          <section class="block">
            <h4>Natural-Language Proof</h4>
            ${renderTex(node.tex_proof)}
          </section>
          <section class="block">
            <h4>Lean Proof</h4>
            ${renderLean(node.lean_proof, leanLinkNames)}
          </section>
        </div>
      </details>
  `;
  return `
    <article class="node-panel" id="panel-${escapeHtml(name)}">
      ${header}
      <div class="subgrid">
        <section class="block">
          <h4>${texHeading}</h4>
          ${renderTex(node.tex_statement)}
        </section>
        <section class="block">
          <h4>${leanHeading}</h4>
          ${renderLean(leanMain, leanLinkNames)}
        </section>
      </div>
      ${proofBlocks}
    </article>
  `;
}

function renderBuildInfo() {
  activeNode = BUILD_INFO_ROUTE;
  const info = tablet.build_info || {};
  const source = info.source || {};
  const trellis = info.trellis || {};
  const lean = info.lean || {};
  const axioms = info.axioms || {};
  const approved = axioms.approved_axioms || {};
  const packages = lean.packages || [];
  const directPackages = packages.filter((pkg) => !pkg.inherited);
  const inheritedPackages = packages.filter((pkg) => pkg.inherited);
  const probes = axioms.print_axioms || [];
  document.title = `Build Info - ${tablet.title}`;
  const renderPackageRows = (items) => items.length
    ? `<table class="info-table"><thead><tr><th>Package</th><th>Revision</th></tr></thead><tbody>${items.map((pkg) => {
        const name = pkg.scope ? `${pkg.scope}/${pkg.name}` : pkg.name;
        const url = pkg.url ? `<a href="${escapeHtml(pkg.url)}" target="_blank" rel="noopener">${escapeHtml(name)}</a>` : escapeHtml(name);
        return `<tr><th>${url}</th><td>${renderInlineCode(pkg.rev || "")}</td></tr>`;
      }).join("")}</tbody></table>`
    : `<p class="empty">No package pins in this group.</p>`;
  const probeBlocks = probes.length
    ? probes.map((probe) => `
        <article class="node-panel">
          <div class="node-panel-header"><h3>${escapeHtml(probe.declaration || "")}</h3>${kindBadge("print axioms")}</div>
          ${renderLean(probe.stdout || "No #print axioms output recorded.")}
          ${probe.stderr ? `<h4>stderr</h4>${renderLean(probe.stderr)}` : ""}
        </article>
      `).join("")
    : `<p class="empty">No #print axioms probes were recorded.</p>`;
  $("mainContent").innerHTML = `
    <header class="node-header">
      <div>
        <h2>Build Info</h2>
        <div class="meta-line">
          <span>public tablet viewer</span>
          <span>${escapeHtml((tablet.targets || []).length)} paper targets</span>
        </div>
      </div>
      <div class="source-links"><a href="data/build-info.toml" target="_blank" rel="noopener">Raw TOML</a></div>
    </header>
    <section class="block">
      <h4>Source</h4>
      ${renderInfoTable([
        ["Git remote", escapeHtml(source.git_remote || "")],
        ["Git branch", escapeHtml(source.git_branch || "")],
        ["Git commit", renderInlineCode(source.git_commit || "")],
        ["Git dirty", escapeHtml(String(Boolean(source.git_dirty)))],
        ["GitHub base", source.github_base ? `<a href="${escapeHtml(source.github_base)}" target="_blank" rel="noopener">${escapeHtml(source.github_base)}</a>` : ""],
      ])}
    </section>
    <section class="block">
      <h4>Lean Build Chain</h4>
      ${renderInfoTable([
        ["Toolchain", renderInlineCode(lean.toolchain || "")],
        ["Lean version", renderInlineCode(lean.lean_version || "")],
        ["Lake version", renderInlineCode(lean.lake_version || "")],
        ["lake-manifest SHA-256", renderInlineCode(lean.lake_manifest_sha256 || "")],
        ["lakefile SHA-256", renderInlineCode(lean.lakefile_sha256 || "")],
      ])}
      <p>The tablet project's Lake file directly requires only the package pins in the first table. The inherited package pins are pulled in by dependencies such as Mathlib; they are recorded as part of the reproducible Lake build chain, but this is not a claim that the tablet imports or uses those packages directly.</p>
      <h4>Direct Lake Dependencies</h4>
      ${renderPackageRows(directPackages)}
      <h4>Inherited Lake Package Pins</h4>
      ${renderPackageRows(inheritedPackages)}
    </section>
    <section class="block">
      <h4>Trellis Export Chain</h4>
      ${renderInfoTable([
        ["Trellis commit", renderInlineCode(trellis.git_commit || "")],
        ["Trellis dirty", escapeHtml(String(Boolean(trellis.git_dirty)))],
        ["Exporter SHA-256", renderInlineCode(trellis.exporter_sha256 || "")],
        ["Semantic script SHA-256", renderInlineCode(trellis.semantic_fingerprint_script_sha256 || "")],
      ])}
    </section>
    <section class="block">
      <h4>Axiom Policy</h4>
      <p>${escapeHtml(axioms.probe_description || "")}</p>
      ${renderInfoTable([
        ["Default allowed axioms", renderStringList(axioms.default_allowed_axioms || [])],
        ["Approved axioms file", escapeHtml(approved.present ? `${approved.path || "APPROVED_AXIOMS.json"} (${approved.empty ? "empty" : "nonempty"})` : "not present")],
        ["Project-approved axioms", renderStringList(approved.global || [])],
        ["Effective allowed axioms", renderStringList(axioms.allowed_axioms || [])],
      ])}
      ${probeBlocks}
    </section>
    <section class="block">
      <h4>Raw TOML</h4>
      ${renderLean(info.toml || "")}
    </section>
  `;
  renderSidebar();
  $("mainContent").focus({ preventScroll: true });
}

function renderMain(name) {
  if (name === BUILD_INFO_ROUTE) {
    renderBuildInfo();
    return;
  }
  const node = tablet.nodes[name] || tablet.nodes[nodeNames[0]];
  if (!node) {
    $("mainContent").innerHTML = `<div class="warning">No nodes found.</div>`;
    return;
  }
  activeNode = node.name;
  document.title = `${node.name} - ${tablet.title}`;
  const closure = (node.semantic_closure || []).filter(nodeExists);
  const deps = directDependencies(node);
  const mathlibImports = node.mathlib_imports || [];
  const closureItems = closure.length
    ? closure.map((dep) => renderNodePanel(dep)).join("")
    : `<p class="empty">The semantic closure of this node has no additional tablet nodes.</p>`;
  const closureWarning = node.semantic_closure_error
    ? `<p class="warning">${escapeHtml(node.semantic_closure_error)}</p>`
    : "";
  $("mainContent").innerHTML = `
    <header class="node-header">
      <div>
        <h2>${escapeHtml(node.name)}</h2>
        <div class="meta-line">
          <span>${escapeHtml(node.kind || "node")}</span>
          ${node.is_target ? "<span>paper target</span>" : ""}
          <span>uses ${(node.imports || []).length} nodes</span>
          <span>used by ${(node.imported_by || []).length} nodes</span>
          <span>${closure.length} semantic-closure nodes</span>
        </div>
      </div>
      <div class="source-links">${renderSourceLinks(node)}</div>
    </header>
    ${renderLinks("Uses", node.imports)}
    ${renderLinks("Used by", node.imported_by)}
    ${renderNodePanel(node.name, { root: true })}
    <h2 class="section-title">Semantic Closure</h2>
    ${renderSemanticClosureNote()}
    ${closureWarning}
    ${renderNodePills(closure)}
    ${closureItems}
    <h2 class="section-title">Tablet Dependencies</h2>
    ${renderNodePills(deps) || `<p class="empty">This node has no direct tablet dependencies.</p>`}
    <h2 class="section-title">Mathlib</h2>
    ${renderMathlibPills(mathlibImports) || `<p class="empty">No Mathlib imports appear in this node's recursive tablet import closure.</p>`}
  `;
  renderSidebar();
  const activeLink = document.querySelector("#allNodeList .node-link.active");
  if (activeLink && activeLink.scrollIntoView) activeLink.scrollIntoView({ block: "nearest" });
  if (window.MathJax && window.MathJax.typesetPromise) {
    window.MathJax.typesetPromise([$("mainContent")]).catch(() => {});
  }
  $("mainContent").focus({ preventScroll: true });
}

function buildTree(root) {
  const seen = new Set();
  function walk(name) {
    const node = tablet.nodes[name];
    if (!node) return "";
    const repeated = seen.has(name);
    seen.add(name);
    const children = repeated ? [] : (node.imports || []).filter(nodeExists);
    return `<li class="${repeated ? "repeated" : ""}">${compactNodeAnchor(name)}${children.length ? `<ul>${children.map(walk).join("")}</ul>` : ""}</li>`;
  }
  return `<ul class="tree">${walk(root)}</ul>`;
}

function renderSidebar() {
  $("siteTitle").textContent = tablet.title || "Trellis Tablet";
  const buildLink = $("buildInfoLink");
  if (buildLink) {
    buildLink.classList.toggle("active", activeNode === BUILD_INFO_ROUTE);
  }
  $("targetList").innerHTML = (tablet.targets || [])
    .filter((target) => nodeExists(target.node))
    .map((target) => {
      const active = target.node === activeNode ? " active" : "";
      const label = target.label ? `<span class="badge">${escapeHtml(target.label)}</span>` : kindBadge(tablet.nodes[target.node].kind);
      return `<a class="target-link${active}" href="${nodeHref(target.node)}"><span class="node-name">${escapeHtml(target.node)}</span>${label}</a>`;
    })
    .join("");

  $("dependencyOutline").innerHTML = (tablet.targets || [])
    .filter((target) => nodeExists(target.node))
    .map((target) => {
      const open = "";
      const label = target.label ? ` <span class="badge">${escapeHtml(target.label)}</span>` : "";
      return `<details${open}><summary>${escapeHtml(target.node)}${label}</summary>${buildTree(target.node)}</details>`;
    })
    .join("");

  const query = $("nodeSearch").value.trim().toLowerCase();
  const counter = $("nodeCount");
  if (!query) {
    if (counter) counter.textContent = `${nodeNames.length} nodes`;
    $("allNodeList").innerHTML = nodeNames.map((name) => nodeLink(name)).join("");
    return;
  }
  const { nameHits, textHits } = searchMatches(query);
  if (counter) counter.textContent = `${nameHits.length + textHits.length} of ${nodeNames.length} nodes`;
  const divider = textHits.length
    ? `<div class="list-divider">statement matches</div>`
    : "";
  $("allNodeList").innerHTML =
    nameHits.map((name) => nodeLink(name)).join("") +
    divider +
    textHits.map((name) => nodeLink(name)).join("");
}

// Name matches rank ahead of statement-text matches; the two groups are
// shown with a divider so a reader can search by what a node says, not
// only what it is called.
function searchMatches(query) {
  const nameHits = [];
  const textHits = [];
  for (const name of nodeNames) {
    if (name.toLowerCase().includes(query)) {
      nameHits.push(name);
    } else {
      const node = tablet.nodes[name];
      if (((node && node.tex_statement) || "").toLowerCase().includes(query)) textHits.push(name);
    }
  }
  return { nameHits, textHits };
}

function routeFromHash() {
  const raw = decodeURIComponent((location.hash || "").replace(/^#/, ""));
  if (raw === BUILD_INFO_ROUTE) return BUILD_INFO_ROUTE;
  return nodeExists(raw) ? raw : ((tablet.targets || []).find((t) => nodeExists(t.node)) || {}).node || nodeNames[0];
}

function firstSearchMatch() {
  const query = $("nodeSearch").value.trim().toLowerCase();
  if (!query) return "";
  const { nameHits, textHits } = searchMatches(query);
  return nameHits[0] || textHits[0] || "";
}

async function boot() {
  const response = await fetch("data/tablet.json", { cache: "no-cache" });
  tablet = await response.json();
  nodeNames = Object.keys(tablet.nodes || {}).sort((a, b) => a.localeCompare(b));
  $("nodeSearch").addEventListener("input", renderSidebar);
  $("nodeSearch").addEventListener("keydown", (event) => {
    if (event.key !== "Enter") return;
    const match = firstSearchMatch();
    if (!match) return;
    event.preventDefault();
    location.hash = encodeURIComponent(match);
  });
  document.addEventListener("keydown", (event) => {
    if (event.key !== "/" || event.ctrlKey || event.metaKey || event.altKey) return;
    const target = event.target;
    if (target && (target.tagName === "INPUT" || target.tagName === "TEXTAREA" || target.isContentEditable)) return;
    event.preventDefault();
    $("nodeSearch").focus();
    $("nodeSearch").select();
  });
  document.addEventListener("click", (event) => {
    const moreButton = event.target && event.target.closest ? event.target.closest("button.pill-more") : null;
    if (moreButton) {
      const rest = moreButton.parentElement ? moreButton.parentElement.querySelector(".pill-rest") : null;
      if (rest) rest.hidden = false;
      moreButton.remove();
      return;
    }
    const link = event.target && event.target.closest ? event.target.closest("a") : null;
    if (!link) return;
    const rawHref = link.getAttribute("href") || "";
    const directName = rawHref.startsWith("#") ? decodeURIComponent(rawHref.slice(1)) : rawHref;
    if (/^[A-Za-z0-9_']+$/.test(directName) && nodeExists(directName)) {
      event.preventDefault();
      location.hash = encodeURIComponent(directName);
    }
  });
  window.addEventListener("hashchange", () => renderMain(routeFromHash()));
  renderMain(routeFromHash());
}

boot().catch((err) => {
  $("mainContent").innerHTML = `<div class="warning">Could not load tablet viewer data: ${escapeHtml(err && err.message ? err.message : err)}</div>`;
});
