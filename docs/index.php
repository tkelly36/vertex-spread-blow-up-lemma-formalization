<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Trellis Tablet Viewer</title>
  <link rel="stylesheet" href="assets/viewer.css">
  <script>
    window.MathJax = {
      loader: { load: ['[tex]/ams', '[tex]/html'] },
      tex: {
        packages: {'[+]': ['ams', 'html']},
        inlineMath: [['\\(', '\\)'], ['$', '$']],
        displayMath: [['\\[', '\\]'], ['$$', '$$']],
        processEnvironments: false,
        processEscapes: true,
        macros: { noderef: ['\\href{#1}{\\operatorname{#1}}', 1] }
      },
      options: { skipHtmlTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code'] }
    };
  </script>
  <script defer src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"></script>
  <script defer src="assets/viewer.js"></script>
</head>
<body>
  <div class="app-shell">
    <aside class="sidebar">
      <div class="brand">
        <div class="eyebrow">Trellis Tablet</div>
        <h1 id="siteTitle">Loading...</h1>
      </div>
      <section class="nav-section">
        <h2>Build</h2>
        <a id="buildInfoLink" class="target-link" href="#build-info"><span class="node-name">Build Info</span><span class="badge">TOML</span></a>
        <a class="target-link" href="data/build-info.toml" target="_blank" rel="noopener"><span class="node-name">Raw TOML</span><span class="badge">file</span></a>
      </section>
      <section class="nav-section">
        <h2>Paper Targets</h2>
        <div id="targetList" class="target-list"></div>
      </section>
      <section class="nav-section">
        <h2>Dependency Outline</h2>
        <div id="dependencyOutline" class="dependency-outline"></div>
      </section>
      <section class="nav-section all-node-section">
        <h2>All Nodes</h2>
        <label class="search-label" for="nodeSearch">Search nodes (press / to focus)</label>
        <input id="nodeSearch" class="search-input" type="search" autocomplete="off" placeholder="Name or statement text">
        <div id="nodeCount" class="node-count"></div>
        <div id="allNodeList" class="all-node-list"></div>
      </section>
    </aside>
    <main class="content" id="mainContent" tabindex="-1">
      <div class="loading">Loading tablet...</div>
    </main>
  </div>
</body>
</html>
