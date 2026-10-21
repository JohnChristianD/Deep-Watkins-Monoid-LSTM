(() => {
  "use strict";
  const learnerPath = "FullCoupled/CanonicalLearnerMonolith.agda";
  const theoremPath = "FullCoupled/TheoremsMonolith.agda";
  const data = window.MonolithContent;

  function filterEntries(query, scope, entries) {
    const needle = String(query || "").trim().toLowerCase();
    return (entries || []).filter((entry) => {
      const inScope = scope === "learner" ? entry.source === learnerPath :
        scope === "theorem" ? entry.source === theoremPath :
        entry.source === learnerPath || entry.source === theoremPath;
      return inScope && (!needle ||
        (entry.name + "\n" + entry.signature).toLowerCase().includes(needle));
    });
  }
  window.MonolithPage = { filterEntries };
  if (typeof document === "undefined") return;
  const root = document.getElementById("app");
  if (!root) return;
  if (!data || !Array.isArray(data.entries) || !Array.isArray(data.sourceFiles)) {
    root.textContent = "The generated declaration catalog is missing or invalid.";
    return;
  }

  const make = (tag, className, text) => {
    const n = document.createElement(tag);
    if (className) n.className = className;
    if (text !== undefined && text !== null) n.textContent = String(text);
    return n;
  };
  const link = (href, label, className) => {
    const n = make("a", className, label);
    n.href = href;
    if (href.startsWith("https://")) { n.target = "_blank"; n.rel = "noreferrer"; }
    return n;
  };
  const sourceUrl = (entry) =>
    "https://github.com/JohnChristianD/Deep-Watkins-Monoid-LSTM/blob/main/" +
    entry.source + "#L" + entry.line;
  const sourceLabel = (path) =>
    path === learnerPath ? "Canonical learner semantics" : "Theorem and proof monolith";
  const section = (id, heading, lede) => {
    const n = make("section", "section");
    n.id = id;
    n.append(make("h2", "", heading));
    if (lede) n.append(make("p", "section-lede", lede));
    return n;
  };

  const shell = make("main", "shell");
  const masthead = make("header", "masthead");
  masthead.append(make("div", "brand", "The Monoid LSTM Project"));
  masthead.append(make("p", "mast-note",
    "Source-first documentation derived from the two canonical Agda monoliths."));
  shell.append(masthead);
  const layout = make("div", "layout");
  const nav = make("nav", "side-nav");
  nav.append(make("p", "nav-title", "Contents"));
  const navList = make("ul", "nav-list");
  [["Overview", "overview"], ["Source files", "sources"],
   ["Russian constructivism", "russ"], ["Declaration index", "declarations"]]
    .forEach(([label, id]) => {
      const li = make("li"); li.append(link("#" + id, label)); navList.append(li);
    });
  nav.append(navList);
  nav.append(link("https://www.gnu.org/",
    "GNU.org · free software and formal tools", "source-link"));
  nav.append(make("p", "nav-title", "Canonical files"));
  data.sourceFiles.forEach((path) => nav.append(link(
    "https://github.com/JohnChristianD/Deep-Watkins-Monoid-LSTM/blob/main/" + path,
    sourceLabel(path), "source-link")));
  layout.append(nav);

  const doc = make("div", "document");
  const intro = make("section", "intro"); intro.id = "overview";
  intro.append(make("div", "eyebrow", "Formal specification / proof surface"));
  intro.append(make("h1", "", "The Monoid LSTM / Learner and Theorem Monoliths"));
  intro.append(make("p", "lede",
    "The learner monolith defines the coupled recurrent learner and its computational semantics; the theorem monolith contains results built over those definitions. This declaration index is regenerated from both canonical files only."));
  const stats = make("div", "stats");
  [[data.entries.filter((e) => e.source === learnerPath).length, "learner entries"],
   [data.entries.filter((e) => e.source === theoremPath).length, "theorem entries"],
   [data.entries.length, "indexed declarations"]].forEach(([count, label]) => {
    const stat = make("div", "stat");
    stat.append(make("strong", "", count), make("span", "", label)); stats.append(stat);
  });
  intro.append(stats); doc.append(intro);

  const sources = section("sources", "The two canonical source files",
    "Only the two source paths below are indexed. Unrelated Agda modules and graph-search helpers are excluded.");
  [
    [learnerPath, "Canonical learner monolith",
     "Defines the coupled recurrent learner, state transitions, optimizer and policy semantics. Its named RUSS basis is the declared source of recursive and computability assumptions."],
    [theoremPath, "Theorem monolith",
     "Contains theorem statements and proof constructions over the learner definitions. Reflection/TC primitives and imported theorem libraries are explicit trust boundaries."]
  ].forEach(([path, title, summary]) => {
    const card = make("div", "source-record");
    card.append(make("h3", "", title), make("p", "", summary));
    card.append(link("https://github.com/JohnChristianD/Deep-Watkins-Monoid-LSTM/blob/main/" + path,
      path, "source-link"));
    sources.append(card);
  });
  doc.append(sources);

  const russ = section("russ", "Russian constructivism (RUSS): trust-surface inventory",
    "This is a lexical inventory of direct monolith declarations, not a global consistency proof. Kernel acceptance remains relative to imported theory, postulates, Reflection/TC primitives, rewrite system, and trusted checker. A model or relative-consistency argument for the complete transitive closure remains a separate obligation.");
  const russNote = make("div", "russ-note");
  russNote.append(make("strong", "trust-label", "Consistency not certified")); russ.append(russNote);
  const russEntries = data.entries.filter((entry) => {
    const c = entry.category.toLowerCase();
    return c.includes("russ") || c.includes("trust boundary") ||
      c.includes("reflection / tc primitive");
  }).slice(0, 24);
  russ.append(make("p", "", "Indexed direct trust entries: " + russEntries.length +
    (russEntries.length === 24 ? " shown (up to 24 displayed)." : ".")));
  russEntries.forEach((entry) => russ.append(make("p", "signature",
    entry.source + ":" + entry.line + ": " + entry.name + " : " + entry.signature)));
  doc.append(russ);

  const declarations = section("declarations", "Declaration index",
    "Search declaration names and type signatures. Use source-scope controls to include both monoliths or only one; source path and category are displayed as metadata, not searched.");
  const tools = make("div", "tools");
  const search = make("input");
  search.type = "search"; search.setAttribute("aria-label", "Search monolith declarations");
  search.placeholder = "Search declaration names or types"; tools.append(search);
  const filterRow = make("div", "filter-row");
  const scopes = [["all", "Both monoliths"], ["learner", "Learner monolith"],
    ["theorem", "Theorem monolith"]];
  let scope = "all"; let selected = null;
  const buttons = new Map();
  scopes.forEach(([value, label]) => {
    const button = make("button", "", label); button.type = "button";
    button.setAttribute("aria-pressed", String(value === scope));
    button.dataset.active = String(value === scope);
    button.addEventListener("click", () => {
      scope = value; selected = null;
      buttons.forEach((other, key) => {
        const active = key === scope; other.dataset.active = String(active);
        other.setAttribute("aria-pressed", String(active));
      });
      renderEntries();
    });
    buttons.set(value, button); filterRow.append(button);
  });
  tools.append(filterRow); declarations.append(tools);
  const resultCount = make("p", "result-count", ""); declarations.append(resultCount);
  const entryList = make("div", "entry-list"); declarations.append(entryList);
  const searchLimit = 60;
  function renderEntries() {
    const matches = filterEntries(search.value, scope, data.entries);
    resultCount.textContent = matches.length + " declarations matched; showing " +
      Math.min(matches.length, searchLimit) + ".";
    entryList.replaceChildren();
    matches.slice(0, searchLimit).forEach((entry) => {
      const card = make("div", "entry");
      const expanded = selected === entry.id; card.dataset.selected = String(expanded);
      const meta = make("div", "entry-meta");
      meta.append(make("span", "entry-kind", entry.category));
      meta.append(make("span", "", entry.source + ":" + entry.line)); card.append(meta);
      const open = make("button", "entry-select", entry.name); open.type = "button";
      open.setAttribute("aria-expanded", String(expanded));
      open.addEventListener("click", () => { selected = expanded ? null : entry.id; renderEntries(); });
      const heading = make("h3"); heading.append(open); card.append(heading);
      card.append(make("p", "signature", entry.signature || "(signature continues below)"));
      if (expanded) {
        const details = make("div", "detail");
        details.append(make("p", "", "Source: " + entry.source + " at line " + entry.line +
          ". This entry is indexed from monolith text; its presence is not a type-checking or consistency claim."));
        details.append(link(sourceUrl(entry), "Open declaration in source")); card.append(details);
      }
      entryList.append(card);
    });
  }
  search.addEventListener("input", () => { selected = null; renderEntries(); });
  renderEntries(); doc.append(declarations);
  doc.append(make("footer", "footer",
    "Generated from the two canonical Agda monoliths. Declaration presence is not evidence of theorem correctness or global consistency."));
  layout.append(doc); shell.append(layout); root.replaceChildren(shell);
})();