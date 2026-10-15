#!/usr/bin/env python3
"""Validate the published sources, target, semantic closure, and axiom probe."""

import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / "docs/data/tablet.json").read_text())
nodes = data["nodes"]
assert len(nodes) == 219, "Expected 218 ordinary nodes and Preamble"
assert data["targets"] == [{
    "label": "lem:spread-blowup", "node": "SpreadBlowup",
    "statement": "Vertex-spread blow-up lemma",
}]
expected_closure = {
    "BlowUpInstance", "CandidacyLowerSuperRegular", "CandidacySystem",
    "CompatibleEmbedding", "CylinderEvent", "InstanceLowerSuperRegular",
    "LowerRegularPair", "LowerSuperRegularPair", "PairDensity", "VertexSpreadOn",
}
assert nodes["SpreadBlowup"]["is_target"]
assert set(nodes["SpreadBlowup"]["semantic_closure"]) == expected_closure
shipped = json.loads((ROOT / "formalization/semantic-closure.json").read_text())
for name, node in nodes.items():
    assert not node["semantic_closure_error"], name
    assert set(node["imports"] + node["semantic_closure"]) <= nodes.keys(), name
    assert node["semantic_closure"] == shipped["closures"].get(name, []), name
    lean = (ROOT / "formalization" / node["lean_path"]).read_text()
    tex = (ROOT / "formalization" / node["tex_path"]).read_text()
    if name != "Preamble":
        assert ("\n-- BODY\n" in lean), name
        before, after = lean.split("\n-- BODY\n", 1)
        assert node["lean_proof"] == after.strip(), name
        assert node["tex_statement"] in tex, name
        assert node["tex_proof"] in tex, name
    assert not re.search(r"\b(sorry|admit|axiom|unsafe|sorryAx)\b", lean), name
    for key, ext in [("github_lean_url", "lean"), ("github_tex_url", "tex")]:
        assert node[key] == (
            "https://github.com/tkelly36/vertex-spread-blow-up-lemma-formalization/"
            f"blob/main/formalization/Tablet/{name}.{ext}"
        ), name

probes = data["build_info"]["axioms"]["print_axioms"]
assert len(probes) == 1
probe = probes[0]
assert probe["declaration"] == "SpreadBlowup"
assert probe["returncode"] == 0 and not probe["timed_out"]
assert probe["stdout"] == (
    "'SpreadBlowup' depends on axioms: [propext, Classical.choice, Quot.sound]"
)
assert json.loads((ROOT / "formalization/APPROVED_AXIOMS.json").read_text()) == {
    "global": [], "nodes": {},
}
for filename, digest in json.loads((ROOT / "verification/source-sha256.json").read_text()).items():
    assert hashlib.sha256((ROOT / filename).read_bytes()).hexdigest() == digest, filename
assert (ROOT / "docs/data/build-info.toml").read_text() == data["build_info"]["toml"]
print("Validated 219 modules, the paper target, all semantic closures, source hashes, and standard target axioms.")
