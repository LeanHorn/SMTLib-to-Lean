"""Directory translation preserves paths, isolates modules, and records failures."""

import json
import os
from pathlib import Path
import subprocess

from .support import EXE, ROOT, read_generated, run, without_sources


def check_batch(lean, tmp):
    source = tmp / "batch-suite"
    source.mkdir()
    cases = {
        "04.c_000.smt2": """(set-logic ALL)
(define-fun-rec identity ((n Int)) Int
  (let ((previous (- n 1))) (ite (<= n 0) n (+ 1 (identity previous)))))
(assert (distinct (identity 0) 0))(check-sat)
""",
        "same-name.smt2": """(set-logic ALL)
(declare-const p Bool)(declare-const a (Array Int Int))
(declare-datatype Flag ((off) (on (value Int))))
(assert ((_ is on) (on 0)))(assert (= (value (on 0)) 0))
(assert (xor p p))
(assert (= (select (store a 0 1) 0) 1))(check-sat)
""",
        "same_name.smt2": """(set-logic ALL)
(declare-const p Bool)(declare-const a (Array Int Int))
(declare-datatype Flag ((off) (on (value Int))))
(assert ((_ is on) (on 0)))(assert (= (value (on 0)) 0))
(declare-const r Real)(assert (> r 0.0))
(assert (xor p p))
(assert (= (select (store a 0 2) 0) 2))(check-sat)
""",
        "same-name.lean.tmp/by.smt2": """(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (Inv 0))
(assert (forall ((n Int)) (=> (Inv n) (Inv (+ n 1)))))
(assert (forall ((n Int)) (=> (and (Inv n) (< n 0)) false)))
(check-sat)
""",
        "Broken.smt2": "(set-logic ALL)(assert",
    }
    for name, text in cases.items():
        path = source / name
        path.parent.mkdir(exist_ok=True)
        path.write_text(text)
    (source / "notes.txt").write_text("Not an SMT input.")

    output = tmp / "generated"
    result = subprocess.run(
        [str(EXE), str(source), "--out", str(output), "--max-rec-depth", "8192"],
        cwd=ROOT, capture_output=True, text=True,
    )
    assert result.returncode == 1, result
    report_path = output / "manifest.json"
    assert report_path.exists(), (result.stdout, result.stderr)
    report = json.loads(report_path.read_text())
    assert (report["total"], report["translated"], report["failed"]) == (5, 4, 1), report
    entries = report["files"]
    by_input = {entry["input"]: entry for entry in entries}
    assert set(by_input) == set(cases), report
    failed = by_input["Broken.smt2"]
    assert failed["status"] == "failed" and failed["error"], failed

    paths, modules, namespaces = [], [], []
    for name, entry in by_input.items():
        if name == "Broken.smt2":
            continue
        assert entry["status"] == "translated", entry
        path = output / entry["output"]
        relative = path.relative_to(output)
        assert relative == Path(source.name) / Path(name).with_suffix(".lean"), relative
        text = path.read_text()
        assert "set_option maxRecDepth 8192" in text
        assert "-- Statements" in text and "-- Proofs" in text
        assert "sorry" not in text.split("-- Proofs", 1)[0]
        assert "sorry" in text.split("-- Proofs", 1)[1]
        assert f"namespace {entry['namespace']}" in text
        assert text.rstrip().endswith(f"end {entry['namespace']}")
        paths.append(path)
        modules.append(entry["module"])
        namespaces.append(entry["namespace"])
    assert len(set(paths)) == len(paths) == 4
    assert len(set(modules)) == 4
    assert len(set(namespaces)) == 4
    assert set(output.rglob("*.lean")) == set(paths)

    # Compile the actual generated templates, then import them together. This
    # catches collisions in helper definitions as well as in the main goals.
    for path in paths:
        search_path = str(output)
        if "import Mathlib." in path.read_text():
            search_path += os.pathsep + os.environ["LEAN_PATH"]
        result = subprocess.run(
            [str(lean), "-o", str(path.with_suffix(".olean")), str(path.relative_to(output))],
            cwd=output, env=dict(os.environ, LEAN_PATH=search_path), capture_output=True, text=True,
        )
        assert result.returncode == 0, (path, result.stdout, result.stderr)
    imports = output / "ImportAll.lean"
    imports.write_text("\n".join(f"import {module}" for module in modules) + "\n")
    result = subprocess.run(
        [str(lean), "--error=hasSorry", imports.name], cwd=output,
        env=dict(os.environ, LEAN_PATH=str(output) + os.pathsep + os.environ["LEAN_PATH"]),
        capture_output=True, text=True,
    )
    assert result.returncode == 0, (result.stdout, result.stderr)

    # Re-running must preserve the user's generated files and proof edits.
    before = {path: path.read_bytes() for path in paths + [report_path]}
    run(source, "--out", output, code=1)
    assert all(path.read_bytes() == contents for path, contents in before.items())
    empty = tmp / "empty"
    empty.mkdir()
    run(empty, "--out", tmp / "empty-output", code=1)
    assert not (tmp / "empty-output").exists()

    # Unsafe names cannot silently merge; reject before writing any output.
    collision = tmp / "collision"
    collision.mkdir()
    (collision / "a«b.smt2").write_text("(set-logic ALL)(check-sat)")
    (collision / "a_b.smt2").write_text("(set-logic ALL)(check-sat)")
    run(collision, "--out", tmp / "collision-output", code=1)
    assert not (tmp / "collision-output").exists()
    linked = tmp / "linked"
    linked.mkdir()
    (linked / "escape.smt2").symlink_to(source / "same_name.smt2")
    run(linked, "--out", tmp / "linked-output", code=1)
    assert not (tmp / "linked-output").exists()

    # Reserved report names and unquotable characters receive explicit mappings.
    reserved = tmp / "manifest.json"
    reserved.mkdir()
    (reserved / "odd»name.smt2").write_text("(set-logic ALL)(assert false)(check-sat)")
    normalized = tmp / "normalized"
    run(reserved, "--out", normalized)
    report = json.loads((normalized / "manifest.json").read_text())
    assert (report["total"], report["translated"], report["failed"]) == (1, 1, 0)
    entry = report["files"][0]
    assert entry["input"] == "odd»name.smt2"
    assert entry["output"] == "manifest.json_project/odd_name.lean"
    assert f"namespace {entry['namespace']}" in (normalized / entry["output"]).read_text()

    # Single-file callers still receive Query.lean without an enclosing namespace.
    standalone = tmp / "single"
    run(source / "04.c_000.smt2", "--out", standalone)
    original = without_sources(read_generated(standalone))
    entry = by_input["04.c_000.smt2"]
    batch = without_sources((output / entry["output"]).read_text()).replace("maxRecDepth 8192", "maxRecDepth 4096")
    wrapper = [f"namespace {entry['namespace']}", f"end {entry['namespace']}"]
    unwrapped = [line for line in batch.splitlines() if line.strip() and line not in wrapper]
    assert unwrapped == [line for line in original.splitlines() if line.strip()]
    print("Batch passed: paths, names, mixed outcomes, module imports, overwrite refusal and single-file compatibility")
