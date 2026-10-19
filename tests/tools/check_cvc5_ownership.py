"""Check the built cvc5 FFI's owned arguments; first run scripts/build.py."""

import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def main():
    response = ROOT / ".lake/build/bin/smt2lean.rsp"
    if not response.is_file():
        raise SystemExit("Build smt2lean first: python3 scripts/build.py")
    args = shlex.split(response.read_text())
    root_object = str(ROOT / ".lake/build/ir/Main.c.o.export")
    if args.count(root_object) != 1:
        raise SystemExit("Unexpected smt2lean link response: Main object missing or duplicated")
    native_libs = [Path(arg) for arg in args if Path(arg).name == "libcvc5.a"]
    if len(native_libs) != 1:
        raise SystemExit("Expected one libcvc5.a in smt2lean link response")
    native_include = native_libs[0].parent.parent / "include"
    prefix = Path(subprocess.check_output(
        ["lean", "--print-prefix"], cwd=ROOT, text=True).strip())
    # Lean's bundled clang cannot compile this C++ probe with host SDK headers.
    host_path = os.pathsep.join(p for p in os.environ.get("PATH", "").split(os.pathsep)
                                if Path(p).resolve() != (prefix / "bin").resolve())
    compiler = shutil.which("clang++", path=host_path)
    if compiler is None:
        raise SystemExit("A host clang++ compiler is required")
    with tempfile.TemporaryDirectory(prefix="cvc5-ownership-") as directory:
        temp = Path(directory)
        obj, exe = temp / "ownership.o", temp / "ownership"
        subprocess.run([
            compiler, "-std=c++17", "-stdlib=libc++", "-O2", "-DCVC5_STATIC_DEFINE",
            "-I", str(prefix / "include"), "-I", str(native_include),
            "-c", str(ROOT / "tests/backend/Ownership.cpp"), "-o", str(obj),
        ], cwd=ROOT, check=True, timeout=60)
        args[args.index(root_object)] = str(obj)
        link_response = temp / "link.rsp"
        link_response.write_text("\n".join(shlex.quote(arg) for arg in args) + "\n")
        subprocess.run([str(prefix / "bin/clang"), "-o", str(exe), "@" + str(link_response)],
                       cwd=ROOT, check=True, timeout=60)
        subprocess.run([str(exe)], cwd=ROOT, check=True, timeout=30)


if __name__ == "__main__":
    main()
