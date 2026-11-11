"""Convert one non-module Lean file to the module system, in place.

Usage: python scripts/to_module.py FILE.lean [FILE.lean ...]

The transformation is purely mechanical:
  * a `module` line is put first;
  * every `import X` becomes `public import X`;
  * `@[expose] public section` is inserted after the imports and the module
    docstring, so that all declarations stay visible and unfoldable downstream,
    as they are for a non-module file.

A module may only import modules, so files are converted bottom-up: first the
files that import only Mathlib, then their importers. Proofs that unfolded
non-exposed Mathlib definitions by `rfl`, `simp` or `change` have to be repaired
by hand afterwards.
"""
import re
import sys


def convert(text: str) -> str:
    lines = text.split("\n")
    if lines and lines[0].strip() == "module":
        return text
    i = 0
    n = len(lines)
    # imports (blank lines and line comments between them are kept)
    last_import = -1
    while i < n and (lines[i].startswith("import ") or lines[i].strip() == ""
                     or lines[i].startswith("--")):
        if lines[i].startswith("import "):
            lines[i] = "public " + lines[i]
            last_import = i
        i += 1
    insert_at = last_import + 1
    # skip one module docstring `/-! ... -/` directly after the imports
    j = insert_at
    while j < n and lines[j].strip() == "":
        j += 1
    if j < n and lines[j].lstrip().startswith("/-!"):
        while j < n and "-/" not in lines[j]:
            j += 1
        insert_at = j + 1
    lines[insert_at:insert_at] = ["", "@[expose] public section"]
    return "module\n\n" + "\n".join(lines)


def main() -> None:
    for path in sys.argv[1:]:
        with open(path, encoding="utf-8") as f:
            text = f.read()
        new = convert(text)
        if new != text:
            with open(path, "w", encoding="utf-8", newline="\n") as f:
                f.write(new)
            print("converted", path)
        else:
            print("already a module", path)


if __name__ == "__main__":
    main()
