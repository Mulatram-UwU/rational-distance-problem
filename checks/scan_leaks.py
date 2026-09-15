#!/usr/bin/env python3
"""Publication-hygiene check: does anything in this repository identify the
machine it was written on?

The scan looks for

  * the repository's own directory name (read at run time from the path it is
    invoked with, so this file itself contains no such literal),
  * any absolute local path -- a Windows drive prefix, a UNC share, an
    MSYS/Git-Bash drive prefix, or a POSIX home-directory prefix
    (written here without its literal spelling, or this file would trip its
    own scan),
  * Windows machine-name prefixes.

Every file is read as raw bytes, so nothing is skipped as "binary" and no
locale or encoding rule can hide a match.  Build products (`.git`, `.lake`,
`bin`, `build`, `tmp`, `__pycache__`) are skipped, and their presence is
reported instead: `.lake/` embeds absolute build paths in its artefacts (60
files, measured), so a release has to be the git repository -- not a zip of the
working directory.

Usage:  python checks/scan_leaks.py [root]
Exit:   0 = clean, 1 = at least one hit.
"""
import os
import re
import sys

BS = chr(92)  # backslash, kept out of the literals below to survive shells and shells-in-shells
B = BS.encode()


def patterns(repo_name):
    # A literal backslash in regex source is *two* bytes.  Writing one byte would
    # escape the following metacharacter instead -- `[\/]` collapses to just `/`
    # and `\[` becomes a literal bracket, so the drive and UNC rules would miss
    # exactly the paths they exist to catch.  (This check caught that in itself.)
    Q = B + B
    return [
        ("repo directory name", re.compile(repo_name.encode(), re.I)),
        ("windows drive path", re.compile(rb"(?<![A-Za-z])[A-Za-z]:[" + Q + rb"/]")),
        ("unc path", re.compile(Q + Q + rb"[A-Za-z0-9_.$-]+" + Q + rb"[A-Za-z0-9_.$-]")),
        ("msys drive path", re.compile(rb"(?<![A-Za-z0-9_.-])/[A-Za-z]/[A-Za-z]")),
        ("posix home path", re.compile(rb"(?<![A-Za-z0-9_.-])/(?:home|Users|root)/")),
        ("machine name", re.compile(rb"\b(?:DESKTOP|LAPTOP|WIN)-[A-Za-z0-9]")),
    ]


SKIP_DIRS = {".git", "_third_party", "build", "bin", "tmp", "__pycache__", ".lake"}


def main(root="."):
    root = os.path.abspath(root)
    repo_name = os.path.basename(root)
    pats = patterns(repo_name)
    hits = {}
    skipped = set()
    for dirpath, dirnames, filenames in os.walk(root):
        pruned = [d for d in dirnames if d in SKIP_DIRS]
        for d in pruned:
            skipped.add(os.path.relpath(os.path.join(dirpath, d), root).replace(BS, "/"))
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for fn in filenames:
            p = os.path.join(dirpath, fn)
            rel = os.path.relpath(p, root).replace(BS, "/")
            try:
                with open(p, "rb") as fh:
                    b = fh.read()
            except OSError:
                continue
            for name, rx in pats:
                for m in rx.finditer(b):
                    hits.setdefault(name, {}).setdefault(rel, []).append(
                        b[: m.start()].count(b"\n") + 1)

    for name, _ in pats:
        per_file = hits.get(name, {})
        print("%-5s %-22s %3d hit(s) in %d file(s)"
              % ("FOUND" if per_file else "OK", name,
                 sum(len(v) for v in per_file.values()), len(per_file)))
        for rel in sorted(per_file):
            lines = per_file[rel]
            shown = ", ".join(str(l) for l in lines[:12])
            if len(lines) > 12:
                shown += ", ..."
            print("          %-50s lines %s" % (rel, shown))
    print()
    unique = {f for per in hits.values() for f in per}
    # The summary deliberately does not echo the directory name: this check's own
    # output is archived (it is the last step of `run_all.sh quick`), so printing
    # the name here would put it straight back into the repository.
    print("%d file(s) with at least one hit." % len(unique))
    if unique:
        print("Rewrite these before publishing: local paths are not part of the work.")
    present = sorted(d for d in skipped if os.path.basename(d) not in (".git", "__pycache__"))
    if present:
        print()
        print("Note: skipped on disk (gitignored build products): %s" % ", ".join(present))
        if any(d.endswith(".lake") for d in present):
            print("      .lake/ artefacts embed absolute build paths; publish the git")
            print("      repository (or delete .lake/ first), never a zip of this folder.")
    return 1 if unique else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "."))
