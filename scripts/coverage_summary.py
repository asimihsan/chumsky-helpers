#!/usr/bin/env python3
"""coverage_summary.py - Summarise llvm-cov JSON output focusing on uncovered lines.

The script ingests the `cargo llvm-cov --json` output (optionally via --input),
analyses the per-file *segments* list to derive line-level coverage, and emits a
compact report that language models (and humans!) can quickly absorb.

Key features:
  • Shows, per source file, overall line-coverage percentage and the list of
    uncovered line ranges (e.g. 15-18, 42, 90-93).
  • Sorts files by increasing coverage so the most problematic files appear at
    the top.
  • Optional `--code` flag prints the actual source lines for the gaps to give
    immediate context.
  • Workspace filtering: by default we only report files that reside inside the
    current working directory.  Pass `--all` to include dependency code.

Usage examples (run from the workspace root):
  # Basic summary
  scripts/coverage_summary.py coverage.json

  # Include code snippets, limit to max 5 uncovered lines of code per file
  scripts/coverage_summary.py --code -n 5 coverage.json

  # Show everything including third-party crates
  scripts/coverage_summary.py --all coverage.json
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

Range = Tuple[int, int]  # inclusive (start, end)


# ------------------------------------------------------------ helpers

def _add_line_coverage(mapping: Dict[int, bool], line: int, covered: bool) -> None:
    """Update mapping so that a line is marked as covered if *any* region is covered."""
    prev = mapping.get(line)
    if prev is True:
        # Already known covered; nothing to do.
        return
    mapping[line] = covered or prev is True


def _merge_uncovered_lines(lines: Sequence[int]) -> List[Range]:
    """Convert a sorted list of uncovered line numbers to inclusive ranges."""
    if not lines:
        return []
    ranges: List[Range] = []
    start = prev = lines[0]
    for ln in lines[1:]:
        if ln == prev + 1:
            prev = ln
            continue
        ranges.append((start, prev))
        start = prev = ln
    ranges.append((start, prev))
    return ranges


def _format_range(r: Range) -> str:
    return f"{r[0]}-{r[1]}" if r[0] != r[1] else str(r[0])


def _render_uncovered_ranges(ranges: Sequence[Range]) -> str:
    return ", ".join(_format_range(r) for r in ranges) if ranges else "<none>"


# ------------------------------------------------------------ core parser

def analyse_file(file_entry: dict, show_gap_regions: bool = False) -> Tuple[int, int, List[int]]:
    """Return (covered_lines, total_lines, list_of_uncovered_lines)."""
    segments = file_entry.get("segments") or []

    line_cov: Dict[int, bool] = {}
    for seg in segments:
        # According to CoverageExporterJson.cpp the layout is:
        # [Line, Col, Count, HasCount, IsRegionEntry, (IsGapRegion?)]
        if len(seg) < 5:
            continue  # malformed
        line, _col, count, has_count, _is_region_entry, *rest = seg
        is_gap_region = bool(rest[0]) if rest else False
        if not has_count:
            continue
        if not show_gap_regions and is_gap_region:
            # Gap regions (e.g. lines without executable code) do not affect line coverage.
            continue
        covered = count > 0
        _add_line_coverage(line_cov, line, covered)

    total = len(line_cov)
    covered = sum(1 for v in line_cov.values() if v)
    uncovered_lines = sorted([ln for ln, ok in line_cov.items() if not ok])
    return covered, total, uncovered_lines


# ------------------------------------------------------------ CLI

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Summarise llvm-cov JSON line coverage gaps.")
    p.add_argument(
        "input",
        nargs="?",
        default="coverage.json",
        help="Path to coverage JSON file. If it does not exist and --collect is given"
        " the file will be generated (default: coverage.json).",
    )
    p.add_argument("--all", action="store_true", help="Include files outside the current working directory.")
    p.add_argument("--code", action="store_true", help="Print source code for uncovered lines (expensive).")
    p.add_argument(
        "-n",
        "--max-lines",
        type=int,
        default=10,
        help="Max uncovered source lines to print per file when --code is given (default: 10).",
    )
    p.add_argument(
        "--threshold",
        type=float,
        default=80.0,
        help="Percentage below which a file is considered to have poor coverage (default: 80)",
    )
    p.add_argument(
        "--top",
        type=int,
        default=10,
        help="Show at most this many of the worst-covered files in the guidance section (default: 10).",
    )
    p.add_argument(
        "--collect",
        action="store_true",
        help="Invoke 'cargo llvm-cov' to (re)generate the JSON before analysing.",
    )
    p.add_argument(
        "--workspace",
        default=".",
        help="Path to the Rust workspace root (default: current directory). "
        "The command is executed there when --collect is used.",
    )
    return p


# ------------------------------------------------------------ main

def main(argv: Sequence[str] | None = None) -> None:
    args = build_parser().parse_args(argv)

    json_path = Path(args.input)

    # -------------------------------------------------------- optional collection step

    if args.collect or not json_path.is_file():
        # Lazily run cargo llvm-cov when JSON is missing or user requested collection.
        ws_root = Path(args.workspace).resolve()
        if not ws_root.joinpath("Cargo.toml").is_file():
            sys.exit(f"error: {ws_root} does not look like a Rust workspace (Cargo.toml missing)")

        cmd = [
            "cargo",
            "+nightly",
            "llvm-cov",
            "--json",
            "--mcdc",
            "--all-features",
            "--workspace",
            "--output-path",
            str(json_path),
        ]
        print(f"[cov] collecting coverage via: {' '.join(cmd)} (cwd={ws_root})", file=sys.stderr)
        import subprocess

        try:
            proc = subprocess.run(
                cmd,
                cwd=ws_root,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            if proc.returncode != 0:
                # Forward the captured output so the user can diagnose.
                sys.stderr.write(proc.stdout)
                sys.stderr.flush()
                sys.exit(f"error: coverage collection failed (exit {proc.returncode})")
        except FileNotFoundError:
            sys.exit("error: 'cargo' not found in PATH")

        if not json_path.is_file():
            sys.exit("error: expected coverage.json not produced")

    with json_path.open("r", encoding="utf-8") as fh:
        root = json.load(fh)

    data = root.get("data")
    if not data:
        sys.exit("error: no 'data' array in JSON input")
    # In almost all cases cargo llvm-cov produces a single export.
    cov = data[0]
    files = cov.get("files") or []

    cwd = Path(os.getcwd()).resolve()

    reports = []  # List of tuples: (coverage_ratio, covered, total, uncovered_ranges, path, uncovered_lines)

    for fe in files:
        filename = Path(fe.get("filename", "<unknown>")).resolve()
        if not args.all and cwd not in filename.parents and filename != cwd:
            # skip files outside workspace
            continue
        covered, total, uncovered = analyse_file(fe)
        if total == 0:
            continue  # no executable code
        ranges = _merge_uncovered_lines(uncovered)
        coverage_ratio = covered / total if total else 1.0
        reports.append((coverage_ratio, covered, total, ranges, filename, uncovered))

    # Sort by ascending coverage
    reports.sort(key=lambda x: x[0])

    poor: List[Tuple[float, Range, Path, List[int]]] = []

    for ratio, covered, total, ranges, path, uncovered in reports:
        pct = ratio * 100
        print(f"\n{path.relative_to(cwd) if path.is_relative_to(cwd) else path}")
        print(f"  coverage: {covered}/{total} lines ({pct:.1f}%)")
        print(f"  uncovered: {_render_uncovered_ranges(ranges)}")
        if args.code and uncovered:
            _print_code_snippets(path, uncovered, args.max_lines)

        # Collect poorly covered files for Guidance
        if pct < args.threshold:
            poor.append((pct, ranges, path, uncovered))

    if not reports:
        print("No files matched the selected criteria.")

    # -------------------------------------------------------- Guidance

    if poor:
        print("\n================ Focus Suggestions ================")
        # Sort by ascending percentage, keep top N
        poor.sort(key=lambda t: t[0])
        for pct, ranges, path, uncovered in poor[: args.top]:
            rel = path.relative_to(cwd) if path.is_relative_to(cwd) else path
            print(f"• {rel}: {pct:.1f}% covered; fill gaps at {_render_uncovered_ranges(ranges)}")
        print("=======================================================\n")
    else:
        print("No files with poor coverage found.")


# ------------------------------------------------------------ code snippets

def _print_code_snippets(path: Path, lines: Sequence[int], max_lines: int) -> None:
    try:
        source = path.read_text(encoding="utf-8").splitlines()
    except Exception as e:
        print(f"    [unable to read source: {e}]")
        return

    print("  --- uncovered source (first {} lines) ---".format(max_lines))
    shown = 0
    for ln in lines:
        if shown >= max_lines:
            print("    … (truncated)")
            break
        if ln - 1 < len(source):
            print(f"    {ln:>4}: {source[ln - 1].rstrip()}")
            shown += 1
    print("  --- end ---")


if __name__ == "__main__":  # pragma: no cover
    main()
