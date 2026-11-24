"""Summarise the logs that profile.sh writes, as Markdown.

Usage: python3 profile.py LOG_DIR PACKAGE_DIR...

Each log is one module elaborated on its own with Lean's profiler: `time -p`'s wall time, the
profiler's cumulative times by category, and a trace line for every command, declaration or
tactic run above the threshold. The summary lists the modules by wall time, the cumulative
categories, the slowest declarations and the critical path through the import graph of the
modules in PACKAGE_DIR..., weighted by wall time. A module's wall time includes loading its
imports, which the summary reports separately as the time of an empty module.
"""
import re
import sys
from pathlib import Path

UNITS = {"ms": 1e-3, "s": 1.0}


def seconds(value, unit):
    return float(value) * UNITS[unit]


def parse(log):
    """Wall time, cumulative categories and traced commands of one module's log."""
    text = log.read_text(errors="replace")
    wall = re.search(r"^real\s+([\d.]+)", text, re.M)
    cumulative = {}
    section = text.split("cumulative profiling times:", 1)
    if len(section) == 2:
        for name, value, unit in re.findall(r"^\s+(.+?) ([\d.]+)(ms|s)$", section[1], re.M):
            cumulative[name] = seconds(value, unit)
    traced = []
    # A trace line of the profiler: `[Elab.command] [0.152345] theorem foo ...`.
    for cls, value, what in re.findall(r"^\s*\[([\w.]+)\] \[([\d.]+)\] (.*)$", text, re.M):
        traced.append((float(value), cls, what.strip()))
    return float(wall.group(1)) if wall else None, cumulative, traced, text


def imports(packages):
    """Modules of the packages and the modules each imports, from their sources."""
    graph = {}
    for package in packages:
        for source in Path(package).rglob("*.lean"):
            if ".lake" in source.parts:
                continue
            module = ".".join(source.relative_to(package).with_suffix("").parts)
            found = re.findall(
                r"^(?:public |private )?(?:meta )?import (?:all )?([\w.]+)",
                source.read_text(errors="replace"),
                re.M,
            )
            graph[module] = found
    return graph


def critical_path(graph, weight):
    """The heaviest chain of imports, as (total, modules), counting only profiled modules."""
    memo = {}

    def best(module):
        if module not in memo:
            memo[module] = (0.0, [])
            deps = [best(d) for d in graph.get(module, []) if d in weight]
            total, chain = max(deps, default=(0.0, []), key=lambda d: d[0])
            memo[module] = (total + weight[module], chain + [module])
        return memo[module]

    return max((best(m) for m in weight), default=(0.0, []), key=lambda p: p[0])


def main():
    logs, packages = Path(sys.argv[1]), sys.argv[2:]
    modules = {}
    for log in sorted(logs.glob("*.log")):
        modules[log.stem] = parse(log)
    walls = {m: w for m, (w, _, _, _) in modules.items() if w is not None}
    failed = sorted(m for m, (_, _, _, text) in modules.items() if "error:" in text)

    print("# Lean build profile\n")
    print(f"{len(modules)} modules, each elaborated alone with `Elab.async=false`; "
          f"{sum(walls.values()):.0f}s of wall time in total.\n")
    if failed:
        print("Modules with errors (their times are not meaningful): "
              + ", ".join(failed) + "\n")

    print("## Modules by wall time\n")
    print("| Module | Wall (s) | Elaboration (s) | Largest category |")
    print("| --- | ---: | ---: | --- |")
    for module, wall in sorted(walls.items(), key=lambda kv: -kv[1]):
        cumulative = modules[module][1]
        elab = cumulative.get("elaboration", 0.0)
        top = max(cumulative.items(), key=lambda kv: kv[1], default=("", 0.0))
        print(f"| {module} | {wall:.1f} | {elab:.1f} | {top[0]} {top[1]:.1f}s |")

    print("\n## Cumulative categories over all modules\n")
    totals = {}
    for _, cumulative, _, _ in modules.values():
        for name, value in cumulative.items():
            totals[name] = totals.get(name, 0.0) + value
    print("| Category | Seconds |")
    print("| --- | ---: |")
    for name, value in sorted(totals.items(), key=lambda kv: -kv[1])[:20]:
        print(f"| {name} | {value:.1f} |")

    print("\n## Slowest traced items\n")
    print("| Seconds | Module | Kind | Item |")
    print("| ---: | --- | --- | --- |")
    items = [
        (value, module, cls, what)
        for module, (_, _, traced, _) in modules.items()
        for value, cls, what in traced
    ]
    for value, module, cls, what in sorted(items, key=lambda t: -t[0])[:30]:
        what = what.replace("|", "\\|")
        if len(what) > 90:
            what = what[:87] + "..."
        print(f"| {value:.2f} | {module} | {cls} | `{what}` |")

    total, chain = critical_path(imports(packages), walls)
    print("\n## Critical path through the imports\n")
    print(f"{total:.0f}s of wall time, which includes each module's import loading:\n")
    for module in chain:
        print(f"- {module} ({walls[module]:.1f}s)")


if __name__ == "__main__":
    main()
