#!/usr/bin/env python3
"""Collect recent LLVM GitHub issues and PRs containing Alive2 proofs or links.

Uses the authenticated `gh` CLI to search `llvm/llvm-project` (both issues and
pull requests) for Alive2 web proof links (`alive2.llvm.org/ce/...`) and pasted
Alive2 proof outputs (`Transformation seems to be correct`), deduplicates and
sorts by creation time descending, and optionally fetches the underlying LLVM IR
from the Alive2 Compiler Explorer shortlink API.

Zero external Python dependencies (Python 3 stdlib + `gh` CLI).
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import math
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

ALIVE2_URL_RE = re.compile(
    r"https?://alive2\.llvm\.org/ce/(?:z/[A-Za-z0-9_-]+|[^\s\)\]>\"'`]+)"
)
ALIVE2_SHORTLINK_RE = re.compile(r"https?://alive2\.llvm\.org/ce/z/([A-Za-z0-9_-]+)")
CODE_BLOCK_RE = re.compile(r"```[a-zA-Z0-9_+-]*\n(.*?)```", re.DOTALL)
ALIVE2_PROOF_MARKER_RE = re.compile(
    r"Transformation seems to be correct!?|Transformation doesn't verify!?",
    re.IGNORECASE,
)


def run_gh_search(
    repo: str,
    kind_filter: str,
    term: str,
    limit: int,
    state: str,
) -> list[dict[str, Any]]:
    """Run paginated GitHub `/search/issues` queries via `gh api`."""
    results: list[dict[str, Any]] = []
    per_page = min(100, max(1, limit))
    pages = math.ceil(limit / per_page)

    state_clause = ""
    if state == "open":
        state_clause = " is:open"
    elif state == "closed":
        state_clause = " is:closed"
    elif state == "merged":
        if kind_filter != "is:pull-request":
            return []
        state_clause = " is:merged"

    query = f'repo:{repo} {kind_filter}{state_clause} "{term}"'

    for page in range(1, pages + 1):
        cmd = [
            "gh",
            "api",
            "-X",
            "GET",
            "search/issues",
            "-f",
            f"q={query}",
            "-f",
            "sort=created",
            "-f",
            "order=desc",
            "-f",
            f"per_page={per_page}",
            "-f",
            f"page={page}",
        ]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        if proc.returncode != 0:
            raise RuntimeError(
                f"gh api search failed (exit {proc.returncode}): {proc.stderr.strip()}"
            )
        payload = json.loads(proc.stdout)
        items = payload.get("items", [])
        results.extend(items)
        if len(items) < per_page or len(results) >= limit:
            break

    return results[:limit]


def extract_alive2_links(text: str) -> list[str]:
    seen: set[str] = set()
    links: list[str] = []
    for m in ALIVE2_URL_RE.finditer(text or ""):
        url = m.group(0).rstrip(".,;:!?")
        if url not in seen:
            seen.add(url)
            links.append(url)
    return links


def extract_inline_ir(text: str) -> list[str]:
    blocks: list[str] = []
    for m in CODE_BLOCK_RE.finditer(text or ""):
        content = m.group(1).strip()
        if "define " in content:
            blocks.append(content)
    return blocks


def fetch_alive2_shortlink(
    short_id: str, timeout: float = 10.0, retries: int = 3
) -> dict[str, Any]:
    """Fetch LLVM IR and compiler options from Alive2 CE shortlink API."""
    api_url = f"https://alive2.llvm.org/ce/api/shortlinkinfo/{short_id}"
    req = urllib.request.Request(
        api_url,
        headers={"Accept": "application/json", "User-Agent": "lean-nano-llvm-collector/1.0"},
    )
    last_err: str = ""
    data: dict[str, Any] | None = None
    for attempt in range(retries + 1):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                data = json.loads(resp.read().decode("utf-8", errors="replace"))
            break
        except (urllib.error.URLError, TimeoutError, json.JSONDecodeError, OSError) as exc:
            last_err = str(exc)
            if attempt < retries:
                time.sleep(0.5 * (2**attempt))

    if data is None:
        return {"id": short_id, "ok": False, "error": last_err}

    sources: list[str] = []
    compiler_options: list[str] = []
    for session in data.get("sessions", []):
        src = session.get("source")
        if isinstance(src, str) and src.strip():
            sources.append(src)
        for comp in session.get("compilers", []):
            opts = comp.get("options")
            if isinstance(opts, str) and opts.strip():
                compiler_options.append(opts)

    return {
        "id": short_id,
        "url": f"https://alive2.llvm.org/ce/z/{short_id}",
        "ok": True,
        "sources": sources,
        "compiler_options": compiler_options,
    }


def build_record(item: dict[str, Any], tests_dir: Path) -> dict[str, Any]:
    is_pr = "pull_request" in item and item["pull_request"] is not None
    kind = "pr" if is_pr else "issue"
    number = int(item["number"])
    file_stem = f"{kind}-{number}"
    body = item.get("body") or ""
    links = extract_alive2_links(body)
    inline_ir = extract_inline_ir(body)
    has_proof_marker = bool(ALIVE2_PROOF_MARKER_RE.search(body))
    already_proved = (tests_dir / f"{file_stem}.lean").exists()

    return {
        "kind": kind,
        "number": number,
        "file_stem": file_stem,
        "title": item.get("title", ""),
        "url": item.get("html_url", ""),
        "state": item.get("state", ""),
        "created_at": item.get("created_at", ""),
        "updated_at": item.get("updated_at", ""),
        "author": (item.get("user") or {}).get("login", ""),
        "labels": [lbl.get("name", "") for lbl in item.get("labels", [])],
        "alive2_links": links,
        "has_alive2_proof_marker": has_proof_marker,
        "inline_ir_blocks": inline_ir,
        "alive2_fetched": [],
        "already_proved": already_proved,
    }


def render_markdown(records: list[dict[str, Any]], repo: str) -> str:
    pr_count = sum(1 for r in records if r["kind"] == "pr")
    issue_count = sum(1 for r in records if r["kind"] == "issue")
    proved_count = sum(1 for r in records if r["already_proved"])
    ir_count = sum(
        1
        for r in records
        if r["inline_ir_blocks"]
        or any(f.get("ok") and f.get("sources") for f in r["alive2_fetched"])
    )

    lines = [
        f"# Collected Alive2 Issues & PRs from `{repo}`",
        "",
        f"- **Total**: {len(records)} ({pr_count} PRs, {issue_count} issues)",
        f"- **With LLVM IR extracted (Alive2 CE or inline)**: {ir_count}",
        f"- **Already proved in `Tests/Alive2/`**: {proved_count}",
        "",
        "| # | Target | Created | State | Alive2 Links | IR | Proved | Title |",
        "|---:|---|---|---|---|---|---|---|",
    ]
    for idx, r in enumerate(records, start=1):
        title = r["title"].replace("|", "\\|").replace("\n", " ")
        created = r["created_at"][:10]
        has_ir = bool(r["inline_ir_blocks"]) or any(
            f.get("ok") and f.get("sources") for f in r["alive2_fetched"]
        )
        link_str = ", ".join(
            f"[link {i + 1}]({u})" for i, u in enumerate(r["alive2_links"][:3])
        )
        if len(r["alive2_links"]) > 3:
            link_str += f" (+{len(r['alive2_links']) - 3})"
        if not link_str and r["has_alive2_proof_marker"]:
            link_str = "inline proof"
        lines.append(
            f"| {idx} | [`{r['file_stem']}`]({r['url']}) | {created} | {r['state']} "
            f"| {link_str} | {'yes' if has_ir else 'no'} "
            f"| {'yes' if r['already_proved'] else 'no'} | {title} |"
        )
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Collect recent GitHub issues and PRs with Alive2 proofs/links."
    )
    parser.add_argument(
        "-n",
        "--count",
        type=int,
        default=100,
        help="Number of most recent issues/PRs to collect (default: 100).",
    )
    parser.add_argument(
        "--kind",
        choices=["all", "pr", "issue"],
        default="all",
        help="Collect PRs, issues, or both (default: all).",
    )
    parser.add_argument(
        "--state",
        choices=["all", "open", "closed", "merged"],
        default="all",
        help="Filter by GitHub state (default: all).",
    )
    parser.add_argument(
        "--repo",
        default="llvm/llvm-project",
        help="Target GitHub repository (default: llvm/llvm-project).",
    )
    parser.add_argument(
        "--fetch-alive2",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Fetch LLVM IR from alive2.llvm.org/ce shortlinks (default: true).",
    )
    parser.add_argument(
        "--max-links-per-item",
        type=int,
        default=5,
        help="Maximum Alive2 shortlinks to fetch per issue/PR (default: 5).",
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=4,
        help="Concurrent workers for Alive2 shortlink fetches (default: 4).",
    )
    parser.add_argument(
        "--out",
        default="-",
        help="Output JSON file path, or '-' for stdout (default: '-').",
    )
    parser.add_argument(
        "--markdown",
        default="",
        help="Optional path to write a Markdown summary table.",
    )
    parser.add_argument(
        "--tests-dir",
        default="Tests/Alive2",
        help="Directory to check for already-proved `<kind>-<id>.lean` files.",
    )
    args = parser.parse_args()

    kind_filters = (
        ["is:pull-request", "is:issue"]
        if args.kind == "all"
        else (["is:pull-request"] if args.kind == "pr" else ["is:issue"])
    )
    search_terms = [
        "alive2.llvm.org/ce",
        "Transformation seems to be correct",
    ]

    # Collect candidates from each (kind, term) query and deduplicate by number.
    by_number: dict[int, dict[str, Any]] = {}
    for kf in kind_filters:
        for term in search_terms:
            print(
                f"[search] {args.repo} {kf} \"{term}\" (up to {args.count})...",
                file=sys.stderr,
            )
            items = run_gh_search(args.repo, kf, term, args.count, args.state)
            for item in items:
                num = int(item["number"])
                if num not in by_number:
                    by_number[num] = item

    tests_dir = Path(args.tests_dir)
    records = [build_record(item, tests_dir) for item in by_number.values()]

    # Keep only items that actually contain an Alive2 link or Alive2 proof marker.
    records = [
        r for r in records if r["alive2_links"] or r["has_alive2_proof_marker"]
    ]
    records.sort(key=lambda r: (r["created_at"], r["number"]), reverse=True)
    records = records[: args.count]

    if args.fetch_alive2:
        short_ids: list[str] = []
        seen_ids: set[str] = set()
        for r in records:
            count_for_item = 0
            for url in r["alive2_links"]:
                m = ALIVE2_SHORTLINK_RE.match(url)
                if not m:
                    continue
                sid = m.group(1)
                count_for_item += 1
                if sid not in seen_ids:
                    seen_ids.add(sid)
                    short_ids.append(sid)
                if count_for_item >= args.max_links_per_item:
                    break

        print(
            f"[alive2] Fetching {len(short_ids)} unique Alive2 shortlinks...",
            file=sys.stderr,
        )
        fetched_by_id: dict[str, dict[str, Any]] = {}
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            future_map = {
                pool.submit(fetch_alive2_shortlink, sid): sid for sid in short_ids
            }
            for fut in concurrent.futures.as_completed(future_map):
                sid = future_map[fut]
                fetched_by_id[sid] = fut.result()

        for r in records:
            added = 0
            for url in r["alive2_links"]:
                m = ALIVE2_SHORTLINK_RE.match(url)
                if not m:
                    continue
                sid = m.group(1)
                if sid in fetched_by_id:
                    r["alive2_fetched"].append(fetched_by_id[sid])
                    added += 1
                if added >= args.max_links_per_item:
                    break

    output_payload = {
        "repo": args.repo,
        "count": len(records),
        "pr_count": sum(1 for r in records if r["kind"] == "pr"),
        "issue_count": sum(1 for r in records if r["kind"] == "issue"),
        "items": records,
    }

    serialized = json.dumps(output_payload, indent=2, ensure_ascii=False) + "\n"
    if args.out == "-":
        sys.stdout.write(serialized)
    else:
        out_path = Path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(serialized, encoding="utf-8")
        print(f"[done] Wrote {len(records)} items to {out_path}", file=sys.stderr)

    if args.markdown:
        md_path = Path(args.markdown)
        md_path.parent.mkdir(parents=True, exist_ok=True)
        md_path.write_text(render_markdown(records, args.repo), encoding="utf-8")
        print(f"[done] Wrote Markdown summary to {md_path}", file=sys.stderr)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
