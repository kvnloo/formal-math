"""Map Conjectures.io bounty task ids onto theorems in the local formal-conjectures checkout.

Usage: python3 -I map_bounties.py TASKS_JSON FC_DIR OUT_JSON
Task id shape: fc-v2-<filestem><sep><theorem-slug>-<24 hex>-(proof|counterexample)
"""
import json, re, sys
from pathlib import Path

tasks_json, fc, out = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
tasks = json.loads(tasks_json.read_text())["tasks"]
ids = sorted({re.sub(r"-(proof|counterexample)$", "", t["task_id"]) for t in tasks})

DECL = re.compile(r"^(?:@\[(?P<attr>[^\]]*)\]\s*\n)?\s*theorem\s+(?P<name>[^\s:({\[]+)", re.M)
CAT = re.compile(r"category\s+(research open|research solved|textbook|test|API)")
index = {}
for f in (fc / "FormalConjectures").rglob("*.lean"):
    txt = f.read_text(errors="replace")
    for m in DECL.finditer(txt):
        name = m.group("name")
        cat = CAT.search(m.group("attr") or "")
        slug = re.sub(r"[^a-z0-9]+", "-", name.split(".")[-1].lower()).strip("-")
        for raw in (f.stem, f.parent.name + f.stem, f.parent.name.replace("Problems", "") + f.stem):
            stem = re.sub(r"[^a-z0-9]", "", raw.lower())
            index.setdefault((stem, slug), []).append({
                "file": str(f.relative_to(fc)), "theorem": name,
                "category": cat.group(1) if cat else None})

rows = []
for tid in ids:
    m = re.match(r"fc-v2-(.+?)-([0-9a-f]{24})(-formalized)?$", tid)
    body = m.group(1) if m else tid
    hit = None
    for (stem, slug), v in index.items():
        if body == f"{stem}-{slug}" or (body.startswith(stem + "-") and body[len(stem) + 1:] == slug):
            hit = v
            break
    rows.append({"task": tid, "matches": hit or []})
out.write_text(json.dumps(rows, indent=1))
n = sum(1 for r in rows if r["matches"])
print(f"tasks={len(rows)} mapped={n}")
cats = {}
for r in rows:
    for x in r["matches"][:1]:
        cats[x["category"]] = cats.get(x["category"], 0) + 1
print("categories:", cats)
