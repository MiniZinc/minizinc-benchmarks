from pathlib import Path
from subprocess import run

here = Path(__file__).parent
converter = here / "dzn2json.mzn"

root = here.parent
for dzn in root.glob("todo/working/*/data/*.dzn"):
    target = dzn.with_suffix(".json")
    if target.exists():
        # print(f"{dzn} already has a JSON file, skipping.")
        continue
    print(f"Converting {dzn} to JSON.")
    [mzn] = dzn.parent.parent.glob("*.mzn")
    proc = run(["minizinc", converter, mzn, dzn], capture_output=True, text=True)
    result = proc.stdout
    if "dzn2json" not in proc.stderr:
        print(f"Error converting {dzn} to JSON: {proc.stderr}")
        continue
    target.write_text(result, encoding="utf-8")
