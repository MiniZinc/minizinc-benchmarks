from pathlib import Path
from subprocess import run
import json
import re


def canonical_global(g):
    if g == "alldifferent":
        return "all_different"
    if g == "alldifferent_except_0":
        return "all_different_except_0"
    return g


if __name__ == "__main__":
    root = Path(__file__).parent.parent / "problems"
    sbc = r"^([^%]*[^\w%])?symmetry_breaking_constraint\s*\("
    rc = r"^([^%]*[^\w%])?redundant_constraint\s*\("
    for mzn in root.rglob("*.mzn"):
        try:
            dzn = next(mzn.parent.rglob("*.dzn"))
        except StopIteration:
            try:
                dzn = next(mzn.parent.glob("*.json"))
            except StopIteration:
                dzn = None
        target = Path(mzn.parent / "metadata.json")
        if target.exists():
            continue
        problem = mzn.relative_to(root).parts[0]
        contents = mzn.read_text(encoding="utf-8")
        has_sbc = re.search(sbc, contents, re.M) is not None
        has_rc = re.search(rc, contents, re.M) is not None
        args = ["minizinc", "--model-interface-only", mzn.as_posix()]
        if dzn is not None:
            args.append(dzn.as_posix())
        p = run(args, capture_output=True)
        try:
            obj = json.loads(p.stdout)
            result = {
                "name": mzn.parent.name,
                "type": "UNKNOWN",
                "kind": obj["method"],
                "sbc": has_sbc,
                "rc": has_rc,
                "globals": [canonical_global(g) for g in obj["globals"]],
                "challenges": [],
            }
            target.write_text(json.dumps(result, indent=2), encoding="utf-8")
        except Exception as e:
            print(f"Failed to get problem info for {mzn}: {e}")
