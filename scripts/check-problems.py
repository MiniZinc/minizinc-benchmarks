from pathlib import Path
from subprocess import run

mzns = Path(__file__).parent.parent.glob("todo/working/*/*.mzn")

for mzn in mzns:
    for df in mzn.parent.glob("data/*.json"):
        print(f"Checking {mzn.parent.name} ({mzn.name} with {df.name})")
        proc = run(["minizinc", "--solver", "gecode", "--model-check-only", mzn, df], capture_output=True, text=True)
        if proc.returncode != 0:
            print(proc.stderr)
