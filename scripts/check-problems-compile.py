from pathlib import Path
from subprocess import run

mzns = Path(__file__).parent.parent.glob("problems/*/*.mzn")

for mzn in mzns:
    for df in mzn.parent.glob("data/*.json"):
        print(f"Checking {mzn.parent.name} ({mzn.name} with {df.name})")
        proc = run(
            [
                "minizinc",
                "--solver",
                "org.minizinc.mzn-fzn",
                "-c",
                "--output-fzn-to-stdout",
                "--output-ozn-to-stdout",
                mzn,
                df,
            ],
            capture_output=True,
            text=True,
        )
        if proc.returncode != 0:
            print(proc.stderr)
