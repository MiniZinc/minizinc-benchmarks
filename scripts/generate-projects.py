from pathlib import Path
import json

root = Path(__file__).parent.parent
for mzn in root.glob("todo/working/*/*.mzn"):
    p = mzn.parent
    data_files = [df.relative_to(p).as_posix() for df in p.glob("data/*.json")]
    mzn_file = mzn.relative_to(p).as_posix()
    project_files = [mzn_file] + data_files
    project = {
        "version": 105,
        "projectFiles": project_files,
        "openFiles": [mzn_file],
        "selectedBuiltinConfigId": "org.gecode.gecode",
        "selectedBuiltinConfigVersion": "default",
    }
    target = p / f"{p.name}.mzp"
    target.write_text(json.dumps(project, indent=2), encoding="utf-8")