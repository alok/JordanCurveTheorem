#!/usr/bin/env python3
"""Build every Comparator solution locally, without compiling the intentional challenge holes."""

import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
configs = sorted((root / "Verification").glob("*.json"))
if not configs:
    raise SystemExit("No Comparator configurations found")
solutions = sorted({json.loads(path.read_text())["solution_module"] for path in configs})
print(f"Checking {len(solutions)} Comparator solutions and the transfer regressions.", flush=True)
subprocess.run(
    ["lake", "--wfail", "build", "Reeken", "Verification.TransferTests", *solutions],
    cwd=root,
    check=True,
)
