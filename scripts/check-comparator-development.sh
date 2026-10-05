#!/usr/bin/env bash
set -euo pipefail

# DEVELOPMENT ONLY. This explicitly unsandboxed check is useful on macOS.
# It is not Palomar mechanical preflight or a secure independent evaluation.
# Never invoke this script from submission CI or describe its result as such.
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
echo "DEVELOPMENT ONLY: unsandboxed Comparator; this is not Palomar preflight." >&2
python3 scripts/check-lean-sources.py

prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: selected toolchain does not bundle $tool" >&2
    exit 1
  fi
done
config=$(mktemp "${TMPDIR:-/tmp}/fluid-development-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
if not isinstance(config, dict) or "external_kernels" in config:
    raise SystemExit("Comparator configuration must be an object without external_kernels")
permitted = config.get("permitted_axioms")
if not isinstance(permitted, list) or any(
    axiom not in {"propext", "Quot.sound", "Classical.choice"} for axiom in permitted
):
    raise SystemExit("Comparator must permit only the standard three axioms")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

lake comparator --config "$config" --paranoid --inadvisably-no-sandbox
