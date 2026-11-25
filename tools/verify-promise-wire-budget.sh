#!/usr/bin/env bash
set -euo pipefail

task_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if ! command -v lake >/dev/null 2>&1; then
  task_elan_bin="${ELAN_HOME:-$HOME/.elan}/bin"
  if [ -x "$task_elan_bin/lake" ]; then
    export PATH="$task_elan_bin:$PATH"
  else
    echo 'Install elan and the repository-pinned Lean toolchain first.' >&2
    exit 1
  fi
fi

audit_log="$(mktemp)"
trap 'rm -f "$audit_log"' EXIT
cd "$task_root/lean"
lake build PEqualNP.Research.PromiseWireBudget
lake env lean "$task_root/research/VerifyPromiseWireBudget.lean" | tee "$audit_log"
python3 - "$audit_log" <<'PY'
import pathlib, re, sys
text = pathlib.Path(sys.argv[1]).read_text()
if re.search(r'\berror\b', text):
    raise SystemExit('Lean reported an error during verification.')
audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
if len(audits) != 7:
    raise SystemExit(f'Expected seven theorem axiom audits, received {len(audits)}.')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, axioms in audits:
    found = {a.strip() for a in axioms.split(',') if a.strip()}
    if found - allowed:
        raise SystemExit(f'{name} uses unexpected axioms: {sorted(found - allowed)}')
print('PASS: examples compile; seven theorem audits use only the standard allowed axioms.')
PY
