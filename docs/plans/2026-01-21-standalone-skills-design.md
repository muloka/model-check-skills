# Standalone Skills Distribution Design

**Date:** 2026-01-21
**Status:** Ready for implementation

## Goal

Package model-check skills for distribution via GitHub as standalone Claude Code skills.

## Decision

Use **standalone skills** (not a plugin) because:
- Readers can cherry-pick individual skills
- Simpler installation instructions for article
- Cleaner skill names (`/model-check-tlaplus` vs `/model-check:tlaplus`)
- No plugin manifest to maintain

## Changes

### 1. README.md

**Update installation instructions:**
```markdown
## Installation

Copy the skill folders you want to your Claude Code skills directory:

```bash
# All skills (personal - available in all projects)
cp -r model-check ~/.claude/skills/
cp -r model-check-tlaplus ~/.claude/skills/
cp -r model-check-alloy ~/.claude/skills/
cp -r model-check-dafny ~/.claude/skills/

# Or project-specific
mkdir -p .claude/skills
cp -r model-check* .claude/skills/
```

**Update examples listing (line 80):**
```markdown
- `model-check-tlaplus/examples/` — SimpleWorkflow.tla, TrafficLight.tla
```

**Remove broken links (lines 86-88):**
Delete the "Further Reading" internal links that don't resolve.

### 2. model-check/SKILL.md (lines 363-365)

**Change from:**
```
- `model-check:tlaplus` — Skip tool selection, use TLA+
- `model-check:alloy` — Skip tool selection, use Alloy
- `model-check:dafny` — Skip tool selection, use Dafny
```

**To:**
```
- `/model-check-tlaplus` — Skip tool selection, use TLA+
- `/model-check-alloy` — Skip tool selection, use Alloy
- `/model-check-dafny` — Skip tool selection, use Dafny
```

### 3. .claude/settings.local.json

**Update to:**
```json
{
  "permissions": {
    "allow": [
      "Bash(tlc:*)",
      "Bash(alloy:*)",
      "Bash(dafny:*)"
    ]
  }
}
```

### 4. test-examples.sh (new file)

```bash
#!/bin/bash
# Test that verification tools work with example specs
set -e

echo "=== Testing TLA+ examples ==="
if command -v tlc &> /dev/null; then
    tlc -workers auto -config model-check-tlaplus/examples/SimpleWorkflow.cfg model-check-tlaplus/examples/SimpleWorkflow.tla
    tlc -workers auto -config model-check-tlaplus/examples/TrafficLight.cfg model-check-tlaplus/examples/TrafficLight.tla
    echo "TLA+ examples: PASS"
else
    echo "TLA+ (tlc) not installed, skipping"
fi

echo ""
echo "=== Testing Dafny examples ==="
if command -v dafny &> /dev/null; then
    dafny verify model-check-dafny/examples/BinarySearch.dfy
    dafny verify model-check-dafny/examples/Max.dfy
    echo "Dafny examples: PASS"
else
    echo "Dafny not installed, skipping"
fi

echo ""
echo "=== Testing Alloy examples ==="
if command -v alloy &> /dev/null; then
    alloy exec model-check-alloy/examples/OrgStructure.als
    echo "Alloy examples: PASS"
else
    echo "Alloy not installed, skipping"
fi

echo ""
echo "=== Done ==="
```

## Verification

After implementation:
1. Copy skills to a test location
2. Verify Claude Code discovers them with `/model-check-tlaplus`
3. Run `test-examples.sh` (requires tools installed)
