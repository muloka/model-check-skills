# model-check Skills

Formal verification skills for Claude Code. Generate and verify formal models from natural language system descriptions.

## Skills

| Skill | Use Case | Tool |
|-------|----------|------|
| `model-check` | Auto-select based on context | TLA+, Alloy, or Dafny |
| `model-check-tlaplus` | State machines, workflows, protocols | TLC model checker |
| `model-check-alloy` | Data models, taxonomies, constraints | Alloy Analyzer |
| `model-check-dafny` | Code with pre/post conditions | Dafny verifier |

## Installation

Copy the skill folders you want to your Claude Code skills directory:

```bash
# All skills (personal - available in all projects)
cp -r model-check ~/.claude/skills/
cp -r model-check-tlaplus ~/.claude/skills/
cp -r model-check-alloy ~/.claude/skills/
cp -r model-check-dafny ~/.claude/skills/

# Or just the ones you need
cp -r model-check-tlaplus ~/.claude/skills/
```

For project-specific use:

```bash
mkdir -p .claude/skills
cp -r model-check* .claude/skills/
```

## Tool Requirements

The skills will check for tool installation and provide instructions if missing.

| Tool | Installation | Difficulty |
|------|--------------|------------|
| Dafny | `dotnet tool install --global dafny` | Easy |
| Alloy | `brew install alloy` or download JAR | Medium |
| TLA+ | `brew install tlaplus` or download toolbox | Medium |

## Usage

Describe a system in conversation. Claude will:

1. Detect if there's something modelable
2. Select the appropriate tool (or ask)
3. Check tool installation
4. Generate the specification
5. Run verification
6. Report results with clear explanations

### Example: State Machine

> "I'm building an approval workflow. Requests start pending, can be approved or rejected. Approved requests can be revoked within 24 hours."

Claude generates a TLA+ spec and verifies termination, deadlock-freedom, and temporal constraints.

### Example: Data Model

> "Every user belongs to exactly one organization. Organizations must have at least one admin."

Claude generates an Alloy spec and verifies the constraints are satisfiable and complete.

### Example: Algorithm

> "Write a binary search that returns the index if found, -1 otherwise. The input array is sorted."

Claude generates Dafny code with pre/post conditions and verifies correctness.

## Graceful Decline

If no formal system is detected, Claude will explain what's needed:

> "I don't see a state machine, workflow, or formal structure to model. Model checking is useful for systems with states and transitions. Can you describe what you're building?"

## Examples

Each skill folder contains example specifications:

- `model-check-tlaplus/examples/` — SimpleWorkflow.tla, TrafficLight.tla
- `model-check-alloy/examples/` — OrgStructure.als
- `model-check-dafny/examples/` — BinarySearch.dfy, Max.dfy

## Further Reading

- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html) — Learn TLA+
- [Practical Alloy](https://practicalalloy.github.io/) — Learn Alloy
- [Dafny Documentation](https://dafny.org/dafny/) — Learn Dafny

## License

MIT
