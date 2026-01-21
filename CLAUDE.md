# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This repository contains Claude Code skills for formal verification. The skills translate natural language system descriptions into formal specifications and verify them using model checking tools.

## Repository Structure

```
model-check/           # Auto-selecting meta-skill (chooses TLA+/Alloy/Dafny)
model-check-tlaplus/   # TLA+ for state machines, workflows, protocols
model-check-alloy/     # Alloy for data models, taxonomies, constraints
model-check-dafny/     # Dafny for code with pre/post conditions
```

Each skill folder contains:
- `SKILL.md` - Full skill specification and documentation
- `examples/` - Working example specifications

## Running Verification Tools

**TLA+ (TLC model checker):**
```bash
tlc -workers auto -config ConfigName.cfg SpecName.tla
```

**Alloy Analyzer:**
```bash
alloy exec ModelName.als
```

**Dafny verifier:**
```bash
dafny verify FileName.dfy
```

## Tool Installation Check

```bash
tlc -h 2>/dev/null || echo "TLA+ not installed"
alloy --help 2>/dev/null || echo "Alloy not installed"
dafny --help 2>/dev/null || echo "Dafny not installed"
```

## Tool Selection Logic

| Conversation Pattern | Tool |
|---------------------|------|
| States, transitions, concurrency, "eventually"/"always" | TLA+ |
| Entities, relationships, set constraints, "exactly one" | Alloy |
| Functions, pre/post conditions, loop invariants | Dafny |

## Skill Architecture

The `model-check` skill is the primary entry point that auto-detects which tool to use. Direct variants (`model-check-tlaplus`, `model-check-alloy`, `model-check-dafny`) skip tool selection.

Workflow: Analyze conversation → Select tool → Check installation → Generate spec → Run verification → Interpret results

## Specification Naming Conventions

- Module/Spec names: `PascalCase` (e.g., `SimpleWorkflow`)
- Constants: `UPPERCASE` (e.g., `MaxTime`)
- Variables: `camelCase` (e.g., `currentState`)
- Predicates/Actions: `CamelCase` (e.g., `TypeOK`, `ParseSuccess`)

## Testing Skills

**Test auto-detection (should pick TLA+):**
"Model a mutex where two processes compete for a lock. Only one can hold it at a time."

**Test Alloy directly:**
"Use model-check-alloy: every user belongs to exactly one org, every org has at least one admin."

**Test graceful decline:**
"How do I center a div in CSS?"
→ Should respond: "Nothing to model here."

**Test installation detection:**
If a tool isn't installed, should provide installation instructions instead of failing.

## Verification Examples

Run the included examples to verify tools are working:
```bash
# TLA+
cd model-check-tlaplus/examples
tlc -workers auto -config SimpleWorkflow.cfg SimpleWorkflow.tla

# Alloy  
cd model-check-alloy/examples
alloy exec OrgStructure.als

# Dafny
cd model-check-dafny/examples
dafny verify BinarySearch.dfy
```
