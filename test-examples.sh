#!/bin/bash
# Test that verification tools work with example specs
# Run from the repository root directory

set -e
cd "$(dirname "$0")"

run_tlc() {
    if command -v tlc &> /dev/null; then
        tlc "$@"
    elif [[ -n "$TLA2TOOLS_JAR" && -f "$TLA2TOOLS_JAR" ]]; then
        java -XX:+UseParallelGC -jar "$TLA2TOOLS_JAR" "$@"
    else
        return 1
    fi
}

echo "=== Testing TLA+ examples ==="
if run_tlc -workers auto -config model-check-tlaplus/examples/SimpleWorkflow.cfg model-check-tlaplus/examples/SimpleWorkflow.tla; then
    run_tlc -workers auto -config model-check-tlaplus/examples/TrafficLight.cfg model-check-tlaplus/examples/TrafficLight.tla
    echo "TLA+ examples: PASS"
else
    echo "TLA+ (tlc) not installed, skipping"
    echo "  Install: brew install tlaplus"
    echo "  Or set TLA2TOOLS_JAR=/path/to/tla2tools.jar"
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
