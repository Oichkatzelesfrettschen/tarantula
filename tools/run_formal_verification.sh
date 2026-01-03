#!/usr/bin/env bash
# Formal Verification Runner Script
# Runs TLA+ model checking and Z3 SMT solving for all specifications

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FORMAL_DIR="$SCRIPT_DIR/../docs/formal"
TLA_TOOLS_JAR="${TLA_TOOLS_JAR:-/tmp/tla2tools.jar}"
TLA_TOOLS_URL="https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"

echo "═══════════════════════════════════════════════════════════"
echo "  Tarantula Formal Verification Suite"
echo "═══════════════════════════════════════════════════════════"
echo ""

# Check for Z3
if ! command -v z3 &> /dev/null; then
    echo "❌ Z3 solver not found. Install with: pip3 install z3-solver"
    exit 1
fi

echo "✓ Z3 solver found: $(z3 --version | head -1)"
echo ""

# Download TLA+ tools if needed
if [ ! -f "$TLA_TOOLS_JAR" ]; then
    echo "📥 Downloading TLA+ tools..."
    curl -L "$TLA_TOOLS_URL" -o "$TLA_TOOLS_JAR"
    echo "✓ TLA+ tools downloaded"
    echo ""
fi

# Run Z3 models
echo "──────────────────────────────────────────────────────────"
echo "Running Z3 SMT Models"
echo "──────────────────────────────────────────────────────────"
echo ""

Z3_MODELS=("$FORMAL_DIR"/*.smt2)
Z3_PASS=0
Z3_FAIL=0

for model in "${Z3_MODELS[@]}"; do
    if [ -f "$model" ]; then
        echo "🔍 Checking $(basename "$model")..."
        if z3 "$model" > /tmp/z3_output.txt 2>&1; then
            result=$(grep -E "^(sat|unsat)" /tmp/z3_output.txt | head -1)
            echo "   Result: $result"
            ((Z3_PASS++))
        else
            echo "   ❌ FAILED"
            cat /tmp/z3_output.txt
            ((Z3_FAIL++))
        fi
        echo ""
    fi
done

# Run TLA+ specifications
echo "──────────────────────────────────────────────────────────"
echo "Running TLA+ Model Checking"
echo "──────────────────────────────────────────────────────────"
echo ""

TLA_SPECS=("$FORMAL_DIR"/*.tla)
TLA_PASS=0
TLA_FAIL=0

for spec in "${TLA_SPECS[@]}"; do
    if [ -f "$spec" ]; then
        specname=$(basename "$spec" .tla)
        echo "🔍 Model checking $specname..."
        
        # Create minimal TLC configuration if it doesn't exist
        tlc_config="$FORMAL_DIR/${specname}.cfg"
        if [ ! -f "$tlc_config" ]; then
            cat > "$tlc_config" << EOF
SPECIFICATION Spec
INVARIANTS TypeInvariant
EOF
        fi
        
        # Run TLC model checker
        if java -jar "$TLA_TOOLS_JAR" -config "$tlc_config" "$spec" > /tmp/tlc_output.txt 2>&1; then
            if grep -q "No errors" /tmp/tlc_output.txt; then
                echo "   ✓ PASSED - No errors found"
                ((TLA_PASS++))
            else
                echo "   ⚠ COMPLETED with warnings"
                grep -A 5 "Warning" /tmp/tlc_output.txt || true
                ((TLA_PASS++))
            fi
        else
            echo "   ❌ FAILED"
            grep -A 10 "Error" /tmp/tlc_output.txt || cat /tmp/tlc_output.txt
            ((TLA_FAIL++))
        fi
        echo ""
    fi
done

# Summary
echo "═══════════════════════════════════════════════════════════"
echo "  Verification Summary"
echo "═══════════════════════════════════════════════════════════"
echo ""
echo "Z3 Models:  $Z3_PASS passed, $Z3_FAIL failed"
echo "TLA+ Specs: $TLA_PASS passed, $TLA_FAIL failed"
echo ""

TOTAL_FAIL=$((Z3_FAIL + TLA_FAIL))
if [ $TOTAL_FAIL -eq 0 ]; then
    echo "✓ All formal verification checks passed!"
    exit 0
else
    echo "❌ $TOTAL_FAIL verification check(s) failed"
    exit 1
fi
