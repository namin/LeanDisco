#!/bin/bash

# Script to run TestBenchmarks.lean with proper stack size
# This addresses the stack overflow issue when running the benchmark

echo "Running LeanDisco benchmarks with increased stack size..."
echo "This may take a while as it processes many mathematical problems."

# Try multiple approaches to increase stack size
echo "Setting stack size limits..."

# Set process stack size limit (if possible)
ulimit -s 16384 2>/dev/null || echo "Warning: Could not increase ulimit stack size"

# Set larger stack size for Lean (try multiple values)
export LEAN_STACK_SIZE=16777216  # 16MB stack

echo "Stack size set to: $(ulimit -s) kbytes"
echo "LEAN_STACK_SIZE set to: $LEAN_STACK_SIZE bytes"

# Run the benchmark
lake lean TestBenchmarks.lean

echo "Benchmark run completed."