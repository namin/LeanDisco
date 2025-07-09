# LeanDisco Benchmark System

Integrates LeanDisco's mathematical discovery with the miniF2F theorem proving dataset.

## Quick Start

```bash
# Quick test (3 problems by default)
lake lean TestBenchmarks.lean

# Edit TestBenchmarks.lean to uncomment lines for:
# - 50 problems: runBenchmarks (some 50) none false true
# - All test problems: runBenchmarks none (some "test") false true  
# - ALL problems: runBenchmarks none none false true
```

## Current Status

✅ **Working**: Dataset loading, discovery integration, progress tracking  
❌ **Needs Work**: Proof validation, complex statement parsing

## Key Files

- `LeanDisco/Benchmarks/RealRunner.lean` - Main evaluation logic
- `LeanDisco/Benchmarks/MiniF2F.lean` - Dataset loader  
- `TestBenchmarks.lean` - Configurable benchmark runner