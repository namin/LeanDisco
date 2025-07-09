# LeanDisco Benchmark System

Integrates LeanDisco's mathematical discovery with the miniF2F theorem proving dataset.

## Quick Start

```bash
# Full benchmark (all ~244 problems by default)
lake lean TestBenchmarks.lean

# Edit TestBenchmarks.lean to uncomment lines for smaller test runs:
# - 3 problems: runBenchmarks (some 3) none false true
# - 10 valid problems: runBenchmarks (some 10) (some "valid") false true
# - 50 problems: runBenchmarks (some 50) none false true
```

## Current Status

✅ **Working**: Dataset loading, discovery integration, progress tracking  
❌ **Needs Work**: Proof validation, complex statement parsing

## Key Files

- `LeanDisco/Benchmarks/RealRunner.lean` - Main evaluation logic
- `LeanDisco/Benchmarks/MiniF2F.lean` - Dataset loader  
- `TestBenchmarks.lean` - Configurable benchmark runner