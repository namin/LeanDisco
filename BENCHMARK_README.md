# LeanDisco Benchmark System

Integrates LeanDisco's mathematical discovery with the miniF2F theorem proving dataset.

## Quick Start

```bash
# Test benchmark integration
lake lean TestBenchmarks.lean

# Simple evaluation (3 problems)
lake lean BenchmarkEval.lean

# Full benchmark (244 problems)
lake lean RunFullBenchmark.lean
```

## Current Status

✅ **Working**: Dataset loading, discovery integration, progress tracking  
❌ **Needs Work**: Proof validation, complex statement parsing

## Key Files

- `LeanDisco/Benchmarks/RealRunner.lean` - Main evaluation logic
- `LeanDisco/Benchmarks/MiniF2F.lean` - Dataset loader  
- `TestBenchmarks.lean` - Simple integration test
- `BenchmarkEval.lean` - Quick evaluation script