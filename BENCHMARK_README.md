# LeanDisco Benchmark System

Integrates LeanDisco's mathematical discovery with the miniF2F theorem proving dataset.

## Quick Start

```bash
# Quick evaluation (3 problems)
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
- `BenchmarkEval.lean` - Quick evaluation script