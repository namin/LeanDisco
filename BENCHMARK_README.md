# LeanDisco Benchmark System

A benchmark evaluation system that integrates LeanDisco's mathematical discovery capabilities with the miniF2F theorem proving dataset.

## Quick Start

### Dataset Statistics
```bash
lake lean -c "LeanDisco.Benchmarks.showDatasetStats \"benchmarks/miniF2F-lean4/minif2f_lean4.jsonl\""
```

### Quick Evaluation (3 problems)
```bash
lake lean BenchmarkEval.lean
```

### Full Benchmark (all ~244 problems)
```bash
lake lean RunFullBenchmark.lean
```

## File Structure

```
LeanDisco/Benchmarks/
├── Core.lean           # Core types and configuration
├── MiniF2F.lean        # miniF2F dataset loader
├── RealRunner.lean     # Main evaluation logic
├── Metrics.lean        # Results analysis and reporting
└── Benchmarks.lean     # Main module with utilities

Root evaluation files:
├── BenchmarkEval.lean       # Quick evaluation script
├── RunFullBenchmark.lean    # Full benchmark runner
└── TODO.md                  # Development roadmap
```

## Current Capabilities

✅ **Dataset Loading**: Loads 244 problems from miniF2F with proper JSON parsing  
✅ **Discovery Integration**: Runs LeanDisco's full discovery system on each problem  
✅ **Progress Tracking**: Shows evaluation progress and timing  
✅ **Category Analysis**: Groups results by mathematical domain  
✅ **Detailed Reports**: Generates timestamped results files  

## Current Limitations

❌ **Proof Validation**: No validation of whether discoveries actually solve the problems  
❌ **Proof Heuristics**: Generic heuristics don't effectively guide toward solutions  
❌ **Performance**: Sequential evaluation is slow for large datasets  

## Example Output

```
=== Multi-Problem Benchmark Evaluation ===
Testing 3 problems with LeanDisco discovery

--- Problem 1/3 (33%): amc12a_2019_p21 ---
Category: amc12a
Statement: theorem amc12a_2019_p21 (z : ℂ) (h₀ : z = (1 + Complex.I) / Real.sqrt 2) : ...

[... Discovery process generates 184 concepts ...]

=== EVALUATION SUMMARY ===
Total Problems: 3
Successful: 0
Failed: 3
Success Rate: 0%
Average Time: 75ms
Total Time: 226ms
```

## Development Priority

1. **Proof Validation** (Critical) - Implement proper validation of discovered proofs
2. **Enhanced Heuristics** (High) - Create problem-specific proof-seeking strategies  
3. **Performance** (Medium) - Optimize for large-scale evaluation
4. **Metrics** (Low) - Add advanced success metrics and analysis

See `TODO.md` for detailed development plan.

## Configuration

The discovery system can be configured via `DiscoveryConfig`:

```lean
let config : DiscoveryConfig := {
  maxSpecializationDepth := 2      -- Concept complexity limit
  maxConceptsPerIteration := 25    -- Generation rate control
  pruneThreshold := 0.3            -- Concept filtering threshold
  enableDebugOutput := false       -- Verbose logging
  -- ... other options
}
```

## Understanding Results

- **SUCCESS**: Discovery completed without errors (NOT proof validation)
- **FAILED**: Discovery encountered errors or timeouts
- **Concepts Generated**: Mathematical objects created during discovery
- **Category Breakdown**: Success rates by mathematical domain

**Important**: Current "success" only means discovery ran without crashing, not that proofs were found.

## Next Steps

The benchmark infrastructure is complete, but meaningful evaluation requires implementing proof validation. The system currently demonstrates LeanDisco's ability to generate rich mathematical concepts but cannot determine if these constitute valid proofs of the target problems.