# LeanDisco Improvement Plan

## Executive Summary
We have achieved **99.6% dataset coverage** (486/488 problems) but **0% solve rate**. The next phase focuses on fixing the core proving mechanism to achieve our first theorem proof breakthrough.

## Current Status
- ✅ **Dataset Coverage**: 486/488 problems (removed 1 problematic theorem)
- ✅ **Infrastructure**: Stable benchmark framework, enhanced configuration
- ❌ **Solve Rate**: 0% across all complexity levels (including trivial theorems)
- ❌ **Core Issue**: Application heuristic and goal validation failures

## Phase 1: Core Proving Mechanism (Priority: Critical)

### 1.1 Debug Application Heuristic (Week 1)
**Objective**: Fix why "61 seed functions, 67 potential arguments" → 0 concepts

**Tasks**:
- [ ] Add detailed logging to application heuristic in `LeanDisco/Basic.lean`
- [ ] Identify where function applications fail (type checking, filtering, errors)
- [ ] Create minimal test case with 1-2 seed functions
- [ ] Test function application in isolation
- [ ] Fix identified bugs in application logic

**Success Metric**: Application heuristic generates >0 concepts

### 1.2 Implement Basic Proof Tactics (Week 1-2)
**Objective**: Add fundamental Lean proof tactics to LeanDisco

**Tasks**:
- [ ] Research LeanDisco's current tactic support
- [ ] Implement `trivial` tactic for proving `True`
- [ ] Implement `refl` tactic for reflexivity (`x = x`)
- [ ] Implement `rfl` for definitional equality 
- [ ] Test each tactic with minimal examples
- [ ] Create tactic application heuristic

**Success Metric**: Prove `True` and `∀ x : Nat, x = x`

### 1.3 Fix Goal Validation (Week 2)
**Objective**: Resolve "Theorem not found in environment" errors

**Tasks**:
- [ ] Debug goal creation and environment loading
- [ ] Trace theorem name resolution process
- [ ] Fix type mismatches between goals and proofs
- [ ] Add comprehensive goal validation logging
- [ ] Test with known-good theorem examples

**Success Metric**: Goals properly recognized and validated

## Phase 2: Simple Algebraic Proofs (Week 3-4)

### 2.1 Implement Ring Tactic
**Objective**: Prove basic algebraic theorems like `7 * (3 * y + 2) = 21 * y + 14`

**Tasks**:
- [ ] Add `ring` tactic support for polynomial arithmetic
- [ ] Test on `mathd_algebra_182` (distributive property)
- [ ] Implement algebraic simplification heuristics
- [ ] Add arithmetic concept generation

**Success Metric**: 5-10% solve rate on simple algebraic theorems

### 2.2 Expand Mathematical Knowledge
**Objective**: Add domain-specific mathematical concepts

**Tasks**:
- [ ] Add number theory concepts (gcd, prime, factorial)
- [ ] Add basic arithmetic properties (commutativity, associativity)
- [ ] Create concept hierarchies for different mathematical domains
- [ ] Test on number theory problems

**Success Metric**: 10-15% solve rate across multiple domains

## Phase 3: Advanced Proving (Week 5-6)

### 3.1 Implement Simp Tactic
**Objective**: Add powerful simplification for complex expressions

**Tasks**:
- [ ] Integrate `simp` tactic with custom simp lemmas
- [ ] Add rewriting capabilities for complex expressions
- [ ] Test on trigonometric and logarithmic problems

### 3.2 Goal-Directed Search Enhancement
**Objective**: Improve connection between discovery and proving

**Tasks**:
- [ ] Enhance goal-directed concept generation
- [ ] Add backwards reasoning from goals
- [ ] Implement lemma suggestion based on goal structure
- [ ] Add proof search strategies

**Success Metric**: 20%+ solve rate on representative MiniF2F subset

## Implementation Strategy

### Development Approach
1. **Minimal Working Examples**: Start with absolute simplest cases
2. **Incremental Testing**: Test each component in isolation
3. **Systematic Debugging**: Comprehensive logging at each step
4. **Proof-of-Concept First**: Get 1 theorem working before scaling

### Testing Protocol
1. **Unit Tests**: Test each tactic/heuristic individually
2. **Integration Tests**: Test with simple theorem sets
3. **Regression Tests**: Ensure changes don't break existing functionality
4. **Performance Tests**: Monitor discovery time and resource usage

### Success Milestones

**Week 1**: 
- ✅ Application heuristic generates concepts
- ✅ Prove `True` (first theorem breakthrough!)

**Week 2**:
- ✅ Prove 3-5 trivial theorems 
- ✅ Goal validation working correctly

**Week 3**:
- ✅ 5% solve rate on simple algebra
- ✅ Prove distributive property examples

**Week 4**:
- ✅ 10% solve rate across multiple domains
- ✅ Number theory and arithmetic theorems

**Week 5-6**:
- ✅ 20%+ solve rate on representative subset
- ✅ Complex expression simplification

## Risk Mitigation

### Technical Risks
- **Deep LeanDisco internals**: May need to modify core discovery engine
- **Lean integration complexity**: Tactic implementation may be challenging
- **Performance regression**: Adding features might slow down discovery

### Mitigation Strategies
- **Incremental approach**: Small changes with frequent testing
- **Expert consultation**: Reach out to LeanDisco authors if needed
- **Fallback options**: Keep working configurations as backups
- **Documentation**: Thorough documentation of all changes

## Resource Requirements

### Files to Modify
- `LeanDisco/Basic.lean` - Core discovery engine
- `LeanDisco/Benchmarks/RealRunner.lean` - Goal validation
- `TestBenchmarks.lean` - Test configuration
- New files for tactic implementations

### Knowledge Dependencies
- Lean 4 tactic development
- LeanDisco architecture understanding
- Mathematical theorem proving strategies
- Metaprogramming in Lean

## Tracking and Metrics

### Key Performance Indicators
- **Solve Rate**: % of theorems successfully proven
- **Discovery Time**: Time per successful proof
- **Concept Quality**: Relevance of generated concepts to goals
- **Coverage**: Domains/complexity levels where solving works

### Reporting
- **Daily**: Progress on current milestone, blockers identified
- **Weekly**: Solve rate metrics, successful theorem examples
- **Milestone**: Comprehensive testing results, next phase planning

## Conclusion
This plan focuses on the fundamental proving mechanism first, then builds mathematical capabilities incrementally. The goal is not just to increase solve rates, but to create a robust foundation for mathematical theorem proving that can scale to the full MiniF2F dataset.

**Success Definition**: Achieve 20%+ solve rate on a representative subset of mathematical problems, demonstrating that LeanDisco can be an effective automated theorem prover.