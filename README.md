# LeanDisco

[![CI Status](https://github.com/namin/LeanDisco/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/namin/LeanDisco/actions/workflows/lean_action_ci.yml)
[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/namin/LeanDisco)

_Eurisko-Inspired Discovery System for Lean in Lean_

## Cloning

```bash
git clone --recursive https://github.com/namin/LeanDisco.git
```

## Running

- `lake build` builds the system.
- `lake lean Test*.lean` for some `*`.

## Plans

- Find a way to scale the Lean-in-Lean approach while experimenting with larger discovery loops, or consider an approach with an external distributed agenda queue.
- Incorporate LLMs and agentic systems to help in making discoveries.
- Generate lots of high-quality datasets (verified) for training further heuristics and LLMs.

## References

- [Software Archaeology of Eurisko](https://github.com/namin/eurisclo/tree/llm): a reflective port in Common Lisp, based on unearthed original file.
- [llmlean](https://github.com/cmu-l3/llmlean/): probably a good starting point to think about LLM integration from within Lean.
- [plausible](https://github.com/leanprover-community/plausible): property testing framework (for integration).
