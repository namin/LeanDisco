# LeanDisco

[![CI Status](https://github.com/namin/LeanDisco/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/namin/LeanDisco/actions/workflows/lean_action_ci.yml)

_Eurisko-Inspired Discovery System for Lean in Lean_

See [LeanDisco.lean](LeanDisco.lean) for the code.
See sample outputs in [log](log) directory.

## Running

`lake build` builds the system.
You can use `lake lean TestFiniteFields.lean` as an example for running a `Test*` file directly.
All these files can also be ran interactively in the VSCode Lean extension.

## References

- [Software Archaeology of Eurisko](https://github.com/namin/eurisclo/tree/llm): a reflective port in Common Lisp, based on unearthed original file.
- [llmlean](https://github.com/cmu-l3/llmlean/): probably a good starting point to think about LLM integration from within Lean.
