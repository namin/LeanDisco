import Lean
open Lean Meta Elab Tactic

def tacticStrings : List String := [
  "rfl",
  "trivial",
  "simp",
  "ring",
  "norm_num",
  "decide",
  "assumption",
  "exact rfl",
  "apply Eq.refl",
  "simp_all",
  "ring_nf",
  "norm_cast"
]

def attemptProof (type : Expr) : TermElabM (Option Expr) := do
  let mvar ← mkFreshExprMVar type
  let goal := mvar.mvarId!

  -- First try intros if it's a forall
  let goal' ← try
    if type.isForall then
      let (_, g) ← goal.intros
      pure g
    else
      pure goal
  catch _ => pure goal

  -- Try each tactic in sequence on the intro'd goal
  for tacticStr in tacticStrings do
    try
      let env ← getEnv
      let tacticSyntax ← match Parser.runParserCategory env `tactic tacticStr with
        | .ok stx => pure stx
        | .error _ => continue

      let remainingGoals ← Tactic.run goal' do
        Tactic.evalTactic tacticSyntax

      if remainingGoals.isEmpty then
        let proof ← instantiateMVars mvar
        if !(proof.hasExprMVar) then
          return some proof
    catch _ =>
      continue

  return none
