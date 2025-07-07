import LeanDisco.Types
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Meta Elab Tactic

namespace LeanDisco

-- Simple extensible tactic system that works

-- Result of applying a tactic
inductive SimpleTacticResult where
  | solved : SimpleTacticResult
  | failed : SimpleTacticResult

-- A simple tactic function
abbrev SimpleTactic := MVarId -> MetaM SimpleTacticResult

-- Registry of simple tactics
def SimpleTacticRegistry := List (String × SimpleTactic)

-- Apply all registered tactics to a goal
def trySimpleTactics (tactics : SimpleTacticRegistry) (goal : MVarId) : MetaM Bool := do
  let rec loop (remaining : List (String × SimpleTactic)) : MetaM Bool := do
    match remaining with
    | [] => return false
    | (name, tactic) :: rest =>
      try
        let result ← tactic goal
        match result with
        | SimpleTacticResult.solved => return true
        | SimpleTacticResult.failed => loop rest
      catch _ => loop rest
  loop tactics

-- Core tactic implementations

def reflexivityTactic : SimpleTactic := fun goal => do
  try
    let _ ← goal.refl
    return SimpleTacticResult.solved
  catch _ =>
    return SimpleTacticResult.failed

def assumptionTactic : SimpleTactic := fun goal => do
  try
    let _ ← goal.assumption
    return SimpleTacticResult.solved
  catch _ =>
    return SimpleTacticResult.failed

def constructorTactic : SimpleTactic := fun goal => do
  try
    let _ ← goal.constructor
    return SimpleTacticResult.solved
  catch _ =>
    return SimpleTacticResult.failed

-- List-specific tactics
def listLengthNilTactic : SimpleTactic := fun goal => do
  try
    goal.withContext do
      let goalType ← goal.getType
      match goalType with
      | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) lhs) rhs =>
        -- Check if lhs is List.length [] and rhs is 0
        let isLengthNil := match lhs with
          | Expr.app (Expr.app (Expr.const ``List.length _) _) arg => arg.isAppOf ``List.nil
          | _ => false
        let isZero := rhs.isConstOf ``Nat.zero
        if isLengthNil && isZero then
          let _ ← goal.apply (mkConst ``List.length_nil)
          return SimpleTacticResult.solved
        else
          return SimpleTacticResult.failed
      | _ => return SimpleTacticResult.failed
  catch _ =>
    return SimpleTacticResult.failed

def listAppendNilTactic : SimpleTactic := fun goal => do
  try
    goal.withContext do
      let goalType ← goal.getType
      match goalType with
      | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) lhs) rhs =>
        -- Check if lhs contains List.append with nil
        let hasAppendNil := match lhs with
          | Expr.app (Expr.app (Expr.app (Expr.const ``List.append _) _) arg1) arg2 =>
            arg1.isAppOf ``List.nil || arg2.isAppOf ``List.nil
          | _ => false
        if hasAppendNil then
          -- Try nil_append first
          try
            let _ ← goal.apply (mkConst ``List.nil_append)
            return SimpleTacticResult.solved
          catch _ =>
            -- Then try append_nil
            try
              let _ ← goal.apply (mkConst ``List.append_nil)
              return SimpleTacticResult.solved
            catch _ =>
              return SimpleTacticResult.failed
        else
          return SimpleTacticResult.failed
      | _ => return SimpleTacticResult.failed
  catch _ =>
    return SimpleTacticResult.failed

def listReverseNilTactic : SimpleTactic := fun goal => do
  try
    goal.withContext do
      let goalType ← goal.getType
      match goalType with
      | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) lhs) rhs =>
        -- Check if lhs is List.reverse [] and rhs is []
        let isReverseNil := match lhs with
          | Expr.app (Expr.app (Expr.const ``List.reverse _) _) arg => arg.isAppOf ``List.nil
          | _ => false
        let isNil := rhs.isAppOf ``List.nil
        if isReverseNil && isNil then
          let _ ← goal.apply (mkConst ``List.reverse_nil)
          return SimpleTacticResult.solved
        else
          return SimpleTacticResult.failed
      | _ => return SimpleTacticResult.failed
  catch _ =>
    return SimpleTacticResult.failed

-- Get all available tactics
def getSimpleTactics : SimpleTacticRegistry := [
  ("reflexivity", reflexivityTactic),
  ("assumption", assumptionTactic),
  ("constructor", constructorTactic),
  ("list_length_nil", listLengthNilTactic),
  ("list_append_nil", listAppendNilTactic),
  ("list_reverse_nil", listReverseNilTactic)
]

end LeanDisco