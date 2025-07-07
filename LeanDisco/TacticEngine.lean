import LeanDisco.Types
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Meta Elab Tactic

namespace LeanDisco

-- Tactic plugin framework types

-- Priority for tactic plugins (higher = tried first)
inductive TacticPriority where
  | low : TacticPriority
  | medium : TacticPriority  
  | high : TacticPriority
  | critical : TacticPriority

-- Pattern matcher for goals that a tactic can handle
structure TacticPattern where
  description : String
  matches : Expr -> MetaM Bool
  matchesContext : Option (MVarId -> MetaM Bool) := none

-- Result of applying a tactic
inductive TacticResult where
  | solved : TacticResult  -- Goal completely solved
  | progress (subgoals : List MVarId) : TacticResult  -- Goal reduced to subgoals
  | failed (reason : String) : TacticResult  -- Tactic failed to apply

-- A tactic plugin that can solve specific types of goals
structure TacticPlugin where
  -- Unique name for the tactic plugin
  name : String
  -- Priority for this tactic (higher = tried first)
  priority : TacticPriority
  -- Patterns this tactic can handle
  patterns : List TacticPattern
  -- The tactic implementation
  apply : MVarId -> MetaM TacticResult
  -- Optional: domain this tactic is specific to
  domain : Option String := none

-- Registry for tactic plugins
structure TacticRegistry where
  -- All registered plugins, sorted by priority
  plugins : List TacticPlugin
  -- Domain-specific plugin lookup
  domainPlugins : List (String × List TacticPlugin)

-- Type for tactic plugin functions
abbrev TacticPluginFn := MVarId -> MetaM TacticResult

-- Helper functions for tactic framework

def TacticPriority.toNat : TacticPriority -> Nat
  | .low => 1
  | .medium => 2
  | .high => 3
  | .critical => 4

instance : LE TacticPriority where
  le p1 p2 := p1.toNat ≤ p2.toNat

instance : LT TacticPriority where
  lt p1 p2 := p1.toNat < p2.toNat

-- Create an empty tactic registry
def TacticRegistry.empty : TacticRegistry :=
  { plugins := [], domainPlugins := [] }

-- Register a tactic plugin
def TacticRegistry.register (registry : TacticRegistry) (plugin : TacticPlugin) : TacticRegistry :=
  let sortedPlugins := (plugin :: registry.plugins).toArray.qsort (fun p1 p2 => p1.priority.toNat > p2.priority.toNat) |>.toList
  let newDomainPlugins := match plugin.domain with
    | none => registry.domainPlugins
    | some domain =>
      match registry.domainPlugins.lookup domain with
      | none => (domain, [plugin]) :: registry.domainPlugins
      | some existing => 
        let updated := (plugin :: existing).toArray.qsort (fun p1 p2 => p1.priority.toNat > p2.priority.toNat) |>.toList
        registry.domainPlugins.filter (fun (d, _) => d != domain) ++ [(domain, updated)]
  { plugins := sortedPlugins, domainPlugins := newDomainPlugins }

-- Get plugins for a specific domain
def TacticRegistry.getForDomain (registry : TacticRegistry) (domain : String) : List TacticPlugin :=
  (registry.domainPlugins.lookup domain).getD []

-- Check if a tactic plugin can handle a goal
def TacticPlugin.canHandle (plugin : TacticPlugin) (goal : MVarId) : MetaM Bool := do
  goal.withContext do
    let goalType ← goal.getType
    for pattern in plugin.patterns do
      if ← pattern.matches goalType then
        match pattern.matchesContext with
        | none => return true
        | some contextMatcher => 
          if ← contextMatcher goal then return true
    return false

/-- Global tactic registry (mutable state) -/
private def tacticRegistryRef : IO.Ref TacticRegistry ← IO.mkRef TacticRegistry.empty

/-- Register a tactic plugin globally -/
def registerTacticPlugin (plugin : TacticPlugin) : IO Unit := do
  let registry ← tacticRegistryRef.get
  let newRegistry := registry.register plugin
  tacticRegistryRef.set newRegistry

/-- Get the current tactic registry -/
def getTacticRegistry : IO TacticRegistry := do
  tacticRegistryRef.get

/-- Apply tactic plugins to a goal, trying them in priority order -/
def applyTacticPlugins (goal : MVarId) (domain : Option String := none) : MetaM TacticResult := do
  let registry ← getTacticRegistry
  
  -- Get plugins to try (domain-specific first, then general)
  let domainPlugins := match domain with
    | none => []
    | some d => registry.getForDomain d
  let allPlugins := domainPlugins ++ registry.plugins
  
  IO.println s!"[TACTIC-ENGINE] Trying {allPlugins.length} plugins on goal"
  
  for plugin in allPlugins do
    -- Check if plugin can handle this goal
    if ← plugin.canHandle goal then
      IO.println s!"[TACTIC-ENGINE] Trying plugin: {plugin.name}"
      try
        let result ← plugin.apply goal
        match result with
        | TacticResult.solved =>
          IO.println s!"[TACTIC-ENGINE] ✓ Plugin {plugin.name} solved the goal!"
          return result
        | TacticResult.progress subgoals =>
          IO.println s!"[TACTIC-ENGINE] → Plugin {plugin.name} made progress (generated {subgoals.length} subgoals)"
          return result
        | TacticResult.failed reason =>
          IO.println s!"[TACTIC-ENGINE] ✗ Plugin {plugin.name} failed: {reason}"
      catch e =>
        IO.println s!"[TACTIC-ENGINE] ✗ Plugin {plugin.name} threw exception: {← e.toMessageData.toString}"
    else
      IO.println s!"[TACTIC-ENGINE] - Plugin {plugin.name} cannot handle this goal type"
  
  return TacticResult.failed "No applicable tactic plugins found"

/-- Enhanced version of tryBasicTactics that uses the plugin system -/
def tryExtensibleTactics (goal : MVarId) (domain : Option String := none) : MetaM Bool := do
  let result ← applyTacticPlugins goal domain
  match result with
  | TacticResult.solved => return true
  | TacticResult.progress subgoals =>
    -- Try to solve all subgoals recursively
    let mut allSolved := true
    for subgoal in subgoals do
      let subSolved ← tryExtensibleTactics subgoal domain
      if !subSolved then
        allSolved := false
    return allSolved
  | TacticResult.failed _ => return false

/-- Helper functions for creating common tactic patterns -/

/-- Pattern that matches equality goals -/
def equalityPattern (description : String) : TacticPattern :=
  { description := description
    matches := fun goalType => do
      match goalType with
      | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) _) _ => return true
      | _ => return false }

/-- Pattern that matches goals containing a specific constant -/
def constantPattern (const : Name) (description : String) : TacticPattern :=
  { description := description
    matches := fun goalType => do
      return goalType.find? (fun e => e.isConstOf const) |>.isSome }

/-- Pattern that matches goals with a specific structure -/
def structurePattern (description : String) (matcher : Expr → MetaM Bool) : TacticPattern :=
  { description := description
    matches := matcher }

/-- Core tactic plugins (basic tactics that work in any domain) -/

/-- Reflexivity tactic plugin -/
def reflexivityPlugin : TacticPlugin :=
  { name := "reflexivity"
    priority := TacticPriority.high
    patterns := [equalityPattern "reflexive equality"]
    apply := fun goal => do
      try
        let _ ← goal.refl
        return TacticResult.solved
      catch _ =>
        return TacticResult.failed "not a reflexive equality" }

/-- Assumption tactic plugin -/
def assumptionPlugin : TacticPlugin :=
  { name := "assumption"
    priority := TacticPriority.medium
    patterns := [structurePattern "any goal that matches a hypothesis" (fun _ => return true)]
    apply := fun goal => do
      try
        let _ ← goal.assumption
        return TacticResult.solved
      catch _ =>
        return TacticResult.failed "no matching assumption" }

/-- Constructor tactic plugin -/
def constructorPlugin : TacticPlugin :=
  { name := "constructor"
    priority := TacticPriority.medium
    patterns := [structurePattern "inductive type goal" (fun _ => return true)]
    apply := fun goal => do
      try
        let _ ← goal.constructor
        return TacticResult.solved
      catch _ =>
        return TacticResult.failed "no applicable constructor" }

/-- Definitional equality tactic plugin -/
def defEqPlugin : TacticPlugin :=
  { name := "definitional_equality"
    priority := TacticPriority.high
    patterns := [equalityPattern "definitional equality"]
    apply := fun goal => do
      try
        goal.withContext do
          let goalType ← goal.getType
          match goalType with
          | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) lhs) rhs =>
            let lhsWhnf ← whnf lhs
            let rhsWhnf ← whnf rhs
            if ← isDefEq lhsWhnf rhsWhnf then
              let _ ← goal.refl
              return TacticResult.solved
            else
              return TacticResult.failed "not definitionally equal"
          | _ => return TacticResult.failed "not an equality goal"
      catch _ =>
        return TacticResult.failed "definitional equality check failed" }

/-- Register core tactic plugins -/
def registerCoreTactics : IO Unit := do
  registerTacticPlugin reflexivityPlugin
  registerTacticPlugin assumptionPlugin
  registerTacticPlugin constructorPlugin
  registerTacticPlugin defEqPlugin
  IO.println "[TACTIC-ENGINE] Registered core tactic plugins"

/-- Initialize the tactic engine -/
def initializeTacticEngine : IO Unit := do
  registerCoreTactics

end LeanDisco