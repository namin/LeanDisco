import Lean
import LeanDisco.DiscoverySystem
import Mathlib.Algebra.Group.Defs
import LeanDisco.Domains.GroupRing.Objects
import Lean.Elab.Term

open Lean Meta Elab Term

namespace LeanDisco.Domains.GroupRing

/-- Recognizer for unary operations α → α, possibly under implicit arguments -/
def isUnaryOp (ty : Expr) : MetaM Bool := do
  -- Count explicit arguments and check type matching
  forallTelescope ty fun fvars body => do
    -- Count only explicit arguments
    let mut numExplicit := 0
    let mut lastExplicitArgType? := none

    for i in [:fvars.size] do
      let fvar := fvars[i]!
      let fvarDecl ← fvar.fvarId!.getDecl
      if fvarDecl.binderInfo.isExplicit then
        numExplicit := numExplicit + 1
        lastExplicitArgType? := some (← inferType fvar)

    -- We want exactly one explicit argument
    if numExplicit != 1 then
      return false

    -- Check if the last explicit argument type matches the return type
    match lastExplicitArgType? with
    | some argType => isDefEq argType body
    | none => return false

/-- Extract relevant theorems and definitions from group-related typeclasses -/
def extractGroupConcepts : MetaM (Array ConceptData) := do
  let env ← getEnv
  let all := env.constants.toList.filter (fun (n, info) =>
    let s := n.toString
    -- Include items from group-related namespaces
    s.startsWith "MulOneClass" || s.startsWith "Group" || s.startsWith "Monoid" ||
    s.startsWith "DivInvMonoid" || s.startsWith "Inv" ||
    -- Include our custom definitions
    n.toString.startsWith "LeanDisco.Domains.GroupRing.Objects" ||
    -- Include theorems that mention group operations
    (match info with
     | .thmInfo _ =>
       -- Simple check: does the name contain inv, mul, one, or cancel?
       let parts := s.splitOn "_"
       parts.any (fun p => p == "inv" || p == "mul" || p == "one" || p == "cancel") ||
       s.endsWith "inv" || s.endsWith "mul" || s.endsWith "cancel"
     | _ => false))
  let relevant ← all.filterMapM fun (name, info) => do
    let mut tags := ["group"]
    let (ty, val, isDef) ← match info with
      | .thmInfo thm => pure (thm.type, some thm.value, false)
      | .defnInfo defn => pure (defn.type, some defn.value, true)
      | _ => return none
    if isDef && (← isUnaryOp ty) then
      tags := "unary_op" :: tags
    return some {
      name := name,
      type := ty,
      proof? := val,
      isDef := isDef,
      isProp := !isDef,
      origin? := some "GroupRing",
      tags := tags,
      contexts := #[]
    }
  return relevant.toArray

/-- Group/Ring domain instance -/
def GroupRingDomain : DiscoveryDomain where
  name := "GroupRing"
  seed := extractGroupConcepts

/-- Build a properly‐universe‐polymorphic `Eq.{u} α lhs rhs`. -/
def mkEqStmt (lhs rhs : Expr) : MetaM Expr := do
  let α ← inferType lhs
  let sort ← inferType α
  let u ← match sort with
    | Expr.sort (.succ u) .. => pure u
    | _              => throwError "mkEqStmt: expected type of {α} to be a Type, got {sort}"
  let eqConst := Lean.mkConst ``Eq [u]
  pure $ mkAppN eqConst #[α, lhs, rhs]

/-- Types of unary operation conjectures we can generate -/
inductive UnaryOpPattern
  | involution  -- f(f(x)) = x
  | idempotence -- f(f(x)) = f(x)
  deriving BEq

/-- Build the equation for a given pattern -/
def buildUnaryOpEquation (pattern : UnaryOpPattern) (fname : Name) (G inst x : Expr) : MetaM Expr := do
  let fx ← mkAppOptM fname #[some G, some inst, some x]
  let ffx ← mkAppOptM fname #[some G, some inst, some fx]
  match pattern with
  | .involution => mkAppM ``Eq #[ffx, x]
  | .idempotence => mkAppM ``Eq #[ffx, fx]

/-- Generate conjectures for unary operations based on a pattern -/
def generateUnaryOpConjectures
  (pattern : UnaryOpPattern)
  (state : DiscoveryState)
  : MetaM DiscoveryStateDelta := do

  let (suffix, tag) := match pattern with
    | .involution => ("_invol", "involution")
    | .idempotence => ("_idem", "idempotence")

  -- Pick out only the *new* proven unary_ops
  let candidates := state.newConcepts.filter fun c =>
    "unary_op" ∈ c.tags && c.proof?.isSome

  -- For each, build the conjecture
  let maybeNew ← candidates.mapM fun f => do
    try
      -- Build the type with explicit arguments
      let conjTy ← withLocalDeclD `G (mkSort levelOne) fun G => do
        let GroupG ← mkAppM ``Group #[G]
        withLocalDeclD `inst GroupG fun inst => do
          withLocalDeclD `x G fun x => do
            -- Build the equation based on the pattern
            let stmt ← buildUnaryOpEquation pattern f.name G inst x
            -- Create forall with explicit arguments
            mkForallFVars #[G, inst, x] stmt

      let name := f.name.appendAfter suffix
      return (some {
        name     := name,
        type     := conjTy,
        proof?   := none,
        isDef    := false,
        isProp   := true,
        origin?  := some suffix,
        tags     := ["generated", tag],
        contexts := #[]
      } : Option ConceptData)
    catch e =>
      -- Skip functions that don't work with Group
      return none

  return { newConcepts := maybeNew.filterMap id }

/-- Involution heuristic: f(f(x)) = x -/
def heuristicInvolutionConjectures : DiscoveryState → MetaM DiscoveryStateDelta :=
  generateUnaryOpConjectures .involution

/-- Idempotence heuristic: f(f(x)) = f(x) -/
def heuristicIdempotenceConjectures : DiscoveryState → MetaM DiscoveryStateDelta :=
  generateUnaryOpConjectures .idempotence

end LeanDisco.Domains.GroupRing
