import Lean
import LeanDisco.DiscoverySystem
import Mathlib.Algebra.Group.Defs
import LeanDisco.Domains.GroupRing.Objects
import Lean.Elab.Term

open Lean Meta Elab Term

namespace LeanDisco.Domains.GroupRing

/-- Recognizer for unary operations α → α, possibly under implicit arguments -/
def isUnaryOp (ty : Expr) : MetaM Bool := do
  -- For now, we check if after telescoping all binders,
  -- we get something of the form α → α
  forallTelescopeReducing ty fun _fvars body => do
    match body with
    | Expr.forallE _ domain codomain _ =>
      -- Check if it's α → α (same type)
      return (← isDefEq domain codomain)
    | _ => return false

/-- Extract relevant theorems and definitions from group-related typeclasses -/
def extractGroupConcepts : MetaM (Array ConceptData) := do
  let env ← getEnv
  let all := env.constants.toList.filter (fun (n, _) =>
    let s := n.toString
    s.startsWith "MulOneClass" || s.startsWith "Group" || s.startsWith "Monoid" ||
    n == `LeanDisco.Domains.GroupRing.Objects.negate)
  let relevant ← all.filterMapM fun (name, info) => do
    let mut tags := ["group"]
    let (ty, val, isDef) ← match info with
      | .thmInfo thm => pure (thm.type, some thm.value, false)
      | .defnInfo defn => pure (defn.type, some defn.value, true)
      | _ => return none
    if name == `LeanDisco.Domains.GroupRing.Objects.negate || (← isUnaryOp ty) then
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
def buildUnaryOpEquation (pattern : UnaryOpPattern) (fname : Name) (x : Expr) : MetaM Expr := do
  let fx ← mkAppOptM fname #[none, none, some x]
  let ffx ← mkAppOptM fname #[none, none, some fx]
  match pattern with
  | .involution => mkEqStmt ffx x
  | .idempotence => mkEqStmt ffx fx

/-- Generate conjectures for unary operations based on a pattern -/
def generateUnaryOpConjectures
  (pattern : UnaryOpPattern)
  (state : DiscoveryState)
  : MetaM DiscoveryStateDelta := do

  let (suffix, tag) := match pattern with
    | .involution => ("_invol_conj", "involution")
    | .idempotence => ("_idem_conj", "idempotence")

  -- Pick out only the *new* proven unary_ops
  let candidates := state.newConcepts.filter fun c =>
    "unary_op" ∈ c.tags && c.proof?.isSome

  -- For each, build the conjecture
  let maybeNew ← candidates.mapM fun f => do
    -- Build the type with explicit arguments
    let conjTy ← withLocalDeclD `G (mkSort levelOne) fun G => do
      let GroupG ← mkAppM ``Group #[G]
      withLocalDeclD `inst GroupG fun inst => do
        withLocalDeclD `x G fun x => do
          -- Build the equation based on the pattern
          let stmt ← buildUnaryOpEquation pattern f.name x
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

  return { newConcepts := maybeNew.filterMap id }

/-- Involution heuristic: f(f(x)) = x -/
def heuristicInvolutionConjectures : DiscoveryState → MetaM DiscoveryStateDelta :=
  generateUnaryOpConjectures .involution

/-- Idempotence heuristic: f(f(x)) = f(x) -/
def heuristicIdempotenceConjectures : DiscoveryState → MetaM DiscoveryStateDelta :=
  generateUnaryOpConjectures .idempotence

end LeanDisco.Domains.GroupRing
