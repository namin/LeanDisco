
import Mathlib.Algebra.Group.Defs

namespace LeanDisco.Domains.GroupRing.Objects

variable {G : Type} [Group G]

/-- The negate operation: x ↦ x⁻¹ -/
@[simp]
def negate (x : G) : G := x⁻¹

/-- Conjugation by a fixed element: x ↦ axa⁻¹ -/
def conjugateBy (a : G) (x : G) : G := a * x * a⁻¹

/-- Squaring operation: x ↦ x² -/
@[simp]
def square (x : G) : G := x * x

/-- Commutator with a fixed element: x ↦ [a,x] = axa⁻¹x⁻¹ -/
def commutatorWith (a : G) (x : G) : G := a * x * a⁻¹ * x⁻¹

/-- Inverse square: x ↦ (x⁻¹)² -/
def inverseSquare (x : G) : G := x⁻¹ * x⁻¹

/-- Triple: x ↦ x³ -/
def triple (x : G) : G := x * x * x

/-- The identity function (for testing) -/
@[simp]
def identity (x : G) : G := x

/-- Conjugation by a²: x ↦ a²xa⁻² -/
def conjugateBySquare (a : G) (x : G) : G := a * a * x * a⁻¹ * a⁻¹

/-- In abelian groups, this is just identity -/
@[simp]
def commutatorWithSelf (x : G) : G := x * x * x⁻¹ * x⁻¹

end LeanDisco.Domains.GroupRing.Objects
