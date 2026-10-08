import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace AnisotropicCalderon

/-!
Smooth anisotropic Calderón uniqueness, specialized to `n = 3`, `M` the open
unit ball `B ⊆ ℝ³`, `Γ = ∂B`, and metrics that are Euclidean outside `B`.

A metric is a smooth matrix-valued function `g : ℝ³ → ℝ³ˣ³` in Cartesian
coordinates, equal to the identity on `ℝ³ ∖ B`. Its restriction to the closed
ball is a smooth metric on `M`.

The full-boundary Dirichlet-to-Neumann data is encoded by the minimal Dirichlet
energy `E_g(f) = inf { ∫_B g^{ij} ∂ᵢu ∂ⱼu √(det g) dx : u smooth, u - f ∈ C_c^∞(B) }`
of each smooth boundary value `f|_{∂B}`. This infimum equals
`⟨Λ_g f, f⟩ = ∫_B |d u_f^g|²_g dV_g`, and by polarization and density the
quadratic forms `E_{g₁} = E_{g₂}` determine `Λ_{g₁} = Λ_{g₂}`.
-/

/-- The Euclidean space `ℝ³`. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Fields of `3 × 3` matrices on `ℝ³`, such as metrics and Jacobians. -/
abbrev MatrixField := R3 → Matrix (Fin 3) (Fin 3) ℝ

/-- The open unit ball. -/
def B : Set R3 := Metric.ball 0 1

/-- Differential `du(x)` in Cartesian coordinates, `d u x i = ∂ᵢu(x)`. -/
def d (u : R3 → ℝ) (x : R3) : Fin 3 → ℝ :=
  fun i => fderiv ℝ u x (EuclideanSpace.single i 1)

/-- Jacobian matrix, `D Φ x i j = ∂ⱼΦⁱ(x)`. -/
def D (Φ : R3 → R3) : MatrixField :=
  fun x => Matrix.of fun i j => fderiv ℝ Φ x (EuclideanSpace.single j 1) i

/-- Riemannian volume density `V = √(det g)`. -/
def vol (g : MatrixField) (x : R3) : ℝ :=
  Real.sqrt (g x).det

/-- Dirichlet energy `∫_B |du|²_g dV = ∫_B g^{ij} ∂ᵢu ∂ⱼu dV`. -/
def energy (g : MatrixField) (u : R3 → ℝ) : ℝ :=
  ∫ x in B, (∑ i, ∑ j, (g x)⁻¹ i j * d u x i * d u x j) * vol g x

/-- Minimal Dirichlet energy with boundary value `f|_{∂B}`, i.e. `⟨Λ_g f, f⟩`. -/
def minimalEnergy (g : MatrixField) (f : R3 → ℝ) : ℝ :=
  sInf (energy g '' { u | ContDiff ℝ ∞ u ∧ tsupport (u - f) ⊆ B })

/-- `g` is a smooth Riemannian metric on `ℝ³` equal to the Euclidean metric
outside the open unit ball. -/
structure IsAdmissibleMetric (g : MatrixField) : Prop where
  smooth : ∀ i j, ContDiff ℝ ∞ fun x => g x i j
  posDef : ∀ x, (g x).PosDef
  euclidean_exterior : ∀ x : R3, 1 ≤ ‖x‖ → g x = 1

/-- `Φ` is a diffeomorphism of `ℝ³` that is the identity outside the open unit ball
and pulls `g₁` back to `g₂`, i.e. `g₂ = Φ^* g₁`. -/
structure IsIsometryFixingExterior (Φ : R3 ≃ R3) (g₁ g₂ : MatrixField) : Prop where
  smooth : ContDiff ℝ ∞ Φ
  smooth_inv : ContDiff ℝ ∞ Φ.symm
  fixes_exterior : ∀ x : R3, 1 ≤ ‖x‖ → Φ x = x
  isometry : ∀ x : R3, g₂ x = (D Φ x).transpose * g₁ (Φ x) * D Φ x

/-- Main theorem: equal Dirichlet-to-Neumann data on the whole boundary implies that
the metrics agree up to a diffeomorphism fixing the boundary. Because both metrics
agree with the Euclidean metric to infinite order at `∂B`, the diffeomorphism agrees
with the identity to infinite order at `∂B`, so it extends by the identity to a
diffeomorphism of `ℝ³`. -/
theorem main (g₁ g₂ : MatrixField)
    (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f) :
    ∃ Φ : R3 ≃ R3, IsIsometryFixingExterior Φ g₁ g₂ := by
  sorry

end AnisotropicCalderon
end

end OAI
