import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace AnisotropicCalderon

/-!
Smooth anisotropic Calderón uniqueness, specialized to `n = 3`, `M` the closed
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

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- The open unit ball `B`. -/
def ball : Set R3 := Metric.ball 0 1

/-- Partial derivative `∂ᵢu(x)` in Cartesian coordinates. -/
def partialDeriv (u : R3 → ℝ) (i : Fin 3) (x : R3) : ℝ :=
  fderiv ℝ u x (EuclideanSpace.single i 1)

/-- Jacobian matrix `(DΦ(x))_{ij} = ∂ⱼΦⁱ(x)`. -/
def jacobian (Φ : R3 → R3) (x : R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => fderiv ℝ Φ x (EuclideanSpace.single j 1) i

/-- `g` is a smooth Riemannian metric on `ℝ³` equal to the Euclidean metric
outside the open unit ball. -/
def IsAdmissibleMetric (g : R3 → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  (∀ i j, ContDiff ℝ ∞ fun x => g x i j) ∧
  (∀ x, (g x).PosDef) ∧
  ∀ x : R3, 1 ≤ ‖x‖ → g x = 1

/-- Dirichlet energy `∫_B |du|²_g dV_g = ∫_B g^{ij} ∂ᵢu ∂ⱼu √(det g) dx`. -/
def energy (g : R3 → Matrix (Fin 3) (Fin 3) ℝ) (u : R3 → ℝ) : ℝ :=
  ∫ x in ball, (∑ i, ∑ j, (g x)⁻¹ i j * partialDeriv u i x * partialDeriv u j x) *
    Real.sqrt (g x).det

/-- Smooth competitors with the same boundary values as `f` on `∂B`:
`u - f` is smooth and compactly supported in the open ball. -/
def competitors (f : R3 → ℝ) : Set (R3 → ℝ) :=
  { u | ContDiff ℝ ∞ u ∧ tsupport (u - f) ⊆ ball }

/-- Minimal Dirichlet energy with boundary value `f|_{∂B}`, i.e. `⟨Λ_g f, f⟩`. -/
def dirichletEnergy (g : R3 → Matrix (Fin 3) (Fin 3) ℝ) (f : R3 → ℝ) : ℝ :=
  sInf (energy g '' competitors f)

/-- Main theorem: equal Dirichlet-to-Neumann data on the whole boundary implies that
the metrics agree up to a diffeomorphism fixing the boundary. Because both metrics
agree with the Euclidean metric to infinite order at `∂B`, the diffeomorphism agrees
with the identity to infinite order at `∂B`, so it extends by the identity to a
diffeomorphism of `ℝ³`. -/
theorem main (g₁ g₂ : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → dirichletEnergy g₁ f = dirichletEnergy g₂ f) :
    ∃ Φ : R3 ≃ R3,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
      (∀ x : R3, 1 ≤ ‖x‖ → Φ x = x) ∧
      ∀ x : R3, g₂ x = (jacobian Φ x).transpose * g₁ (Φ x) * jacobian Φ x := by
  sorry

end AnisotropicCalderon
end

end OAI
