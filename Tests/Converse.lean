import ComparatorChallenges.AnisotropicCalderon

/-!
The easy converse of `OAI.AnisotropicCalderon.main`: metrics related by a diffeomorphism
that is the identity outside the unit ball have the same minimal Dirichlet energies.
This checks that the hypothesis and conclusion of the challenge fit together.
-/

namespace OAI.AnisotropicCalderon.Tests

noncomputable section
open MeasureTheory Matrix
open scoped ContDiff

/-- The standard basis of `ℝ³`. -/
abbrev e : Module.Basis (Fin 3) ℝ R3 := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

lemma D_eq_toMatrix (Φ : R3 → R3) (x : R3) :
    D Φ x = LinearMap.toMatrix e e (fderiv ℝ Φ x : R3 →ₗ[ℝ] R3) := by
  ext i j
  simp [D, LinearMap.toMatrix_apply]

lemma det_D (Φ : R3 → R3) (x : R3) : (D Φ x).det = (fderiv ℝ Φ x).det := by
  rw [D_eq_toMatrix, LinearMap.det_toMatrix]

lemma D_comp {Φ ψ : R3 → R3} {x : R3} (hψ : DifferentiableAt ℝ ψ (Φ x))
    (hΦ : DifferentiableAt ℝ Φ x) : D (ψ ∘ Φ) x = D ψ (Φ x) * D Φ x := by
  rw [D_eq_toMatrix, D_eq_toMatrix, D_eq_toMatrix, fderiv_comp x hψ hΦ, ← LinearMap.toMatrix_comp]
  rfl

lemma D_id (x : R3) : D id x = 1 := by
  rw [D_eq_toMatrix, fderiv_id]
  exact LinearMap.toMatrix_id e

lemma d_comp {u : R3 → ℝ} {Φ : R3 → R3} {x : R3} (hu : DifferentiableAt ℝ u (Φ x))
    (hΦ : DifferentiableAt ℝ Φ x) : d (u ∘ Φ) x = vecMul (d u (Φ x)) (D Φ x) := by
  funext i
  have h := e.sum_repr (fderiv ℝ Φ x (EuclideanSpace.single i 1))
  rw [d, fderiv_comp x hu hΦ, ContinuousLinearMap.comp_apply, ← h, map_sum]
  simp [vecMul, dotProduct, d, D, mul_comm]

lemma quadForm_eq_dotProduct (A : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 3 → ℝ) :
    ∑ i, ∑ j, A i j * w i * w j = w ⬝ᵥ (A *ᵥ w) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma quadForm_pullback (G J : Matrix (Fin 3) (Fin 3) ℝ) (hJ : IsUnit J.det) (v : Fin 3 → ℝ) :
    ∑ i, ∑ j, (Jᵀ * G * J)⁻¹ i j * (v ᵥ* J) i * (v ᵥ* J) j =
      ∑ i, ∑ j, G⁻¹ i j * v i * v j := by
  have hJt : IsUnit Jᵀ.det := by rwa [det_transpose]
  rw [quadForm_eq_dotProduct, quadForm_eq_dotProduct, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    ← mulVec_transpose, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
    nonsing_inv_mul _ hJt, Matrix.mul_one, mulVec_transpose, dotProduct_mulVec, vecMul_vecMul,
    ← Matrix.mul_assoc, mul_nonsing_inv _ hJ, Matrix.one_mul, ← dotProduct_mulVec]

section

variable {g₁ g₂ : MatrixField} {Φ : R3 ≃ R3} (hΦ : IsIsometryFixingExterior Φ g₁ g₂)
include hΦ

lemma differentiableAt (x : R3) : DifferentiableAt ℝ Φ x :=
  hΦ.smooth.differentiable (by simp) x

lemma isUnit_det_D (x : R3) : IsUnit (D Φ x).det := by
  have hsymm : DifferentiableAt ℝ Φ.symm (Φ x) := hΦ.smooth_inv.differentiable (by simp) _
  have h : D Φ.symm (Φ x) * D Φ x = 1 := by
    rw [← D_comp hsymm (differentiableAt hΦ x)]
    have : (Φ.symm ∘ Φ : R3 → R3) = id := funext Φ.symm_apply_apply
    rw [this, D_id]
  exact isUnit_det_of_left_inverse h

lemma vol_eq (x : R3) : vol g₂ x = |(D Φ x).det| * vol g₁ (Φ x) := by
  rw [vol, vol, hΦ.isometry x, det_mul, det_mul, det_transpose,
    show (D Φ x).det * (g₁ (Φ x)).det * (D Φ x).det = (D Φ x).det ^ 2 * (g₁ (Φ x)).det by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

lemma mem_B_iff (x : R3) : Φ x ∈ B ↔ x ∈ B := by
  have hext : ∀ y : R3, y ∉ B → Φ y = y := fun y hy =>
    hΦ.fixes_exterior y (by simpa [B] using hy)
  constructor
  · intro hx
    by_contra hx'
    exact (hx' ((hext x hx') ▸ hx)).elim
  · intro hx
    by_contra hx'
    have : Φ (Φ x) = Φ x := hext _ hx'
    exact hx' (by rw [Φ.injective this]; exact hx)

lemma image_B : Φ '' B = B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_B_iff hΦ x).2 hx
  · intro hy
    exact ⟨Φ.symm y, (mem_B_iff hΦ _).1 (by simpa using hy), by simp⟩

/-- The energy is invariant under pullback by `Φ`. -/
lemma energy_comp {u : R3 → ℝ} (hu : Differentiable ℝ u) :
    energy g₂ (u ∘ Φ) = energy g₁ u := by
  let F : R3 → ℝ := fun y =>
    (∑ i, ∑ j, (g₁ y)⁻¹ i j * d u y i * d u y j) * vol g₁ y
  have hpt : ∀ x, (∑ i, ∑ j, (g₂ x)⁻¹ i j * d (u ∘ Φ) x i * d (u ∘ Φ) x j) * vol g₂ x =
      |(fderiv ℝ Φ x).det| • F (Φ x) := by
    intro x
    rw [d_comp (hu _) (differentiableAt hΦ x), hΦ.isometry x,
      quadForm_pullback _ _ (isUnit_det_D hΦ x), vol_eq hΦ x, det_D, smul_eq_mul]
    ring
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_ball : MeasurableSet B)
    (fun x _ => (differentiableAt hΦ x).hasFDerivAt.hasFDerivWithinAt)
    Φ.injective.injOn F
  have himage := image_B hΦ
  simp only [B] at himage
  rw [himage] at hcov
  simp only [energy, hpt]
  exact hcov.symm

end

/-- Converse of `OAI.AnisotropicCalderon.main`: if `g₂ = Φ^* g₁` for a diffeomorphism `Φ`
that is the identity outside the unit ball, then the minimal Dirichlet energies agree. -/
theorem converse (g₁ g₂ : MatrixField) (Φ : R3 ≃ R3) (hΦ : IsIsometryFixingExterior Φ g₁ g₂)
    (f : R3 → ℝ) : minimalEnergy g₁ f = minimalEnergy g₂ f := by
  have hfix : ∀ x : R3, 1 ≤ ‖x‖ → Φ.symm x = x := fun x hx => by
    rw [Equiv.symm_apply_eq, hΦ.fixes_exterior x hx]
  unfold minimalEnergy
  congr 1
  ext E
  constructor
  · rintro ⟨u, ⟨hu, hbd⟩, rfl⟩
    refine ⟨u ∘ Φ, ⟨hu.comp hΦ.smooth, fun x hx => ?_⟩, energy_comp hΦ (hu.differentiable (by simp))⟩
    simp [hΦ.fixes_exterior x hx, hbd x hx]
  · rintro ⟨v, ⟨hv, hbd⟩, rfl⟩
    refine ⟨v ∘ Φ.symm, ⟨hv.comp hΦ.smooth_inv, fun x hx => ?_⟩, ?_⟩
    · simp [hfix x hx, hbd x hx]
    · rw [← energy_comp hΦ ((hv.differentiable (by simp)).comp
        (hΦ.smooth_inv.differentiable (by simp)))]
      congr 1
      funext x
      simp

end

end OAI.AnisotropicCalderon.Tests
