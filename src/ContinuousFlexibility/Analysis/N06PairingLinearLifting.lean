import Mathlib.Analysis.Normed.Operator.Basic

/-!
# A bounded linear map determined by separating linear pairings

Existence and a norm estimate for each input suffice when the output
is determined by a separating family of linear pairings. This avoids
requiring intermediate choices of weak derivative representatives to
depend linearly on the input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

variable {E Y ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A chosen output is automatically linear because all its pairings
are prescribed by linear functions of the input. -/
theorem n06_exists_clm_of_separating_pairings
    (test : ι → Y →ₗ[ℝ] ℝ)
    (hinj : Function.Injective (fun y : Y => fun i => test i y))
    (rhs : ι → E →ₗ[ℝ] ℝ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hex : ∀ x : E, ∃ y : Y,
      (∀ i, test i y = rhs i x) ∧ ‖y‖ ≤ Q * ‖x‖) :
    ∃ M : E →L[ℝ] Y, ‖M‖ ≤ Q ∧
      (∀ x i, test i (M x) = rhs i x) ∧
      (∀ x y, (∀ i, test i y = rhs i x) → M x = y) := by
  choose W hWtest hWnorm using hex
  let W₀ : E →ₗ[ℝ] Y :=
    { toFun := W
      map_add' := by
        intro x y
        apply hinj
        funext i
        simp only [map_add, hWtest]
      map_smul' := by
        intro c x
        apply hinj
        funext i
        simp only [map_smul, hWtest, RingHom.id_apply] }
  let M : E →L[ℝ] Y := W₀.mkContinuous Q hWnorm
  refine ⟨M, W₀.mkContinuous_norm_le hQ hWnorm, hWtest, ?_⟩
  intro x y hy
  apply hinj
  funext i
  exact (hWtest x i).trans (hy i).symm

/-- The same constant is chosen before the smallness parameter and the
coefficient family. No output map has been assumed as an input. -/
theorem n06_exists_clm_family_of_separating_pairings
    {Z : Type*} (admissible : ℝ → Z → Prop)
    (test : ι → Y →ₗ[ℝ] ℝ)
    (hinj : Function.Injective (fun y : Y => fun i => test i y))
    (rhs : Z → ι → E →ₗ[ℝ] ℝ)
    (hex : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ δ : ℝ, 0 ≤ δ →
      ∀ z : Z, admissible δ z → ∀ x : E, ∃ y : Y,
        (∀ i, test i y = rhs z i x) ∧ ‖y‖ ≤ (Q * δ) * ‖x‖) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ δ : ℝ, 0 ≤ δ →
      ∀ z : Z, admissible δ z → ∃ M : E →L[ℝ] Y,
        ‖M‖ ≤ Q * δ ∧ (∀ x i, test i (M x) = rhs z i x) ∧
        (∀ x y, (∀ i, test i y = rhs z i x) → M x = y) := by
  obtain ⟨Q, hQ, hfamily⟩ := hex
  refine ⟨Q, hQ, ?_⟩
  intro δ hδ z hz
  exact n06_exists_clm_of_separating_pairings test hinj (rhs z)
    (mul_nonneg hQ hδ) (hfamily δ hδ z hz)

end ContinuousFlexibility.Analysis
