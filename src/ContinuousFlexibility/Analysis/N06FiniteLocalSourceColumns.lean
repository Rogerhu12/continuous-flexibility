module

public import ContinuousFlexibility.Analysis.N06FiniteSourceColumns
public import ContinuousFlexibility.Analysis.N06WeakAngularMultiplier

/-!
# Finite source columns smooth only on their actual open strips

A finite constant physical source is first constructed with the original
N05 smooth-jet API. The already established local weak angular multiplier
then inserts the actual coefficient fields. No smooth extension across a
canonical boundary is assumed. Vanishing on inactive pieces is required
only inside their canonical open strips.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The exact finite constant source in the selected weighted level. -/
theorem n06Volume_exists_finite_constant_source
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {K : CanonicalData S} {V : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ t : ℝ) (b : ℕ) (I : Finset ℕ) :
    ∃ B : V.level γ t b,
      (∀ m, (V.forget γ t b B m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun _ => if m ∈ I then (1 : ℝ) else 0) ∧
      ‖B‖ ≤ n06FiniteSourceCost T S K γ t b I := by
  classical
  let g : ℕ → PolarPoint → ℝ := fun m _ => if m ∈ I then 1 else 0
  have hg : ∀ m, ContDiff ℝ ∞ (g m) := fun _ => contDiff_const
  have hp : ∀ m, Function.Periodic (g m) (0, Real.pi) := fun _ _ => rfl
  have he : ∀ m p, g m (p.1, Real.pi - p.2) = g m p := fun _ _ => rfl
  have hz : ∀ m, m ∉ I → g m = 0 := by
    intro m hm
    funext p
    simp only [g, if_neg hm, Pi.zero_apply]
  have hbound : ∀ m ∈ I, ∀ j, j ≤ b → ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative 0 j (g m) p| ≤ (1 : ℝ) := by
    intro m hm j _hj p _hp
    by_cases hj : j = 0
    · simp only [g, if_pos hm, hj, mixedDerivative, iteratedDeriv_zero, abs_one, le_refl]
    · simp only [g, if_pos hm, mixedDerivative, iteratedDeriv_zero,
        iteratedDeriv_const, if_neg hj, ite_true, ite_self, abs_zero, zero_le_one]
  obtain ⟨B, hB, hnorm⟩ := n06Volume_exists_finite_smooth_source hD hT hV γ t b I
    g hg hp he hz zero_le_one hbound
  exact ⟨B, hB, by simpa only [mul_one] using hnorm⟩

/-- A finite family of genuine strip-smooth, periodic, even fields is an
actual source at any fixed angular order. Its norm is bounded by the
explicit finite material cost times the established weak product cost. -/
theorem n06Volume_exists_finite_local_source
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {K : CanonicalData S} {V : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ t : ℝ) (b : ℕ)
    (I : Finset ℕ) (f : ℕ → PolarPoint → ℝ)
    (hf : ∀ m, ContDiffOn ℝ ∞ (f m) (canonicalOpen S K m))
    (hp : ∀ m p, p ∈ canonicalOpen S K m → f m (p + (0, Real.pi)) = f m p)
    (he : ∀ m p, p ∈ canonicalOpen S K m → f m (p.1, Real.pi - p.2) = f m p)
    (hsupport : ∀ m, m ∉ I → ∀ p ∈ canonicalOpen S K m, f m p = 0)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ m ∈ I, ∀ j, j ≤ b → ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative 0 j (f m) p| ≤ δ) :
    ∃ F : V.level γ t b,
      (∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] f m) ∧
      ‖F‖ ≤ (n06WeakAngularMultiplierCost b * n06FiniteSourceCost T S K γ t b I) * δ := by
  classical
  obtain ⟨B, hB, hBnorm⟩ := n06Volume_exists_finite_constant_source hD hT hV γ t b I
  have hfull : ∀ m j, j ≤ b → ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative 0 j (f m) p| ≤ δ := by
    intro m j hj p hpU
    by_cases hm : m ∈ I
    · exact hbound m hm j hj p hpU
    · have hz : (fun θ : ℝ => f m (p.1, θ)) = (0 : ℝ → ℝ) := by
        funext θ
        exact hsupport m hm (p.1, θ) ⟨hpU.1, mem_univ θ⟩
      change |iteratedDeriv j (fun θ : ℝ => f m (p.1, θ)) p.2| ≤ δ
      rw [hz]
      simpa only [iteratedDeriv_const_zero, abs_zero] using hδ
  obtain ⟨F, _hjets, hF, hFnorm⟩ :=
    n06Volume_weakAngularMultiplier hV γ t b f hf hp he δ hδ hfull B
  refine ⟨F, ?_, hFnorm.trans ?_⟩
  · intro m
    filter_upwards [hF m, hB m,
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hFp hBp hstrip
    rw [hFp, hBp]
    by_cases hm : m ∈ I
    · simp only [if_pos hm, mul_one]
    · rw [if_neg hm, hsupport m hm p ⟨hstrip.1, mem_univ _⟩, mul_zero]
  · calc
      n06WeakAngularMultiplierCost b * δ * ‖B‖ ≤
          n06WeakAngularMultiplierCost b * δ * n06FiniteSourceCost T S K γ t b I :=
        mul_le_mul_of_nonneg_left hBnorm
          (mul_nonneg (n06WeakAngularMultiplierCost_nonneg b) hδ)
      _ = _ := by ring

end ContinuousFlexibility.Statements
