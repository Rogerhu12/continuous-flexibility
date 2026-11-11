import ContinuousFlexibility.Scalar.WeightedRadialMultiplier
import ContinuousFlexibility.Analysis.MaterialOrdinaryJets

/-!
# Lowering the weight exponent of actual physical jets

The ratio of the two material pullbacks is the positive radial multiplier
`H^(γ - γ')`.  For a nonnegative exponent, every fixed derivative of that
multiplier is globally bounded.  The radial multiplier estimate therefore
preserves the physical jet order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

theorem contDiff_materialH_rpow
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (δ : ℝ) :
    ContDiff ℝ ∞ (fun x => T.H (T.radius x) ^ δ) := by
  obtain ⟨hcont, hpos, _, _, _, _, hrad, hInv, _⟩ := hT
  have hH : ContDiff ℝ ∞ (fun x => T.H (T.radius x)) :=
    (hcont T.H (by simp)).comp_contDiff hrad (fun x => (hInv x).1)
  exact hH.rpow_const_of_ne (fun x => ((hpos _ (hInv x).1).2.1).ne')

theorem materialH_nonnegative_power_bounded
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, T.H (T.radius x) ^ δ ≤ C := by
  by_cases hz : δ = 0
  · exact ⟨1, zero_le_one, fun x => by simp only [hz, Real.rpow_zero]⟩
  · have hp : 0 < δ := lt_of_le_of_ne hδ hz.symm
    obtain ⟨_, _, _, _, _, _, _, hInv, _, _, _, _, hPower, _⟩ := hT
    obtain ⟨C, hC, hbound, _, _⟩ := hPower 0 δ hp
    refine ⟨C, hC.le, fun x => ?_⟩
    simpa only [Real.rpow_zero, mul_one] using hbound (T.radius x) (hInv x).1

/-- Every radial jet of a nonnegative material-height power is bounded on
the whole material cylinder, including both infinite ends. -/
theorem iteratedDeriv_materialH_nonnegative_power_bounded
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv n (fun t => T.H (T.radius t) ^ δ) x| ≤ C := by
  obtain ⟨B, hB, hBx⟩ := iteratedDeriv_materialH_rpow_bound hT δ n
  obtain ⟨K, hK, hKx⟩ := materialH_nonnegative_power_bounded hT hδ
  exact ⟨B * K, mul_nonneg hB hK, fun x =>
    (hBx x).trans (mul_le_mul_of_nonneg_left (hKx x) hB)⟩

/-- Exact relation between the two actual material pullbacks. -/
theorem materialPullback_weight_shift
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (γ γ' : ℝ) (f : PolarPoint → ℝ) :
    materialPullback T γ' f =
      fun p => T.H (T.radius p.1) ^ (γ - γ') * materialPullback T γ f p := by
  funext p
  obtain ⟨_, hpos, _, _, _, _, _, hInv, _⟩ := hT
  have hH : 0 < T.H (T.radius p.1) := (hpos _ (hInv p.1).1).2.1
  have he : (γ - γ') + (-γ) = -γ' := by ring
  simp only [materialPullback]
  rw [← mul_assoc, ← Real.rpow_add hH, he]

/-- Lowering the weight exponent preserves every weighted-jet order. -/
theorem weightedPhysicalJet_weight_shift_bound
    {D : ReferenceData} {T : MaterialData} {γ γ' : ℝ}
    (hT : IsMaterialData D T) (hγ : γ' ≤ γ) (a b c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      MemLp (weightedPhysicalJet T γ' a b c f) 2 materialCylinderMeasure ∧
      (eLpNorm (weightedPhysicalJet T γ' a b c f) 2 materialCylinderMeasure).toReal ≤
        C * physicalNorm T γ (a + b + c) f := by
  have hδ : 0 ≤ γ - γ' := sub_nonneg.mpr hγ
  have hbound : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv j (fun t => T.H (T.radius t) ^ (γ - γ')) x| ≤
        C * T.M (T.radius x) ^ (0 : ℕ) := by
    intro j
    simpa only [pow_zero, mul_one] using
      iteratedDeriv_materialH_nonnegative_power_bounded hT hδ j
  obtain ⟨C, hC, hCf⟩ := weightedRadialMultiplier_jet_bound hT
    (contDiff_materialH_rpow hT (γ - γ')) 0 hbound a b c
  refine ⟨C, hC, fun f hf => ?_⟩
  have heq : weightedPhysicalJet T γ' a b c f =
      fun p => T.M (T.radius p.1) ^ c * mixedDerivative a b
        (fun q => T.H (T.radius q.1) ^ (γ - γ') * materialPullback T γ f q) p := by
    simp only [weightedPhysicalJet, materialPullback_weight_shift hT γ γ' f]
  have h := hCf f hf
  rw [← heq] at h
  simpa only [Nat.add_zero] using h

theorem heightMember_weight_shift
    {D : ReferenceData} {T : MaterialData} {γ γ' : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hγ : γ' ≤ γ) (hf : HeightMember D T γ f) :
    HeightMember D T γ' f := by
  refine ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, ?_⟩
  intro a b c
  obtain ⟨_, _, hbound⟩ := weightedPhysicalJet_weight_shift_bound hT hγ a b c
  exact (hbound f hf).1

end ContinuousFlexibility.Statements
