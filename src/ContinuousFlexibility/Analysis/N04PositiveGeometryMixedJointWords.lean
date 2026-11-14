module

public import ContinuousFlexibility.Analysis.N04PulledFieldsJointExpansion
public import ContinuousFlexibility.Analysis.N04PulledFieldsInverseSlotBounds
public import ContinuousFlexibility.Analysis.N04RealizationFixedSpatialProduct

/-!
# Actual mixed bounds on the original pure joint words

The exact double expansion keeps the parameter count unchanged. No
uniform seminorm premise is needed because the supplied joint tower
already belongs to the same actual function. A fixed spatial multiplier
also keeps every parameter derivative on the current factor.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {Ω : Set PolarPoint} {f : E → PolarPoint → ℝ}

theorem n04PositiveGeometry_joint_word_bound_of_mixed
    (J : SmoothDirections (U ×ˢ Ω) (fun z : E × PolarPoint => f z.1 z.2))
    (RF : MixedJetRegularity U Ω f)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hc : Convex ℝ (U ×ˢ Ω))
    (P : E → Prop) {n : ℕ} (w : StateAngleWord n)
    {x : E} (hx : x ∈ U) {q : PolarPoint} (hq : q ∈ Ω)
    {M : ℝ} (hM : 0 ≤ M)
    (hraw : ∀ a b : ℕ, a + b = w.angleArity →
      ∀ u : Fin w.stateArity → E, (∀ i, P (u i)) →
        ‖(RF.parameter a b q hq).D w.stateArity x u‖ ≤ M)
    (v : Fin n → E × PolarPoint)
    (hpure : ∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0)
    (hbox : ∀ i, P (v i).1 ∧ ‖(v i).2‖ ≤ 1) :
    ‖J.D n (x, q) v‖ ≤ M * (2 : ℝ) ^ w.angleArity := by
  rw [Real.norm_eq_abs,
    n04PulledFields_jointDirections_mixedExpansion J RF hU hΩ hc n x hx q hq]
  apply n04PulledFields_doubleExpansion_pureSlots_bound P w
    (fun a b k => ((RF.parameter a b q hq).D k x).toMultilinearMap) hM
    (fun a b hab u hu => by
      change |(RF.parameter a b q hq).D w.stateArity x u| ≤ M
      rw [← Real.norm_eq_abs]
      exact hraw a b hab u hu)
    (fun i => (((v i).1, (v i).2.1), (v i).2.2))
    (fun i => (hbox i).1)
    (fun i => (show |(v i).2.1| ≤ ‖(v i).2‖ by
      simpa only [Real.norm_eq_abs] using norm_fst_le (v i).2).trans (hbox i).2)
    (fun i => (show |(v i).2.2| ≤ ‖(v i).2‖ by
      simpa only [Real.norm_eq_abs] using norm_snd_le (v i).2).trans (hbox i).2)
    (fun i hi => by simpa only [hi, Bool.false_eq_true, if_false] using hpure i)
    (fun i hi => by simpa only [hi, if_true, Prod.eta] using hpure i)

/-- The scalar power is the exact spatial order plus the unchanged
parameter shift. The fixed multiplier consumes no parameter height. -/
theorem n04PositiveGeometry_fixedSpatialProduct_power_bound
    {h : PolarPoint → ℝ} (hΩ : IsOpen Ω) (hh : ContDiffOn ℝ ∞ h Ω)
    (RF : MixedJetRegularity U Ω f)
    (a b k shift : ℕ) {q : PolarPoint} (hq : q ∈ Ω)
    (J : SmoothDirections U (fun x => mixedDerivative a b (fun p => h p * f x p) q))
    {x : E} (hx : x ∈ U) (v : Fin k → E)
    {A M H t : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 1 ≤ t)
    (hfixed : ∀ u w : ℕ, u + w ≤ a + b → |mixedDerivative u w h q| ≤ A)
    (hraw : ∀ u w : ℕ, u + w ≤ a + b →
      ‖(RF.parameter u w q hq).D k x v‖ ≤
        M * parameterHeightWeight H k * t ^ (u + w + shift * k)) :
    ‖J.D k x v‖ ≤ (2 : ℝ) ^ (a + b) * A * M * parameterHeightWeight H k *
      t ^ (a + b + shift * k) := by
  let R : ℝ := t ^ (a + b + 1)
  let M' := M * parameterHeightWeight H k * t ^ (shift * k)
  have hM' : 0 ≤ M' := mul_nonneg (mul_nonneg hM (parameterHeightWeight_nonneg hH _))
    (pow_nonneg (zero_le_one.trans ht) _)
  have hR : 1 ≤ R := one_le_pow₀ ht
  have hpower (j : ℕ) : R ^ ((j : ℝ) / (((a + b : ℕ) : ℝ) + 1)) = t ^ j := by
    dsimp only [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans ht), ← Real.rpow_natCast]
    congr 1
    push_cast
    field_simp [show (a : ℝ) + (b : ℝ) + 1 ≠ 0 by positivity]
  have hb := n04Realization_fixedSpatialProduct_parameterJet_bound hΩ hh RF
    a b (a + b) k le_rfl hq J hx v hA hM' hR hfixed (fun u w huw => by
      rw [hpower]
      have he : M * parameterHeightWeight H k * t ^ (u + w + shift * k) =
          M' * t ^ (u + w) := by
        dsimp only [M']
        rw [pow_add]
        ring
      simpa only [Real.norm_eq_abs, he] using hraw u w huw)
  rw [hpower] at hb
  rw [Real.norm_eq_abs]
  exact hb.trans_eq (by
    dsimp only [M']
    rw [pow_add]
    ring)

end ContinuousFlexibility.Analysis
