module

public import ContinuousFlexibility.Analysis.MaterialComponentEnergy
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Actual L2 energy under a finite weighted overlap

The count of sets containing a point stays inside the integral. Thus a
coefficient-weight bound for the overlap gives a genuine bound for the
infinite sum of restricted energies, with one additional material order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

set_option backward.isDefEq.respectTransparency false

theorem eLpNorm_two_sq_eq_lintegral_of_aestronglyMeasurable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] using
    (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hf)

theorem tsum_indicator_eq_overlap_count
    {α : Type*} (A : ℕ → Set α) (g : α → ℝ≥0∞) (x : α)
    (hfinite : {m : ℕ | x ∈ A m}.Finite) :
    (∑' m : ℕ, (A m).indicator g x) =
      ENNReal.ofReal ({m : ℕ | x ∈ A m}.ncard : ℝ) * g x := by
  classical
  let B : Set ℕ := {m | x ∈ A m}
  have hB : B.Finite := hfinite
  have heq : (∑' m : ℕ, (A m).indicator g x) =
      ∑ m ∈ hB.toFinset, (A m).indicator g x := by
    apply tsum_eq_sum
    intro m hm
    apply Set.indicator_of_notMem
    intro hx
    exact hm (hB.mem_toFinset.mpr hx)
  rw [heq]
  calc
    _ = ∑ _m ∈ hB.toFinset, g x := by
      apply Finset.sum_congr rfl
      intro m hm
      have hx : x ∈ A m := hB.mem_toFinset.mp hm
      exact Set.indicator_of_mem hx g
    _ = (hB.toFinset.card : ℝ≥0∞) * g x := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by
      rw [Set.ncard_eq_toFinset_card B hB, ENNReal.ofReal_natCast]

theorem restricted_L2_energy_tsum_eq_lintegral_overlap
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A : ℕ → Set α} {f : α → ℝ}
    (hA : ∀ m, MeasurableSet (A m))
    (hfinite : ∀ x, {m : ℕ | x ∈ A m}.Finite)
    (hf : AEStronglyMeasurable f μ) :
    (∑' m : ℕ, eLpNorm f 2 (μ.restrict (A m)) ^ 2) =
      ∫⁻ x, ENNReal.ofReal ({m : ℕ | x ∈ A m}.ncard : ℝ) * ‖f x‖ₑ ^ 2 ∂μ := by
  have hm (m : ℕ) : AEMeasurable ((A m).indicator (fun x => ‖f x‖ₑ ^ 2)) μ :=
    (hf.enorm.pow_const (2 : ℕ)).indicator (hA m)
  simp_rw [eLpNorm_two_sq_eq_lintegral_of_aestronglyMeasurable hf.restrict,
    ← lintegral_indicator (hA _)]
  rw [← lintegral_tsum hm]
  apply lintegral_congr
  intro x
  exact tsum_indicator_eq_overlap_count A (fun x => ‖f x‖ₑ ^ 2) x (hfinite x)

theorem restricted_L2_energy_tsum_le_of_overlap_majorant
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A : ℕ → Set α} {f g : α → ℝ} {K : ℝ}
    (hA : ∀ m, MeasurableSet (A m))
    (hfinite : ∀ x, {m : ℕ | x ∈ A m}.Finite)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hbound : ∀ x,
      ENNReal.ofReal ({m : ℕ | x ∈ A m}.ncard : ℝ) * ‖f x‖ₑ ^ 2 ≤
        ENNReal.ofReal K * ‖g x‖ₑ ^ 2) :
    (∑' m : ℕ, eLpNorm f 2 (μ.restrict (A m)) ^ 2) ≤
      ENNReal.ofReal K * eLpNorm g 2 μ ^ 2 := by
  rw [restricted_L2_energy_tsum_eq_lintegral_overlap hA hfinite hf,
    eLpNorm_two_sq_eq_lintegral_of_aestronglyMeasurable hg]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal K * ‖g x‖ₑ ^ 2 ∂μ := lintegral_mono hbound
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem weightedPhysicalJet_succ_material_order
    (T : MaterialData) (γ : ℝ) (a b c : ℕ) (f : PolarPoint → ℝ) (p : PolarPoint) :
    weightedPhysicalJet T γ a b (c + 1) f p =
      T.M (T.radius p.1) * weightedPhysicalJet T γ a b c f p := by
  simp only [weightedPhysicalJet, pow_succ]
  ring

/-- A real overlap bound by the square of the material weight is
absorbed by the next actual physical material jet. -/
theorem weightedPhysicalJet_restricted_energy_tsum_le
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    {A : ℕ → Set PolarPoint} {K : ℝ}
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f) (hK : 0 ≤ K)
    (hA : ∀ m, MeasurableSet (A m))
    (hfinite : ∀ p, {m : ℕ | p ∈ A m}.Finite)
    (hcount : ∀ p, ({m : ℕ | p ∈ A m}.ncard : ℝ) ≤ K * T.M (T.radius p.1) ^ 2)
    (a b c : ℕ) :
    (∑' m : ℕ, eLpNorm (weightedPhysicalJet T γ a b c f)
      2 (materialCylinderMeasure.restrict (A m)) ^ 2) ≤
      ENNReal.ofReal K *
        eLpNorm (weightedPhysicalJet T γ a b (c + 1) f) 2 materialCylinderMeasure ^ 2 := by
  apply restricted_L2_energy_tsum_le_of_overlap_majorant hA hfinite
    (hf.2.2.2.2 a b c).aestronglyMeasurable
    (hf.2.2.2.2 a b (c + 1)).aestronglyMeasurable
  intro p
  have hM : 0 ≤ T.M (T.radius p.1) :=
    zero_le_one.trans (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.2.2
  have hnorm : ‖weightedPhysicalJet T γ a b (c + 1) f p‖ₑ ^ 2 =
      ENNReal.ofReal (T.M (T.radius p.1) ^ 2) *
        ‖weightedPhysicalJet T γ a b c f p‖ₑ ^ 2 := by
    rw [weightedPhysicalJet_succ_material_order, enorm_mul, mul_pow,
      Real.enorm_eq_ofReal_abs, abs_of_nonneg hM, ← ENNReal.ofReal_pow hM]
  calc
    _ ≤ ENNReal.ofReal (K * T.M (T.radius p.1) ^ 2) *
        ‖weightedPhysicalJet T γ a b c f p‖ₑ ^ 2 :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal (hcount p)) _
    _ = _ := by rw [ENNReal.ofReal_mul hK, hnorm, mul_assoc]

end ContinuousFlexibility.Statements
