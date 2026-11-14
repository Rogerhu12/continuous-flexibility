module

public import ContinuousFlexibility.Analysis.N08RadialHeightForcing
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.IntermediateValue

/-!
# A positive physical-cell height direction detects the flow label

The return margin supplies a positive lower bound for the total optical
travel. Continuity of its primitive gives an interior radius containing
half that lower bound. A constant positive radial height slope then forces
a positive mixed flow variation at that radius. The upper bound remains
at N01's original label, while the return margin records its actual cell.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped Interval

theorem n08_exists_partialIntegral_half
    {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b) (hc : 0 < c)
    (hf : IntervalIntegrable f volume a b) (htotal : c ≤ ∫ s in a..b, f s) :
    ∃ r ∈ Ioo a b, (∫ s in a..r, f s) = c / 2 := by
  have hcont : ContinuousOn (fun r => ∫ s in a..r, f s) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      (intervalIntegral.continuousOn_primitive_interval' hf
        (left_mem_uIcc : a ∈ uIcc a b))
  have htarget : c / 2 ∈ Icc (∫ s in a..a, f s) (∫ s in a..b, f s) := by
    rw [intervalIntegral.integral_same]
    exact ⟨(half_pos hc).le, (half_le_self hc.le).trans htotal⟩
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc hab.le hcont htarget
  dsimp only at heq
  have hleft : a < r := by
    by_contra h
    have he : r = a := le_antisymm (le_of_not_gt h) hr.1
    rw [he, intervalIntegral.integral_same] at heq
    linarith only [hc, heq]
  have hright : r < b := by
    by_contra h
    have he : r = b := le_antisymm hr.2 (le_of_not_gt h)
    rw [he] at heq
    linarith only [hc, heq, htotal]
  exact ⟨r, ⟨hleft, hright⟩, heq⟩

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Interval

set_option backward.isDefEq.respectTransparency false

theorem n08_partialOpticalForcing_lower
    {w : ℝ → ℝ} {l h c a : ℝ}
    (hw : ContDiff ℝ ∞ w) (hl : 0 < l) (hlh : l < h)
    (hpos : ∀ s ∈ Icc l h, 0 < w s) (hc : 0 < c) (ha : 0 ≤ a)
    (htravel : c ≤ opticalTravel w l h) :
    ∃ r ∈ Ioo l h,
      a * c ≤ ∫ s in l..r, opticalSpeed w s * (1 + w s ^ 2) / w s * a := by
  have hwd : Continuous (deriv w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hv : ContinuousOn (opticalSpeed w) (Icc l h) :=
    (hwd.neg.continuousOn.div (continuous_id.mul hw.continuous).continuousOn
      (fun s hs => (mul_pos (hl.trans_le hs.1) (hpos s hs)).ne')).sqrt
  obtain ⟨r, hr, hhalf⟩ := n08_exists_partialIntegral_half hlh hc
    (hv.intervalIntegrable_of_Icc hlh.le) htravel
  have hsub : Icc l r ⊆ Icc l h := Icc_subset_Icc le_rfl hr.2.le
  have hvint : IntervalIntegrable (opticalSpeed w) volume l r :=
    (hv.mono hsub).intervalIntegrable_of_Icc hr.1.le
  have hforcing : ContinuousOn
      (fun s => opticalSpeed w s * (1 + w s ^ 2) / w s * a) (Icc l r) :=
    (((hv.mono hsub).mul
      (continuousOn_const.add (hw.continuous.continuousOn.pow 2))).div
        hw.continuous.continuousOn (fun s hs => (hpos s (hsub hs)).ne')).mul
          continuousOn_const
  refine ⟨r, hr, ?_⟩
  calc
    a * c = ∫ s in l..r, (2 * a) * opticalSpeed w s := by
      rw [intervalIntegral.integral_const_mul, hhalf]
      ring
    _ ≤ ∫ s in l..r, opticalSpeed w s * (1 + w s ^ 2) / w s * a := by
      apply intervalIntegral.integral_mono_on hr.1.le (hvint.const_mul (2 * a))
        (hforcing.intervalIntegrable_of_Icc hr.1.le)
      intro s hs
      have hfactor : (2 : ℝ) ≤ (1 + w s ^ 2) / w s := by
        apply (le_div_iff₀ (hpos s (hsub hs))).mpr
        nlinarith only [sq_nonneg (w s - 1)]
      have hvnonneg : 0 ≤ opticalSpeed w s := Real.sqrt_nonneg _
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactor hvnonneg) ha
      convert h using 1 <;> ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The physical cell and return margin are chosen before the height
direction. The original flow label is retained in the forcing upper bound. -/
theorem n08_radialHeight_positive_slope_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    ∃ parameterLoss : ℕ, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ m,
      ∃ j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
      ∃ c : ℝ, 0 < c ∧ c⁻¹ ≤ radialE (D.cellIndex j) ^ A ∧
      ∀ (η : HeightPair S) (h g : ℝ → ℝ) (a : ℝ), 0 ≤ a →
        (∀ s, HasDerivAt h (g s) s) →
        (∀ s ∈ Ioo (C.left m) (C.right m), g s = a) →
        (∀ s ∈ Ioo (C.left m) (C.right m), ∀ θ, heightPairField S η (s, θ) = h s) →
        a * c ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          (2 * heightPairGrading S base η + heightPairGrading S (loss + parameterLoss) η) := by
  obtain ⟨A, hA, hmargin⟩ := hN.1.2.2.1.2
  obtain ⟨parameterLoss, B, hB, hbound⟩ := n08_radialHeight_forcing_integral_bound hT hS hN
  refine ⟨parameterLoss, A, B, hA, hB, fun m => ?_⟩
  have hC := hN.2.2.2.1
  have hb := hC.1 m
  have hnegative : NegativeRadialComponent D (C.left m) (C.right m) :=
    ⟨hb.1, hb.2.1, hb.2.2, (hC.2.1 m).1, (hC.2.1 m).2.1,
      hC.2.2.2.1 m⟩
  obtain ⟨_, j, hj, c, hc, hcE, hsine⟩ := hmargin (C.left m) (C.right m) hnegative
  have hsineOne : c ≤ |Real.sin (radialTravel D (C.left m) (C.right m))| := by
    simpa only [Nat.cast_one, one_mul, div_one] using hsine 1 le_rfl
  have hnonneg : 0 ≤ radialTravel D (C.left m) (C.right m) :=
    intervalIntegral.integral_nonneg_of_forall hb.2.1.le (fun _ => Real.sqrt_nonneg _)
  have htravel : c ≤ opticalTravel D.w (C.left m) (C.right m) := by
    have h := hsineOne.trans Real.abs_sin_le_abs
    rwa [abs_of_nonneg hnonneg] at h
  have hg : RadialProfileGeometry D := hN.1.1.choose_spec.1
  refine ⟨j, hj, c, hc, hcE, fun η h g a ha hh hgconst hη => ?_⟩
  obtain ⟨r, hr, hlow⟩ := n08_partialOpticalForcing_lower hg.2.2.1.1
    (hg.1.trans hb.1) hb.2.1
    (fun s hs => hg.2.2.2.2.1 s ⟨hb.1.trans_le hs.1, hs.2.trans_lt hb.2.2⟩)
    hc ha htravel
  have heq : (∫ s in C.left m..r, opticalSpeed D.w s * (1 + D.w s ^ 2) / D.w s * a) =
      ∫ s in C.left m..r, opticalSpeed D.w s * (1 + D.w s ^ 2) / D.w s * g s := by
    apply intervalIntegral.integral_congr_Ioo_of_le hr.1.le
    intro s hs
    dsimp only
    rw [hgconst s ⟨hs.1, hs.2.trans hr.2⟩]
  exact (hlow.trans_eq heq).trans ((le_abs_self _).trans
    (hbound m η h g hh hη r hr))

end ContinuousFlexibility.Statements
