import ContinuousFlexibility.Analysis.StateControlDecay
import ContinuousFlexibility.Analysis.StateKappaBounds
import ContinuousFlexibility.Blueprint.Statements
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A linear endpoint factor in the actual control derivative

Smooth controls supported in an open component have zero jets at both
endpoints. The mean value inequality applied to their first derivative
therefore gains the distance to the nearer endpoint from a second-jet
bound. This is the endpoint factor needed when comparing the control
perturbation to the reference optical Morse lower bound.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Blueprint
open scoped ContDiff

/-- One general estimate handles both ends of the support interval. -/
theorem supported_deriv_le_endpointDistance
    {f : ℝ → ℝ} {l h B : ℝ} (hlh : l ≤ h)
    (hf : ContDiff ℝ ∞ f) (hs : Function.support f ⊆ Ioo l h)
    (hB : 0 ≤ B) (hbound : ∀ r ∈ Ioo l h, |iteratedDeriv 2 f r| ≤ B)
    {r : ℝ} (hr : r ∈ Icc l h) :
    |deriv f r| ≤ B * min (r - l) (h - r) := by
  have hd : Differentiable ℝ (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by simp)
  have hleft : deriv f l = 0 := by
    simpa only [iteratedDeriv_one] using
      iteratedDeriv_zero_off_open_interval hf hs 1 (fun q => lt_irrefl l q.1)
  have hright : deriv f h = 0 := by
    simpa only [iteratedDeriv_one] using
      iteratedDeriv_zero_off_open_interval hf hs 1 (fun q => lt_irrefl h q.2)
  have hb (t : ℝ) (ht : t ∈ Icc l h) : ‖deriv (deriv f) t‖ ≤ B := by
    by_cases hi : t ∈ Ioo l h
    · simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero, Real.norm_eq_abs] using hbound t hi
    · have hz := iteratedDeriv_zero_off_open_interval hf hs 2 hi
      have hz' : deriv (deriv f) t = 0 := by
        simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hz
      rw [hz', norm_zero]
      exact hB
  have hL := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t ∈ Icc l h) => hd t) hb (convex_Icc l h)
    (show l ∈ Icc l h from ⟨le_rfl, hlh⟩) hr
  have hR := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t ∈ Icc l h) => hd t) hb (convex_Icc l h)
    (show h ∈ Icc l h from ⟨hlh, le_rfl⟩) hr
  have hL' : |deriv f r| ≤ B * (r - l) := by
    simpa only [hleft, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hr.1)] using hL
  have hR' : |deriv f r| ≤ B * (h - r) := by
    simpa only [hright, sub_zero, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr hr.2)] using hR
  by_cases hnear : r - l ≤ h - r
  · rw [min_eq_left hnear]
    exact hL'
  · rw [min_eq_right (le_of_not_ge hnear)]
    exact hR'

/-- N01a's actual second control-jet bound supplies this endpoint gain
uniformly for every component, using its designated sample weight. -/
theorem n01_controlFirstJet_le_endpointDistance
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hA : N01PartA D T S C) :
    ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ Ioo (C.left m) (C.right m) →
      |deriv (C.control m) r| ≤
        (B * T.E0 (T.sample (C.cell m)) ^ B) *
          min (r - C.left m) (C.right m - r) := by
  obtain ⟨B, hB, hbound⟩ := hA.2.2.2.2 2
  obtain ⟨_, hprofile⟩ := hA.1.1
  have hC : controlGeometryConditions D S C := hA.2.2.1
  refine ⟨B, hB, fun m r hr => ?_⟩
  have hsample : T.sample (C.cell m) ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hprofile.2.1 (C.cell m)
  have hweight : 0 ≤ B * T.E0 (T.sample (C.cell m)) ^ B :=
    mul_nonneg hB.le (Real.rpow_nonneg (hT.2.1 _ hsample).2.2.1.le B)
  obtain ⟨_, _, _, _, _, hcontrol, _⟩ := hC
  exact supported_deriv_le_endpointDistance (hA.2.2.1.1 m).2.1.le
    (hcontrol m).1 (hcontrol m).2.2 hweight
    (hbound m) ⟨hr.1.le, hr.2.le⟩

end ContinuousFlexibility.Statements
