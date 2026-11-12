import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Analysis.RootOpticalEndpointLower
import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# Root-factor lower bounds from the future named primitive certificate

This held adapter targets the exact `N01PrimitiveGeometry` definition in
upstream commit 87f4c59eac24f172212f7cda075e76d0dfb871bf. That certificate is
not a conjunct of the current `N01Properties`. It must be retained on the
same reference, material data and controls by a future construction.

The inward simple-zero factor is the actual factor of `-w'`. The existing
one-sided optical limit supplies its lower bound without choosing another
profile, host cell, sample, or root factor.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis
open scoped ContDiff

theorem N01PrimitiveGeometry.rootSpeedFactor_material_lower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hG : N01PrimitiveGeometry D T S C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ) (rightEnd : Bool) (g : ℝ → ℝ),
      ContDiff ℝ ∞ g →
      (∀ t, -deriv D.w
        ((if rightEnd then C.right m else C.left m) +
          (if rightEnd then -1 else 1) * t) = t * g t) →
      let r := if rightEnd then C.right m else C.left m
      let σ : ℝ := if rightEnd then -1 else 1
      0 < referenceRootSpeedFactor D.w g r σ 0 ∧
        K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) ≤
          referenceRootSpeedFactor D.w g r σ 0 ^ 2 ∧
        (referenceRootSpeedFactor D.w g r σ 0 / 4)⁻¹ ≤
          4 * (1 + K * T.E0 (T.sample (C.cell m)) ^ K) := by
  obtain ⟨_, _, K, hK, hoptical⟩ := hG
  have hD : RadialProfileGeometry D := hA.1.1.choose_spec.1
  refine ⟨K, hK, ?_⟩
  intro m rightEnd g hg hfactor
  dsimp only
  have hcomponent := hA.2.2.1.1 m
  have hleft : 0 < C.left m := hD.1.trans hcomponent.1
  have hpositive : ∀ r ∈ Icc (C.left m) (C.right m), 0 < D.w r := by
    intro r hr
    exact hD.2.2.2.2.1 r
      ⟨hcomponent.1.trans_le hr.1, hr.2.trans_lt hcomponent.2.2⟩
  have hE : 0 < T.E0 (T.sample (C.cell m)) :=
    (hT.2.1 _ (materialSample_mem_interval hA.1.1 hT (C.cell m))).2.2.1
  let κ : ℝ := K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K)
  have hκ : 0 < κ := mul_pos (inv_pos.mpr hK) (Real.rpow_pos_of_pos hE _)
  have hκinv : κ⁻¹ = K * T.E0 (T.sample (C.cell m)) ^ K := by
    dsimp only [κ]
    rw [Real.rpow_neg hE.le K, mul_inv_rev, inv_inv, inv_inv]
    ring
  obtain ⟨hpos, hlower, hinverse⟩ :=
    referenceRootSpeedFactor_lower_of_component_optical
      hD.2.2.1.1 hg hleft hcomponent.2.1 hκ hpositive rightEnd hfactor
      (hoptical m)
  exact ⟨hpos, hlower, by simpa only [hκinv] using hinverse⟩

end ContinuousFlexibility.Blueprint
