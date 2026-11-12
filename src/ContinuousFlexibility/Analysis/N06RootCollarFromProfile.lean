import ContinuousFlexibility.Analysis.N06ReferenceRootDivision

/-!
# A quantitative two-sided collar from the actual profile

The orientation is chosen from the actual second derivative at the root.
Ordinary profile jets control the genuine smooth division, so the selected
radius gives both a positive factor and a positive profile on the whole
collar.  The negative coordinate side is therefore a true positive-type
region, with a linear lower bound for the original derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

/-- The radius is paid for by actual root curvature and actual profile
height.  No bound on a new root coordinate is assumed. -/
theorem n06_root_division_collar_of_profile_bounds
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) {r M δ : ℝ}
    (hroot : deriv w r = 0) (hM : 1 ≤ M) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcurv : 2 * M * δ ≤ |deriv (deriv w) r|)
    (hheight : 2 * M * δ ≤ w r)
    (hjets : ∀ k : ℕ, k ≤ 4 → ∀ y ∈ Icc (r - 1) (r + 1),
      |iteratedDeriv k w y| ≤ M) :
    ∃ ι : ℝ, ∃ g : ℝ → ℝ,
      (ι = 1 ∨ ι = -1) ∧ ContDiff ℝ ∞ g ∧
      g 0 = |deriv (deriv w) r| ∧
      (∀ t : ℝ, -deriv w (r + ι * t) = t * g t) ∧
      (∀ t ∈ Icc (-δ) δ,
        δ ≤ g t ∧ δ ≤ w (r + ι * t) ∧ N06ScalarJetTwoBound g t M ∧
          ∀ k : ℕ, k ≤ 4 → |iteratedDeriv k w (r + ι * t)| ≤ M) ∧
      ∀ t ∈ Ico (-δ) 0,
        0 < deriv w (r + ι * t) ∧ δ * (-t) ≤ deriv w (r + ι * t) := by
  obtain ⟨ι, hι, hsign⟩ : ∃ ι : ℝ,
      (ι = 1 ∨ ι = -1) ∧ -ι * deriv (deriv w) r = |deriv (deriv w) r| := by
    by_cases hd : deriv (deriv w) r ≤ 0
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [abs_of_nonpos hd]
      ring
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [abs_of_pos (lt_of_not_ge hd)]
      ring
  obtain ⟨g, hg, hg0, hfactor, hgbound⟩ := n06_exists_reference_root_division hw r ι hι hroot
  have hgabs : g 0 = |deriv (deriv w) r| := hg0.trans hsign
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hιabs : |ι| = 1 := by rcases hι with he | he <;> rw [he] <;> norm_num
  have hlocal (t : ℝ) (ht : t ∈ Icc (-δ) δ) :
      δ ≤ g t ∧ δ ≤ w (r + ι * t) ∧ N06ScalarJetTwoBound g t M ∧
        ∀ k : ℕ, k ≤ 4 → |iteratedDeriv k w (r + ι * t)| ≤ M := by
    have ht1 : t ∈ Icc (-1 : ℝ) 1 :=
      ⟨(neg_le_neg hδ1).trans ht.1, ht.2.trans hδ1⟩
    have hta : |t| ≤ δ := abs_le.mpr ht
    obtain ⟨hgjet, hgdiff, hwdiff⟩ := hgbound M hM hjets t ht1
    have hvariation : M * |t| ≤ M * δ := mul_le_mul_of_nonneg_left hta hMp.le
    have hMδ : δ ≤ M * δ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hM hδ.le
    have hδg : 2 * M * δ ≤ g 0 := by rw [hgabs]; exact hcurv
    have hshift : |ι * t| ≤ 1 := by
      simpa only [abs_mul, hιabs, one_mul] using hta.trans hδ1
    have hshift' := abs_le.mp hshift
    refine ⟨?_, ?_, hgjet, fun k hk => ?_⟩
    · have he := (abs_le.mp (hgdiff.trans hvariation)).1
      linarith only [hδg, hMδ, he]
    · have he := (abs_le.mp (hwdiff.trans hvariation)).1
      linarith only [hheight, hMδ, he]
    · exact hjets k hk _ ⟨by linarith only [hshift'.1], by linarith only [hshift'.2]⟩
  refine ⟨ι, g, hι, hg, hgabs, hfactor, hlocal, ?_⟩
  intro t ht
  have htc : t ∈ Icc (-δ) δ := ⟨ht.1, ht.2.le.trans hδ.le⟩
  have hgt := (hlocal t htc).1
  have he : deriv w (r + ι * t) = (-t) * g t := by
    linarith only [hfactor t]
  have hbound : δ * (-t) ≤ deriv w (r + ι * t) := by
    rw [he, mul_comm δ (-t)]
    exact mul_le_mul_of_nonneg_left hgt (neg_nonneg.mpr ht.2.le)
  exact ⟨(mul_pos hδ (neg_pos.mpr ht.2)).trans_le hbound, hbound⟩

end ContinuousFlexibility.Analysis
