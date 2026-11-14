module

public import ContinuousFlexibility.Analysis.MaterialRadialExpansion
public import ContinuousFlexibility.Analysis.MaterialOrdinaryJets

/-!
# Actual affine-coordinate jets used by the reference height

These estimates depend only on the scalar affine material model. In
particular, the sample function is arbitrary and no trace assertion is
used to obtain regularity of the coordinate or its weights.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem n01a_affine_ell_upper {D : ReferenceData} {sample : ℕ → ℝ}
    (hab : D.a < D.b) {r : ℝ} (hr : r ∈ radialCore D) :
    (affineMaterialData D sample).ell r ≤ D.b - D.a := by
  let t := affineMaterialUnitCoordinate D r
  have ht : t ∈ Ioo (0 : ℝ) 1 := affineMaterialUnitCoordinate_mem hab hr
  have hL : endpointEll 1 t ≤ 1 := by
    change t / (1 + endpointX 1 t) ≤ 1
    apply (div_le_iff₀ (by
      change 0 < 1 + Real.sqrt (Real.log (1 / t))
      positivity)).mpr
    have hx : 0 ≤ endpointX 1 t := Real.sqrt_nonneg _
    linarith only [ht.2, hx]
  have hR : endpointEll 1 (1 - t) ≤ 1 := by
    change (1 - t) / (1 + endpointX 1 (1 - t)) ≤ 1
    apply (div_le_iff₀ (by
      change 0 < 1 + Real.sqrt (Real.log (1 / (1 - t)))
      positivity)).mpr
    have hx : 0 ≤ endpointX 1 (1 - t) := Real.sqrt_nonneg _
    linarith only [ht.1, hx]
  have hunit : materialIntervalEll t ≤ 1 := by
    have hη := materialIntervalTransition_nonneg t
    have hη₁ := materialIntervalTransition_le_one t
    have hl := mul_le_mul_of_nonneg_left hL (sub_nonneg.mpr hη₁)
    have hr := mul_le_mul_of_nonneg_left hR hη
    change (1 - materialIntervalTransition t) * endpointEll 1 t +
      materialIntervalTransition t * endpointEll 1 (1 - t) ≤ 1
    nlinarith only [hl, hr]
  change (D.b - D.a) * materialIntervalEll t ≤ D.b - D.a
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hunit (sub_pos.mpr hab).le

theorem n01a_affine_scalar_rpow_jets {D : ReferenceData} {sample : ℕ → ℝ}
    (hab : D.a < D.b) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (radialCore D))
    (hp : ∀ r ∈ radialCore D, 0 < f r)
    (hlog : ∀ n : ℕ, 0 < n → ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ radialCore D,
      |materialDerivativeIterate (affineMaterialData D sample) n
        (fun y => Real.log (f y)) r| ≤ C) (γ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv n (fun t => f ((affineMaterialData D sample).radius t) ^ γ) x| ≤
        C * f ((affineMaterialData D sample).radius x) ^ γ := by
  let T := affineMaterialData D sample
  have hi (x : ℝ) : T.radius x ∈ radialCore D :=
    (affineMaterialData_radius_mem_rho (sample := sample) hab x).1
  have hlf : ContDiffOn ℝ ∞ (fun r => Real.log (f r)) (radialCore D) :=
    hf.log (fun r hr => (hp r hr).ne')
  let L : ℝ → ℝ := fun x => Real.log (f (T.radius x)) * γ
  have hL : ContDiff ℝ ∞ L :=
    (hlf.comp_contDiff (contDiff_affineMaterialData_radius (sample := sample)) hi).mul contDiff_const
  have hLb (k : ℕ) (hk : 0 < k) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv k L x| ≤ C := by
    obtain ⟨C, hC, hb⟩ := hlog k hk
    refine ⟨C * |γ|, mul_nonneg hC (abs_nonneg _), fun x => ?_⟩
    change |iteratedDeriv k (fun t => Real.log (f (T.radius t)) * γ) x| ≤ _
    rw [iteratedDeriv_mul_const_field,
      iteratedDeriv_comp_affineMaterialRadius hab hlf, abs_mul]
    exact mul_le_mul_of_nonneg_right (hb (T.radius x) (hi x)) (abs_nonneg _)
  have heq : (fun x => f (T.radius x) ^ γ) = (fun x => Real.exp (L x)) := by
    funext x
    exact Real.rpow_def_of_pos (hp _ (hi x)) γ
  obtain ⟨C, hC, hb⟩ := iteratedDeriv_exp_majorant hL hLb n
  refine ⟨C, hC, fun x => ?_⟩
  rw [heq, congrFun heq x]
  exact hb x

theorem n01a_affine_H_rpow_jets {D : ReferenceData} {sample : ℕ → ℝ}
    (hab : D.a < D.b) (γ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv n (fun t => (affineMaterialData D sample).H
          ((affineMaterialData D sample).radius t) ^ γ) x| ≤
        C * (affineMaterialData D sample).H ((affineMaterialData D sample).radius x) ^ γ := by
  let T := affineMaterialData D sample
  have hH : ContDiffOn ℝ ∞ T.H (radialCore D) :=
    affineMaterialData_smooth_scalar (sample := sample) hab T.H (by simp [T])
  have hlog (k : ℕ) (hk : 0 < k) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ radialCore D,
      |materialDerivativeIterate T k (fun y => Real.log (T.H y)) r| ≤ C := by
    obtain ⟨C, hC, hb⟩ := logarithmicDerivativeBounds_affineMaterialData (sample := sample) hab k hk
    exact ⟨C, hC, fun r hr => (hb r hr).1⟩
  exact n01a_affine_scalar_rpow_jets (sample := sample) hab hH
    (fun r hr => (affineMaterialData_positive (sample := sample) hab hr).2.1) hlog γ n

theorem n01a_affine_radius_jets {D : ReferenceData} {sample : ℕ → ℝ}
    (hab : D.a < D.b) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv n (affineMaterialData D sample).radius x| ≤ C := by
  let T := affineMaterialData D sample
  have hi (x : ℝ) := (affineMaterialData_radius_mem_rho (sample := sample) hab x).1
  cases n with
  | zero =>
      refine ⟨|D.a| + |D.b|, add_nonneg (abs_nonneg _) (abs_nonneg _), fun x => ?_⟩
      rw [iteratedDeriv_zero]
      exact abs_le.mpr ⟨by linarith [(hi x).1, neg_abs_le D.a, abs_nonneg D.b],
        by linarith [(hi x).2, le_abs_self D.b, abs_nonneg D.a]⟩
  | succ n =>
      have hell : ContDiffOn ℝ ∞ T.ell (radialCore D) :=
        affineMaterialData_smooth_scalar (sample := sample) hab _ (by simp [T])
      have hp (r : ℝ) (hr : r ∈ radialCore D) : 0 < T.ell r :=
        (affineMaterialData_positive (sample := sample) hab hr).1
      have hlog (k : ℕ) (hk : 0 < k) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ radialCore D,
          |materialDerivativeIterate T k (fun y => Real.log (T.ell y)) r| ≤ C := by
        obtain ⟨C, hC, hb⟩ := logarithmicDerivativeBounds_affineMaterialData
          (sample := sample) hab k hk
        exact ⟨C, hC, fun r hr => (hb r hr).2.2⟩
      obtain ⟨C, hC, hb⟩ := n01a_affine_scalar_rpow_jets (sample := sample) hab hell hp hlog 1 n
      have hd : deriv T.radius = fun x => T.ell (T.radius x) :=
        funext fun x => (hasDerivAt_affineMaterialData_radius (sample := sample) hab x).deriv
      refine ⟨C * (D.b - D.a), mul_nonneg hC (sub_pos.mpr hab).le, fun x => ?_⟩
      rw [iteratedDeriv_succ', hd]
      have hb' : |iteratedDeriv n (fun t => T.ell (T.radius t)) x| ≤ C * T.ell (T.radius x) := by
        simpa only [Real.rpow_one] using hb x
      exact hb'.trans (mul_le_mul_of_nonneg_left
        (n01a_affine_ell_upper (sample := sample) hab (hi x)) hC)

end ContinuousFlexibility.Statements
