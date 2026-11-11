import ContinuousFlexibility.Analysis.ReturnVelocityCollarExtension
import ContinuousFlexibility.Analysis.PolynomialJetOperations

/-!
# Reflection preserves the exact independent-residual height weight

The odd and even reconstruction of the drift and optical speed uses a
fixed linear reflection of the angular coordinate. Its mixed jets
preserve the same height factor as the actual correction velocity.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem norm_iteratedFDeriv_reflected_linear_weighted_bound
    {ι : Type*} (W H : ι → ℝ) (hW : ∀ i, 1 ≤ W i) (hH : ∀ i, 0 < H i)
    (f : ι → (ℝ × ℝ) → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hbound : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p,
      ‖iteratedFDeriv ℝ k (f i) p‖ ≤ A * H i * W i ^ P)
    (a b : ℝ) (n : ℕ) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p,
      ‖iteratedFDeriv ℝ n (fun q => a * f i q + b * f i (q.1, -q.2)) p‖ ≤
        A * H i * W i ^ P := by
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-ContinuousLinearMap.snd ℝ ℝ ℝ)
  let g (i : ι) (p : ℝ × ℝ) : ℝ := f i (L p)
  have hg (i : ι) : ContDiff ℝ ∞ (g i) := (hf i).comp L.contDiff
  have hgb : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p, p ∈ (univ : Set (ℝ × ℝ)) →
      ‖iteratedFDeriv ℝ n (g i) p‖ ≤ A * H i * W i ^ P := by
    apply norm_iteratedFDeriv_comp_weighted_polynomial_bound
      W H hW hH (fun _ => univ) (fun _ => univ)
      (fun _ => isOpen_univ) (fun _ => isOpen_univ)
      (fun _ => L) f (fun _ => L.contDiff.contDiffOn)
      (fun i => (hf i).contDiffOn) (fun _ _ _ => mem_univ _) n
    · intro k _
      obtain ⟨A, P, hA, hP, hb⟩ := hbound k
      exact ⟨A, P, hA, hP, fun i p _ => hb i (L p)⟩
    · intro k hk _
      refine ⟨‖L‖, 0, ContinuousLinearMap.opNorm_nonneg L, le_rfl, fun i p _ => ?_⟩
      simpa only [Real.rpow_zero, mul_one] using norm_iteratedFDeriv_linear_of_pos L k hk p
  have hfb : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p, p ∈ (univ : Set (ℝ × ℝ)) →
      ‖iteratedFDeriv ℝ n (f i) p‖ ≤ A * H i * W i ^ P := by
    obtain ⟨A, P, hA, hP, hb⟩ := hbound n
    exact ⟨A, P, hA, hP, fun i p _ => hb i p⟩
  let La : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ
  let Lb : ℝ →L[ℝ] ℝ := b • ContinuousLinearMap.id ℝ ℝ
  have hab := norm_iteratedFDeriv_clm_left_weighted_polynomial_bound
    W H (fun _ => univ) (fun _ => isOpen_univ) f
    (fun i => (hf i).contDiffOn) La n hfb
  have hbb := norm_iteratedFDeriv_clm_left_weighted_polynomial_bound
    W H (fun _ => univ) (fun _ => isOpen_univ) g
    (fun i => (hg i).contDiffOn) Lb n hgb
  obtain ⟨A, P, hA, hP, hb⟩ := norm_iteratedFDeriv_add_weighted_polynomial_bound
    W H hW hH (fun _ => univ) (fun _ => isOpen_univ)
    (fun i p => La (f i p)) (fun i p => Lb (g i p))
    (fun i => (La.contDiff.comp (hf i)).contDiffOn)
    (fun i => (Lb.contDiff.comp (hg i)).contDiffOn) n hab hbb
  refine ⟨A, P, hA, hP, fun i p => ?_⟩
  have heq : (fun q => a * f i q + b * f i (q.1, -q.2)) =
      (fun q => La (f i q) + Lb (g i q)) := by
    funext q
    rfl
  rw [heq]
  exact hb i p (mem_univ _)

private theorem reflected_drift_speed_weighted_bounds
    {ι : Type*} (W H : ι → ℝ) (hW : ∀ i, 1 ≤ W i) (hH : ∀ i, 0 < H i)
    (f d e : ι → (ℝ × ℝ) → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hbound : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p,
      ‖iteratedFDeriv ℝ k (f i) p‖ ≤ A * H i * W i ^ P)
    (hd : ∀ i p, d i p = (f i p - f i (p.1, -p.2)) / 2)
    (he : ∀ i p, e i p = (-f i (p.1, -p.2) - f i p) / 2) (n : ℕ) :
    (∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p,
      ‖iteratedFDeriv ℝ n (d i) p‖ ≤ A * H i * W i ^ P) ∧
    (∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p,
      ‖iteratedFDeriv ℝ n (e i) p‖ ≤ A * H i * W i ^ P) := by
  constructor
  · obtain ⟨A, P, hA, hP, hb⟩ := norm_iteratedFDeriv_reflected_linear_weighted_bound
      W H hW hH f hf hbound (1 / 2) (-1 / 2) n
    refine ⟨A, P, hA, hP, fun i p => ?_⟩
    have heq : d i = fun q => (1 / 2) * f i q + (-1 / 2) * f i (q.1, -q.2) := by
      funext q
      rw [hd i q]
      ring
    exact (congrArg (fun g : (ℝ × ℝ) → ℝ => ‖iteratedFDeriv ℝ n g p‖) heq).trans_le
      (hb i p)
  · obtain ⟨A, P, hA, hP, hb⟩ := norm_iteratedFDeriv_reflected_linear_weighted_bound
      W H hW hH f hf hbound (-1 / 2) (-1 / 2) n
    refine ⟨A, P, hA, hP, fun i p => ?_⟩
    have heq : e i = fun q => (-1 / 2) * f i q + (-1 / 2) * f i (q.1, -q.2) := by
      funext q
      rw [he i q]
      ring
    exact (congrArg (fun g : (ℝ × ℝ) → ℝ => ‖iteratedFDeriv ℝ n g p‖) heq).trans_le
      (hb i p)

end ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency true

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped ContDiff

theorem returnCorrectionDriftSpeedLinear_contDiff_of_velocity
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (ρ : CircleSpace S)
    (hV : ∀ m, ContDiff ℝ ∞
      (fun p => returnCorrectionVelocityLinear D S C χ z m p ρ)) (m : ℕ) :
    ContDiff ℝ ∞ (fun p => returnCorrectionDriftLinear D S C χ z m p ρ) ∧
      ContDiff ℝ ∞ (fun p => returnCorrectionSpeedLinear D S C χ z m p ρ) := by
  have hr : ContDiff ℝ ∞ (fun p : PolarPoint => (p.1, -p.2)) :=
    contDiff_fst.prodMk contDiff_snd.neg
  have hvr : ContDiff ℝ ∞
      (fun p : PolarPoint => returnCorrectionVelocityLinear D S C χ z m (p.1, -p.2) ρ) := by
    simpa only [Function.comp_def] using (hV m).comp hr
  constructor
  · have h := ((hV m).sub hvr).div_const 2
    exact h.congr (fun p => (returnCorrectionDriftLinear_apply D S C χ z m p ρ).symm)
  · have h := (hvr.neg.sub (hV m)).div_const 2
    exact h.congr (fun p => (returnCorrectionSpeedLinear_apply D S C χ z m p ρ).symm)

theorem returnCorrectionDriftSpeedLinear_weighted_bound_of_velocity
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (ρ : CircleSpace S)
    (W H : ℕ → ℝ) (hW : ∀ m, 1 ≤ W m) (hH : ∀ m, 0 < H m)
    (hV : ∀ m, ContDiff ℝ ∞
      (fun p => returnCorrectionVelocityLinear D S C χ z m p ρ))
    (hbound : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      ‖iteratedFDeriv ℝ k
        (fun q => returnCorrectionVelocityLinear D S C χ z m q ρ) p‖ ≤
          A * H m * W m ^ P) (n : ℕ) :
    (∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      ‖iteratedFDeriv ℝ n (fun q => returnCorrectionDriftLinear D S C χ z m q ρ) p‖ ≤
        A * H m * W m ^ P) ∧
    (∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      ‖iteratedFDeriv ℝ n (fun q => returnCorrectionSpeedLinear D S C χ z m q ρ) p‖ ≤
        A * H m * W m ^ P) :=
  reflected_drift_speed_weighted_bounds W H hW hH
    (fun m p => returnCorrectionVelocityLinear D S C χ z m p ρ)
    (fun m p => returnCorrectionDriftLinear D S C χ z m p ρ)
    (fun m p => returnCorrectionSpeedLinear D S C χ z m p ρ)
    hV hbound
    (fun m p => returnCorrectionDriftLinear_apply D S C χ z m p ρ)
    (fun m p => returnCorrectionSpeedLinear_apply D S C χ z m p ρ) n

end ContinuousFlexibility.Statements
