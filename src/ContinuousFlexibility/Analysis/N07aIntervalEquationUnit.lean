import ContinuousFlexibility.Analysis.N07aIntervalUnitPullback
import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient

/-!
# Affine normalization of the actual second-order weak equation

The coefficient and unknown are pulled back as the same functions. The
square interval factor on both the lower coefficient and source is exact.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem n07aIntervalUnitInverse_test {a b : ℝ} (hab : a < b)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fun y => φ (n07aIntervalUnitInverse a b y)) ∧
      HasCompactSupport (fun y => φ (n07aIntervalUnitInverse a b y)) ∧
      tsupport (fun y => φ (n07aIntervalUnitInverse a b y)) ⊆ Ioo a b := by
  have hi : ContDiff ℝ ∞ (n07aIntervalUnitInverse a b) :=
    (contDiff_id.sub contDiff_const).div_const (b - a)
  refine ⟨hφ.comp hi, ?_, ?_⟩
  · apply HasCompactSupport.intro
      (hc.image ((continuous_const.mul continuous_id).add continuous_const))
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hy'
    apply hy
    exact ⟨n07aIntervalUnitInverse a b y, hy', n07aIntervalUnitMap_inverse hab y⟩
  · intro y hy
    have hh := hs ((tsupport_comp_subset_preimage φ hi.continuous) hy)
    have hm := n07aIntervalUnitMap_mem hab hh
    rwa [n07aIntervalUnitMap_inverse hab] at hm

theorem n07a_deriv_comp_intervalUnitMap (f : ℝ → ℝ) (a b x : ℝ) :
    deriv (fun y => f (n07aIntervalUnitMap a b y)) x =
      (b - a) * deriv f (n07aIntervalUnitMap a b x) := by
  simpa only [iteratedDeriv_one, pow_one, n07aIntervalUnitMap, add_comm] using
    n07a_iteratedDeriv_comp_affine f a (b - a) 1 x

theorem n07a_interval_equation_unit {a b : ℝ} (hab : a < b)
    (A C u G : ℝ → ℝ)
    (heq : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ y, u y * deriv (fun t => A t * deriv φ t) y) =
        ∫ y, (C y * u y + G y) * φ y) :
    ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) 1 →
      (∫ x, u (n07aIntervalUnitMap a b x) *
        deriv (fun y => A (n07aIntervalUnitMap a b y) * deriv φ y) x) =
        ∫ x, ((b - a) ^ 2 * C (n07aIntervalUnitMap a b x) *
          u (n07aIntervalUnitMap a b x) + (b - a) ^ 2 * G (n07aIntervalUnitMap a b x)) * φ x := by
  intro φ hφ hc hs
  let ψ := fun y => φ (n07aIntervalUnitInverse a b y)
  obtain ⟨hψ, hcψ, hsψ⟩ := n07aIntervalUnitInverse_test hab hφ hc hs
  have hlen : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  have hψmap (x : ℝ) : ψ (n07aIntervalUnitMap a b x) = φ x := by
    dsimp only [ψ]
    rw [n07aIntervalUnitInverse_map hab]
  have hdψ (y : ℝ) : deriv ψ y = deriv φ (n07aIntervalUnitInverse a b y) / (b - a) := by
    have hi : HasDerivAt (n07aIntervalUnitInverse a b) (1 / (b - a)) y :=
      ((hasDerivAt_id y).sub_const a).div_const (b - a)
    have hp : HasDerivAt ψ
        (deriv φ (n07aIntervalUnitInverse a b y) * (1 / (b - a))) y :=
      ((hφ.differentiable (by simp) _).hasDerivAt).comp y hi
    simpa only [mul_one_div] using hp.deriv
  let H := fun y => A y * deriv φ (n07aIntervalUnitInverse a b y)
  have hH : (fun x => H (n07aIntervalUnitMap a b x)) =
      fun x => A (n07aIntervalUnitMap a b x) * deriv φ x := by
    funext x
    dsimp only [H]
    rw [n07aIntervalUnitInverse_map hab]
  have hflux : (fun y => A y * deriv ψ y) = fun y => H y / (b - a) := by
    funext y
    rw [hdψ]
    exact (mul_div_assoc _ _ _).symm
  have hdx (x : ℝ) : deriv (fun y => A y * deriv ψ y) (n07aIntervalUnitMap a b x) =
      deriv (fun y => A (n07aIntervalUnitMap a b y) * deriv φ y) x / (b - a) ^ 2 := by
    rw [hflux, deriv_div_const, ← hH, n07a_deriv_comp_intervalUnitMap]
    field_simp [hlen]
  have hleft : (∫ y, u y * deriv (fun t => A t * deriv ψ t) y) =
      (b - a)⁻¹ * ∫ x, u (n07aIntervalUnitMap a b x) *
        deriv (fun y => A (n07aIntervalUnitMap a b y) * deriv φ y) x := by
    rw [n07aIntervalUnitMap_integral hab]
    simp_rw [hdx, ← mul_div_assoc]
    rw [integral_div]
    field_simp [hlen]
  have h := heq ψ hψ hcψ hsψ
  rw [hleft, n07aIntervalUnitMap_integral hab (fun y => (C y * u y + G y) * ψ y)] at h
  simp_rw [hψmap] at h
  have hscaled := congrArg ((b - a) * ·) h
  rw [← mul_assoc, mul_inv_cancel₀ hlen, one_mul] at hscaled
  have he : (fun x => ((b - a) ^ 2 * C (n07aIntervalUnitMap a b x) *
      u (n07aIntervalUnitMap a b x) + (b - a) ^ 2 * G (n07aIntervalUnitMap a b x)) * φ x) =
      fun x => (b - a) ^ 2 * ((C (n07aIntervalUnitMap a b x) *
        u (n07aIntervalUnitMap a b x) + G (n07aIntervalUnitMap a b x)) * φ x) := by
    funext x
    ring
  rw [he, integral_const_mul]
  exact hscaled.trans (by ring)

end ContinuousFlexibility.Analysis
