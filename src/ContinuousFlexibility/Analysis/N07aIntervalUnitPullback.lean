import ContinuousFlexibility.Analysis.N07aIntervalWeakSecond
import ContinuousFlexibility.Analysis.N07aAngularLpScale
import ContinuousFlexibility.Analysis.SpacesTorusCell

/-!
# Actual affine normalization of radial weak derivatives

Positive intervals are pulled back to `(0,1)` with their exact Lebesgue
factor. The weak derivative acquires the interval length, and the actual
`L²` representatives and squared norms retain that same normalization.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology ENNReal

def n07aIntervalUnitMap (a b x : ℝ) : ℝ := (b - a) * x + a

def n07aIntervalUnitInverse (a b y : ℝ) : ℝ := (y - a) / (b - a)

theorem n07aIntervalUnitMap_inverse {a b : ℝ} (hab : a < b) (y : ℝ) :
    n07aIntervalUnitMap a b (n07aIntervalUnitInverse a b y) = y := by
  unfold n07aIntervalUnitMap n07aIntervalUnitInverse
  field_simp [(sub_pos.mpr hab).ne']
  ring

theorem n07aIntervalUnitInverse_map {a b : ℝ} (hab : a < b) (x : ℝ) :
    n07aIntervalUnitInverse a b (n07aIntervalUnitMap a b x) = x := by
  unfold n07aIntervalUnitMap n07aIntervalUnitInverse
  field_simp [(sub_pos.mpr hab).ne']
  ring

theorem n07aIntervalUnitMap_mem {a b x : ℝ} (hab : a < b)
    (hx : x ∈ Ioo (0 : ℝ) 1) : n07aIntervalUnitMap a b x ∈ Ioo a b := by
  unfold n07aIntervalUnitMap
  constructor <;> nlinarith [mul_pos (sub_pos.mpr hab) hx.1,
    mul_lt_mul_of_pos_left hx.2 (sub_pos.mpr hab)]

theorem n07aIntervalUnitMap_preserving {a b : ℝ} (hab : a < b) :
    MeasurePreserving (n07aIntervalUnitMap a b)
      (volume.restrict (Ioo (0 : ℝ) 1))
      (n07aAngularNormalizedMeasure (volume.restrict (Ioo a b)) (b - a)) := by
  unfold n07aIntervalUnitMap
  simpa only [n07aAngularNormalizedMeasure,
    restrict_Ioo_eq_restrict_Ioc, mul_zero, zero_add, mul_one, sub_add_cancel] using
    spaces_affineInterval_preserving (b - a) (sub_pos.mpr hab) a 0 1

/-- Exact whole-line substitution; it also applies to compact interior tests. -/
theorem n07aIntervalUnitMap_integral {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) :
    (∫ y, f y) = (b - a) * ∫ x, f (n07aIntervalUnitMap a b x) := by
  have h := Measure.integral_comp_mul_left (fun y => f (y + a)) (b - a)
  rw [integral_add_right_eq_self f a, abs_of_pos (inv_pos.mpr (sub_pos.mpr hab)),
    smul_eq_mul] at h
  unfold n07aIntervalUnitMap
  rw [h, ← mul_assoc, mul_inv_cancel₀ (sub_pos.mpr hab).ne', one_mul]

/-- The actual restriction class, normalized to unit radial coordinates. -/
def n07aIntervalUnitPullback {a b : ℝ} (hab : a < b)
    (u : Lp ℝ 2 (volume.restrict (Ioo a b))) : N07aIntervalL2 :=
  Lp.compMeasurePreserving (n07aIntervalUnitMap a b) (n07aIntervalUnitMap_preserving hab)
    (n07aAngularLpNormalize (volume.restrict (Ioo a b)) (b - a) u)

theorem n07aIntervalUnitPullback_ae {a b : ℝ} (hab : a < b)
    (u : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    (n07aIntervalUnitPullback hab u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x => u (n07aIntervalUnitMap a b x) := by
  have h := (n07aIntervalUnitMap_preserving hab).quasiMeasurePreserving.ae
    (n07aAngularLpNormalize_ae (volume.restrict (Ioo a b)) (b - a) u)
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (n07aAngularLpNormalize (volume.restrict (Ioo a b)) (b - a) u)
    (n07aIntervalUnitMap_preserving hab), h] with x hx hu
  exact hx.trans hu

theorem n07aIntervalUnitPullback_norm_sq {a b : ℝ} (hab : a < b)
    (u : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    ‖n07aIntervalUnitPullback hab u‖ ^ 2 = (b - a)⁻¹ * ‖u‖ ^ 2 := by
  rw [n07aIntervalUnitPullback, Lp.norm_compMeasurePreserving,
    n07aAngularLpNormalize_norm_sq _ _ (sub_pos.mpr hab)]

theorem n07aIntervalUnitMap_memLp {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) :
    MemLp (fun x => f (n07aIntervalUnitMap a b x)) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
  (hf.smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving
    (n07aIntervalUnitMap_preserving hab)

/-- Affine substitution of the actual compact-test identity. No smooth
representative of the unknown is needed. -/
theorem n07a_interval_weakDerivative_unit {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hfg : HasIntervalWeakDerivative a b f g) :
    HasIntervalWeakDerivative 0 1
      (fun x => f (n07aIntervalUnitMap a b x))
      (fun x => (b - a) * g (n07aIntervalUnitMap a b x)) := by
  intro φ hφ hc hs
  let ψ : ℝ → ℝ := fun y => φ (n07aIntervalUnitInverse a b y)
  have hi : ContDiff ℝ ∞ (n07aIntervalUnitInverse a b) :=
    (contDiff_id.sub contDiff_const).div_const (b - a)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp hi
  have hcψ : HasCompactSupport ψ := by
    apply HasCompactSupport.intro
      (hc.image ((continuous_const.mul continuous_id).add continuous_const))
    intro y hy
    dsimp only [ψ]
    apply image_eq_zero_of_notMem_tsupport
    intro hy'
    apply hy
    exact ⟨n07aIntervalUnitInverse a b y, hy', n07aIntervalUnitMap_inverse hab y⟩
  have hsψ : tsupport ψ ⊆ Ioo a b := by
    intro y hy
    have hh := hs ((tsupport_comp_subset_preimage φ hi.continuous) hy)
    have hm := n07aIntervalUnitMap_mem hab hh
    rwa [n07aIntervalUnitMap_inverse hab] at hm
  have hd (y : ℝ) : deriv ψ y =
      deriv φ (n07aIntervalUnitInverse a b y) / (b - a) := by
    have hi' : HasDerivAt (n07aIntervalUnitInverse a b) (1 / (b - a)) y :=
      ((hasDerivAt_id y).sub_const a).div_const (b - a)
    have hp : HasDerivAt ψ
        (deriv φ (n07aIntervalUnitInverse a b y) * (1 / (b - a))) y :=
      ((hφ.differentiable (by simp) _).hasDerivAt).comp y hi'
    simpa only [mul_one_div] using hp.deriv
  have he (x : ℝ) : ψ (n07aIntervalUnitMap a b x) = φ x := by
    dsimp only [ψ]
    rw [n07aIntervalUnitInverse_map hab]
  have hleft : (∫ y, f y * deriv ψ y) =
      ∫ x, f (n07aIntervalUnitMap a b x) * deriv φ x := by
    rw [n07aIntervalUnitMap_integral hab]
    simp_rw [hd, n07aIntervalUnitInverse_map hab, ← mul_div_assoc]
    rw [integral_div]
    exact mul_div_cancel₀ _ (sub_pos.mpr hab).ne'
  have hright : (∫ y, g y * ψ y) =
      ∫ x, ((b - a) * g (n07aIntervalUnitMap a b x)) * φ x := by
    rw [n07aIntervalUnitMap_integral hab]
    simp_rw [he, mul_assoc]
    exact (integral_const_mul _ _).symm
  rw [← hleft, ← hright]
  exact hfg ψ hψ hcψ hsψ

theorem n07aIntervalUnitPullback_weakDerivative {a b : ℝ} (hab : a < b)
    (u d : Lp ℝ 2 (volume.restrict (Ioo a b)))
    (hud : HasIntervalWeakDerivative a b u d) :
    HasIntervalWeakDerivative 0 1 (n07aIntervalUnitPullback hab u)
      ((b - a) • n07aIntervalUnitPullback hab d) := by
  apply n07a_intervalWeakDerivative_congr
    (g := fun x => (b - a) * d (n07aIntervalUnitMap a b x))
    (n07aIntervalUnitPullback_ae hab u).symm
  · filter_upwards [n07aIntervalUnitPullback_ae hab d,
      Lp.coeFn_smul (b - a) (n07aIntervalUnitPullback hab d)] with x hx hd
    simp only [hd, Pi.smul_apply, smul_eq_mul, hx]
  · exact n07a_interval_weakDerivative_unit hab hud

end ContinuousFlexibility.Analysis
