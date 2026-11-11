import ContinuousFlexibility.Radial.R07ConeSolution
import ContinuousFlexibility.Radial.R07CapPullback
import ContinuousFlexibility.Radial.R07JoinSmallness
import ContinuousFlexibility.Radial.R07AngleScale
import ContinuousFlexibility.Radial.R07FiniteAngles

/-!
# The actual first-band cone solution across its short join

The cone fixes the incoming normalization at the cut. Dividing by its
positive value at the join gives a state with a fixed cone slope, so the
same transfer estimate used for the infinite height selection applies.
The angle is then transferred back to the required cut normalization.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def r07ConeSlope (right : Bool) (j : ℕ) : ℝ :=
  (if right then 1 else -1) / (j : ℝ) - 1

theorem r07ConeSlope_mem (right : Bool) {j : ℕ} (hj : 2 ≤ j) :
    r07ConeSlope right j ∈ Icc (-(3 : ℝ) / 2) (-1 / 2) := by
  have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hj₀ : (0 : ℝ) < j := lt_of_lt_of_le (by norm_num) hjr
  have hlo : (0 : ℝ) ≤ 1 / (j : ℝ) := (one_div_pos.mpr hj₀).le
  have hhi : 1 / (j : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hjr
  cases right <;>
    simp only [r07ConeSlope, Bool.false_eq_true, ite_false, ite_true, neg_div] <;>
    constructor <;> linarith only [hlo, hhi]

theorem r07ConeSlope_ne_zero (right : Bool) {j : ℕ} (hj : 2 ≤ j) :
    r07ConeSlope right j ≠ 0 :=
  ne_of_lt ((r07ConeSlope_mem right hj).2.trans_lt (by norm_num))

/-- An ideal first-band angle persists for the actual cut-normalized
incoming solution after its sufficiently short positive join. -/
theorem exists_r07_cone_incoming_angle {D : ReferenceData}
    (hD : RadialProfileGeometry D) {right : Bool} {j : ℕ} (hj : 2 ≤ j)
    {c p e scale contrast δ : ℝ} {v : ℝ → ℝ}
    (hc : c ∈ radialCore D) (hp : p ∈ radialCore D) (he : e ∈ radialCore D)
    (horder : if right then c < p ∧ p < e else e < p ∧ p < c)
    (hs : 0 < scale)
    (hcone : ∀ r ∈ uIcc c p, D.w =ᶠ[𝓝 r] fun x => scale * x)
    (hcontrast : 1 ≤ contrast)
    (hw : ∀ r ∈ uIcc p e,
      0 < D.w r ∧ D.w r ≤ contrast * D.w p ∧ D.w p ≤ contrast * D.w r)
    (hδ : 0 < δ) (hδ48 : δ ≤ 1 / 48)
    (hsmall : 2 * (j : ℝ) ^ 2 * contrast / min p e * |e - p| ≤ δ / 12)
    (hideal : 2 * δ ≤ radialAngleSine (1, r07ConeSlope right j)
      (radialState D j e (D.w p) v)) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
      u c = 1 ∧ deriv u c = (if right then (j : ℝ) else -(j : ℝ)) / c ∧
      0 < u p ∧
      (∀ r ∈ uIcc c e, radialJacobi ((j : ℝ) ^ 2) D.w u r = 0) ∧
      (∀ r ∈ radialOpenSpan c p, 0 < deriv D.w r) ∧
      δ ≤ radialAngleSine (radialState D j e (D.w p) u)
        (radialState D j e (D.w p) v) := by
  obtain ⟨u, hu, hu₀, hu₁, hup, hueq, hdup, hwd⟩ :=
    exists_r07_cone_incoming hD hj hc hp he horder hs hcone
  let z : ℝ → ℝ := fun r => (u p)⁻¹ * u r
  have hz : ContDiff ℝ ∞ z := contDiff_const.mul hu
  have hz' : ContDiff ℝ ∞ (deriv z) := (contDiff_infty_iff_deriv.mp hz).2
  have hw' : ContDiff ℝ ∞ D.w := hD.2.2.1.1
  have hp₀ : 0 < p := hD.1.trans hp.1
  have he₀ : 0 < e := hD.1.trans he.1
  have hW : 0 < D.w p := hD.2.2.2.2.1 p hp
  have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hj₀ : (0 : ℝ) < j := lt_of_lt_of_le (by norm_num) hjr
  have hJ : 1 ≤ (j : ℝ) ^ 2 := by
    calc
      (1 : ℝ) ≤ 2 ^ 2 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hjr 2
  have hz₀ : z p = 1 := inv_mul_cancel₀ hup.ne'
  have hz₁ : deriv z p = (if right then (j : ℝ) else -(j : ℝ)) / p := by
    change deriv (fun r => (u p)⁻¹ * u r) p = _
    rw [deriv_const_mul_field, hdup]
    field_simp [hup.ne', hp₀.ne'] <;> ring
  have hstart : joinState ((j : ℝ) ^ 2) (D.w p) D.w z p =
      (1, r07ConeSlope right j) := by
    apply Prod.ext
    · exact hz₀
    · change D.w p / D.w p * (p * deriv z p / (j : ℝ) ^ 2 - z p) =
        r07ConeSlope right j
      rw [div_self hW.ne', one_mul, hz₀, hz₁]
      cases right <;>
        simp only [r07ConeSlope, Bool.false_eq_true, ite_false, ite_true] <;>
        field_simp [hp₀.ne', hj₀.ne'] <;> ring
  have hpFull : p ∈ uIcc c e := by
    cases right
    · rw [uIcc_of_ge (horder.1.trans horder.2).le]
      exact ⟨horder.1.le, horder.2.le⟩
    · rw [uIcc_of_le (horder.1.trans horder.2).le]
      exact ⟨horder.1.le, horder.2.le⟩
  have hsub : uIcc p e ⊆ uIcc c e :=
    ordConnected_uIcc.uIcc_subset hpFull right_mem_uIcc
  have hzeq : ∀ r ∈ uIcc p e, radialJacobi ((j : ℝ) ^ 2) D.w z r = 0 := by
    intro r hr
    change radialJacobi ((j : ℝ) ^ 2) D.w (fun x => (u p)⁻¹ * u x) r = 0
    rw [radialJacobi_const_mul, hueq r (hsub hr), mul_zero]
  have hclose :
      |(radialState D j e (D.w p) z).1 - 1| ≤ δ / 4 ∧
      |(radialState D j e (D.w p) z).2 - r07ConeSlope right j| ≤ δ / 4 :=
    r07_joinState_close (lt_min hp₀ he₀) hJ hW hcontrast
      (fun r _ => ⟨hw'.differentiable (by simp) r, hz.differentiable (by simp) r,
        hz'.differentiable (by simp) r⟩)
      hw hzeq left_mem_uIcc right_mem_uIcc hstart
      (r07ConeSlope_mem right hj) (hδ48.trans (by norm_num)) hsmall
  have hB : radialState D j e (D.w p) v ≠ (0, 0) := by
    intro hzero
    rw [hzero] at hideal
    norm_num [radialAngleSine] at hideal
    linarith only [hδ, hideal]
  have hangle := r07_angle_lower_of_near hB hδ hδ48 hclose hideal
  have hscale :
      radialAngleSine (radialState D j e (D.w p) z) (radialState D j e (D.w p) v) =
      radialAngleSine (radialState D j e (D.w p) u) (radialState D j e (D.w p) v) := by
    change radialAngleSine (radialState D j e (D.w p) (fun x => (u p)⁻¹ * u x)) _ = _
    rw [radialState_const_mul D j e (D.w p) (u p)⁻¹ (hu.differentiable (by simp) e),
      radialAngleSine_scale_left (inv_ne_zero hup.ne')]
  rw [hscale] at hangle
  exact ⟨u, hu, hu₀, hu₁, hup, hueq, hwd, hangle⟩

end ContinuousFlexibility.Radial
