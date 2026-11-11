import ContinuousFlexibility.Contracts.CapInteriorClosure
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The actual cap body has one connected inside and one connected exterior

The explicit continuous wall-straightening is followed by an affine vertical
normalization and the genuine complex-coordinate homeomorphism of the plane.
The resulting ball uses the product max norm on `ℂ × ℝ`; no Euclidean metric
identity for `PolarPoint` is asserted. These are properties of the actual cap
body, before the moving graph and the marker are inserted.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Metric

set_option backward.isDefEq.respectTransparency false

def capCylinderNormalization (h : ℝ) {L : ℝ} (hL : 0 < L) :
    (PolarPoint × ℝ) ≃ₜ (ℂ × ℝ) where
  toFun := fun q => (Complex.equivRealProdCLM.symm q.1,
    (2 * q.2 - (2 * h - L * capDrop)) / (L * capDrop))
  invFun := fun q => (Complex.equivRealProdCLM q.1,
    (L * capDrop * q.2 + 2 * h - L * capDrop) / 2)
  left_inv := by
    intro q
    apply Prod.ext
    · exact Complex.equivRealProdCLM.apply_symm_apply q.1
    · dsimp
      field_simp [hL.ne', capDrop_pos.ne']; ring
  right_inv := by
    intro q
    apply Prod.ext
    · exact Complex.equivRealProdCLM.symm_apply_apply q.1
    · dsimp
      field_simp [hL.ne', capDrop_pos.ne']; ring
  continuous_toFun :=
    (Complex.equivRealProdCLM.symm.continuous.comp continuous_fst).prodMk
      (((continuous_const.mul continuous_snd).sub continuous_const).div_const _)
  continuous_invFun :=
    (Complex.equivRealProdCLM.continuous.comp continuous_fst).prodMk
      ((((continuous_const.mul continuous_snd).add continuous_const).sub
        continuous_const).div_const _)

theorem cap_normalized_height_abs_lt {h L z : ℝ} (hL : 0 < L) :
    |(2 * z - (2 * h - L * capDrop)) / (L * capDrop)| < 1 ↔
      z ∈ Ioo (h - L * capDrop) h := by
  have hd := mul_pos hL capDrop_pos
  rw [abs_lt, lt_div_iff₀ hd, div_lt_iff₀ hd]
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hl, hr⟩
    exact ⟨by linarith, by linarith⟩

def capBallHomeomorph {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    E3 ≃ₜ (ℂ × ℝ) :=
  (capCylinderHomeomorph hR hL h).trans (capCylinderNormalization h hL)

theorem capRevolutionInterior_eq_preimage_ball {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    capRevolutionInterior R h L = (capBallHomeomorph hR hL h) ⁻¹'
      ball (0 : ℂ × ℝ) 1 := by
  rw [capRevolutionInterior_eq_preimage_cylinder hR hL h]
  ext v
  let q := capCylinderHomeomorph hR hL h v
  change (cartesianRadius q.1 < 1 ∧ q.2 ∈ Ioo (h - L * capDrop) h) ↔
    dist (capCylinderNormalization h hL q) 0 < 1
  rw [dist_zero_right, Prod.norm_def, max_lt_iff, Real.norm_eq_abs]
  change (cartesianRadius q.1 < 1 ∧ q.2 ∈ Ioo (h - L * capDrop) h) ↔
    (cartesianRadius q.1 < 1 ∧
      |(2 * q.2 - (2 * h - L * capDrop)) / (L * capDrop)| < 1)
  rw [cap_normalized_height_abs_lt hL]

theorem isConnected_compl_unitClosedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hdim : 1 < Module.rank ℝ E) :
    IsConnected (closedBall (0 : E) 1)ᶜ := by
  let f : E × ℝ → E := fun q => q.2 • q.1
  have hc := (isConnected_sphere hdim (0 : E) (by norm_num : (0 : ℝ) ≤ 1)).prod
    (isConnected_Ioi : IsConnected (Ioi (1 : ℝ)))
  have him := hc.image f (continuous_snd.smul continuous_fst).continuousOn
  have he : f '' (sphere (0 : E) 1 ×ˢ Ioi (1 : ℝ)) = (closedBall (0 : E) 1)ᶜ := by
    ext y
    constructor
    · rintro ⟨⟨u, r⟩, ⟨hu, hr⟩, rfl⟩
      change 1 < r at hr
      have hn : ‖u‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hu
      change ¬dist (r • u) 0 ≤ 1
      rw [dist_zero_right, norm_smul, Real.norm_eq_abs, hn,
        abs_of_pos (by linarith : 0 < r), mul_one]
      exact not_le.mpr hr
    · intro hy
      have hr : 1 < ‖y‖ := by simpa only [mem_compl_iff, mem_closedBall,
        dist_zero_right, not_le] using hy
      have hp : 0 < ‖y‖ := lt_trans zero_lt_one hr
      refine ⟨(‖y‖⁻¹ • y, ‖y‖), ⟨?_, hr⟩, ?_⟩
      · simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
      · dsimp [f]
        rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
  rwa [he] at him

theorem isConnected_capRevolutionInterior {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    IsConnected (capRevolutionInterior R h L) := by
  rw [capRevolutionInterior_eq_preimage_ball hR hL h]
  exact (capBallHomeomorph hR hL h).isConnected_preimage.mpr
    (isConnected_ball (by norm_num))

theorem isConnected_capRevolutionExterior {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    IsConnected (closure (capRevolutionInterior R h L))ᶜ := by
  rw [capRevolutionInterior_eq_preimage_ball hR hL h,
    ← (capBallHomeomorph hR hL h).preimage_closure,
    closure_ball (0 : ℂ × ℝ) (by norm_num : (1 : ℝ) ≠ 0), ← preimage_compl]
  apply (capBallHomeomorph hR hL h).isConnected_preimage.mpr
  apply isConnected_compl_unitClosedBall
  apply Module.one_lt_rank_of_one_lt_finrank
  simp [Module.finrank_prod]

theorem unbounded_capRevolutionExterior (R h : ℝ) {L : ℝ} (hL : 0 < L) :
    ¬Bornology.IsBounded (closure (capRevolutionInterior R h L))ᶜ := by
  obtain ⟨K, hK, hsub⟩ := capRevolutionInterior_subset_compact R h hL
  have hb : Bornology.IsBounded (closure (capRevolutionInterior R h L)) :=
    hK.isBounded.subset (closure_minimal hsub hK.isClosed)
  intro he
  apply NormedSpace.unbounded_univ ℝ E3
  simpa only [union_compl_self] using hb.union he

end ContinuousFlexibility
