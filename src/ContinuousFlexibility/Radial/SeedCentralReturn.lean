import ContinuousFlexibility.Radial.SeedGluedNegativeCover
import ContinuousFlexibility.Radial.CentralPhysicalTravel
import ContinuousFlexibility.Radial.CentralTurningPoints

/-!
# The actual central negative component in the glued seed

The whole closed turning interval lies inside the retained germ, so both
zero endpoint derivatives and the physical optical integral survive the
gluing exactly.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem SeedGluedPair.central_profile_germ
    {D : ReferenceData} {c d : ℝ} {uL uR : ℝ → ℝ}
    {K : SeedCentralCutoff} {q : ℝ}
    (G : SeedGluedPair D c d uL uR K q) (hq : 0 < q)
    {r : ℝ}
    (hr : r ∈ Icc (centralRadius (-sqrt centralOscillatorA))
      (centralRadius (sqrt centralOscillatorA))) :
    G.profile =ᶠ[𝓝 r] centralRadialProfile 1 := by
  have hL : exp K.left < centralRadius (-sqrt centralOscillatorA) :=
    (lt_log_iff_exp_lt (centralRadius_pos _)).mp K.left_turn
  have hR : centralRadius (sqrt centralOscillatorA) < exp K.right :=
    (log_lt_iff_lt_exp (centralRadius_pos _)).mp K.right_turn
  have hretL := hL.trans_le hr.1
  have hretR := hr.2.trans_lt hR
  have hp : 0 < r := (exp_pos K.left).trans hretL
  have hy : log r ∈ Ioo K.left K.right :=
    ⟨(lt_log_iff_exp_lt hp).mpr hretL, (log_lt_iff_lt_exp hp).mpr hretR⟩
  have hcentral : K.profile =ᶠ[𝓝 r] centralRadialProfile 1 := by
    simpa only [exp_log hp] using K.profile_retained_germ hy
  have hm : r ∈ Ioo (exp (K.left - q - 4)) (exp (K.right + q + 4)) := by
    constructor
    · exact (exp_lt_exp.mpr (by linarith only [hq])).trans hretL
    · exact hretR.trans (exp_lt_exp.mpr (by linarith only [hq]))
  exact (G.middle_germ r hm).1.trans hcentral

/-- The physical central component and its travel survive the actual
three-piece profile construction. -/
theorem SeedGluedPair.central_model_return
    {D : ReferenceData} {c d : ℝ} {uL uR : ℝ → ℝ}
    {K : SeedCentralCutoff} {q : ℝ}
    (G : SeedGluedPair D c d uL uR K q) (hq : 0 < q)
    (hc : c ∈ radialCore D) (hd : d ∈ radialCore D) :
    let E : ReferenceData :=
      { D with a := G.radiusL * D.a, b := G.radiusR * D.b,
        w := G.profile, phi := G.height }
    let l := centralRadius (-sqrt centralOscillatorA)
    let h := centralRadius (sqrt centralOscillatorA)
    NegativeRadialComponent E l h ∧
      radialTravel E l h = Real.pi / (2 * sqrt 2) := by
  let E : ReferenceData :=
    { D with a := G.radiusL * D.a, b := G.radiusR * D.b,
      w := G.profile, phi := G.height }
  let l := centralRadius (-sqrt centralOscillatorA)
  let h := centralRadius (sqrt centralOscillatorA)
  change NegativeRadialComponent E l h ∧ radialTravel E l h = _
  have hlh : l < h := central_turning_radii_pos_ordered.2
  have hL : exp K.left < l :=
    (lt_log_iff_exp_lt (centralRadius_pos _)).mp K.left_turn
  have hR : h < exp K.right :=
    (log_lt_iff_lt_exp (centralRadius_pos _)).mp K.right_turn
  have hRR : 0 < G.radiusR := G.radiusL_pos.trans_le G.radius_order
  have hal : E.a < l :=
    ((mul_lt_mul_of_pos_left hc.1 G.radiusL_pos).trans G.left_entry).trans
      ((exp_lt_exp.mpr (by linarith only [hq])).trans hL)
  have hhb : h < E.b :=
    (hR.trans ((exp_lt_exp.mpr (by linarith only [hq])).trans G.right_entry)).trans
      (mul_lt_mul_of_pos_left hd.2 hRR)
  have hg (r : ℝ) (hr : r ∈ Icc l h) :
      G.profile =ᶠ[𝓝 r] centralRadialProfile 1 := G.central_profile_germ hq hr
  have hneg : NegativeRadialComponent E l h := by
    refine ⟨hal, hlh, hhb, ?_, ?_, ?_⟩
    · change deriv G.profile l = 0
      rw [(hg l (left_mem_Icc.mpr hlh.le)).deriv_eq]
      exact (centralRadialProfile_critical_iff (by norm_num) (centralRadius_pos _)).mpr
        (Or.inl rfl)
    · change deriv G.profile h = 0
      rw [(hg h (right_mem_Icc.mpr hlh.le)).deriv_eq]
      exact (centralRadialProfile_critical_iff (by norm_num) (centralRadius_pos _)).mpr
        (Or.inr rfl)
    · intro r hr
      change deriv G.profile r < 0
      rw [(hg r (Ioo_subset_Icc_self hr)).deriv_eq]
      have himage := contDiff_centralRadius.continuous.image_Ioo_of_strictMono
        strictMono_centralRadius (a := -sqrt centralOscillatorA) (b := sqrt centralOscillatorA)
      have hrim : r ∈ centralRadius '' Ioo (-sqrt centralOscillatorA) (sqrt centralOscillatorA) := by
        rw [himage]
        exact hr
      obtain ⟨x, hx, rfl⟩ := hrim
      exact (centralRadialProfile_deriv_neg_iff (by norm_num) x).mpr (sq_lt.mpr hx)
  refine ⟨hneg, ?_⟩
  calc
    radialTravel E l h =
        (∫ r in l..h, sqrt (-(deriv (centralRadialProfile 1) r) /
          (r * centralRadialProfile 1 r))) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Icc l h := by simpa only [uIcc_of_le hlh.le] using hr
      change sqrt (-(deriv G.profile r) / (r * G.profile r)) = _
      rw [(hg r hr').deriv_eq, (hg r hr').eq_of_nhds]
    _ = Real.pi / (2 * sqrt 2) := central_radialTravel_integral (by norm_num)

end ContinuousFlexibility.Radial
