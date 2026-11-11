import ContinuousFlexibility.Analysis.RootCharacteristicFactor
import ContinuousFlexibility.Analysis.N01ProfileRootCollar
import ContinuousFlexibility.Analysis.StateControlCofiniteClosure
import ContinuousFlexibility.Analysis.MaterialHeightRegularity

/-!
# A common actual characteristic-factor strip at each reference root

The radial collar is selected before the state. On it every actual profile
equals the reference profile. A genuine smooth division of the reference
derivative and the numerical N01 bounds then give positive smooth factored
speeds, uniformly for every angle and every sector state in the same U.

The radius depends on the root. No uniform radius over components, and no
common germ for an arbitrary corrected N03 operator, is asserted here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem contDiff_stateRadialHeight_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) :
    ContDiff ℝ ∞ (stateRadialHeight D S C x) := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN x
  have hd (r : ℝ) : HasDerivAt (stateRadialHeight D S C x)
      (stateProfile D S C x r) r :=
    (hw.continuous.integral_hasStrictDerivAt D.b r).hasDerivAt
  have he : deriv (stateRadialHeight D S C x) = stateProfile D S C x :=
    funext fun r => (hd r).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun r => (hd r).differentiableAt, ?_⟩
  rwa [he]

theorem contDiff_stateHeight_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (z : AnnularState S × ℝ) :
    ContDiff ℝ ∞ (stateHeight D S C z) :=
  ((contDiff_stateRadialHeight_of_n01 hS hT hN z.1).comp contDiff_fst).add
    (contDiff_const.mul
      (physical_height_with_cutoff_contDiff hT hS (by norm_num : (0 : ℝ) < 3 / 4)
        z.1.1.1 z.1.1.2))

/-- Every state is admitted in the profile identity. The smoothness and
numerical field bounds concern the original common sector neighborhood. -/
theorem n01_exists_common_characteristic_root_strip
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {r σ : ℝ} (hr : r ∈ Ioo D.a D.b)
    (hzero : deriv D.w r = 0) (hsign : σ * deriv (deriv D.w) r < 0) :
    ∃ (g : ℝ → ℝ) (δ : ℝ), ContDiff ℝ ∞ g ∧ 0 < g 0 ∧ 0 < δ ∧
      (∀ t : ℝ, -deriv D.w (r + σ * t) = t * g t) ∧
      (∀ t ∈ Ioo (-δ) δ, r + σ * t ∈ Ioo D.a D.b ∧ 0 < g t ∧
        ∀ x : AnnularState S, stateProfile D S C x (r + σ * t) = D.w (r + σ * t)) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ContDiffOn ℝ ∞
          (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
            (stateHeight D S C z) r σ) (Ioo (-δ) δ ×ˢ univ) ∧
        ContDiffOn ℝ ∞
          (orientedCharacteristicDrift (stateProfile D S C z.1)
            (stateHeight D S C z) r σ) (Ioo (-δ) δ ×ˢ univ) ∧
        ∀ p ∈ Ioo (-δ) δ ×ˢ univ,
          0 < factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
            (stateHeight D S C z) r σ p ∧
          referenceRootSpeedFactor D.w g r σ 0 / 4 ≤
            factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
              (stateHeight D S C z) r σ p ∧
          factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
              (stateHeight D S C z) r σ p ≤
            4 * referenceRootSpeedFactor D.w g r σ 0 ∧
          (0 ≤ p.1 →
            characteristicSpeed (stateProfile D S C z.1) (stateHeight D S C z)
                (rootProfileShift r σ p) =
              Real.sqrt p.1 *
                factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
                  (stateHeight D S C z) r σ p) := by
  obtain ⟨_, hD⟩ := hN.1.1
  have ha : 0 < D.a := hD.1.1
  have hwref : ContDiff ℝ ∞ D.w := hD.1.2.2.1.1
  have hwpos : ∀ s ∈ Ioo D.a D.b, 0 < D.w s := hD.1.2.2.2.2.1
  obtain ⟨ρ, hρ, hprofile⟩ := n01_exists_common_profile_root_collar hS hN hr hzero
  have hwd : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hwref).2
  have hshift : ContDiff ℝ ∞ (fun t : ℝ => r + σ * t) :=
    contDiff_const.add (contDiff_const.mul contDiff_id)
  let f : ℝ → ℝ := fun t => -deriv D.w (r + σ * t)
  have hf : ContDiff ℝ ∞ f := (hwd.comp hshift).neg
  have hfzero : f 0 = 0 := by simp only [f, mul_zero, add_zero, hzero, neg_zero]
  obtain ⟨g, hg, hgzero, hdivide⟩ := exists_smooth_division_at_zero hf hfzero
  have hfderiv : HasDerivAt f (-(deriv (deriv D.w) r * σ)) 0 := by
    have ho : HasDerivAt (deriv D.w) (deriv (deriv D.w) r) (r + σ * 0) := by
      simpa only [mul_zero, add_zero] using (hwd.differentiable (by simp) r).hasDerivAt
    have hd := (ho.comp 0 (((hasDerivAt_id 0).const_mul σ).const_add r)).fun_neg
    simpa only [Function.comp_def, id_eq, f, mul_zero, add_zero, mul_one] using hd
  have hgpos : 0 < g 0 := by
    rw [hgzero, hfderiv.deriv]
    nlinarith only [hsign]
  have hr0 : 0 < r + σ * 0 := by
    simpa only [mul_zero, add_zero] using ha.trans hr.1
  have hw0 : 0 < D.w (r + σ * 0) := by
    simpa only [mul_zero, add_zero] using hwpos r hr
  have hc0 : 0 < referenceRootSpeedFactor D.w g r σ 0 :=
    referenceRootSpeedFactor_pos hr0 hw0 hgpos
  have hccont : ContinuousAt (referenceRootSpeedFactor D.w g r σ) 0 :=
    (contDiffAt_referenceRootSpeedFactor hwref hg hr0 hw0 hgpos).continuousAt
  have hshift0 : ContinuousAt (fun t : ℝ => r + σ * t) 0 := hshift.continuous.continuousAt
  have hphys : ∀ᶠ t in 𝓝 (0 : ℝ), r + σ * t ∈ Ioo D.a D.b :=
    hshift0.tendsto.eventually (by
      change Ioo D.a D.b ∈ 𝓝 (r + σ * 0)
      simpa only [mul_zero, add_zero] using isOpen_Ioo.mem_nhds hr)
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), |r + σ * t - r| < ρ := by
    have hh := hshift0.tendsto.eventually
      (show Metric.ball r ρ ∈ 𝓝 (r + σ * 0) by
        simpa only [mul_zero, add_zero] using Metric.ball_mem_nhds r hρ)
    simpa only [Metric.mem_ball, Real.dist_eq] using hh
  have hgnear : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < g t :=
    (hg.continuous.continuousAt : ContinuousAt g 0).tendsto.eventually (Ioi_mem_nhds hgpos)
  have hcl : ∀ᶠ t in 𝓝 (0 : ℝ),
      referenceRootSpeedFactor D.w g r σ 0 / 2 < referenceRootSpeedFactor D.w g r σ t :=
    hccont.tendsto.eventually (Ioi_mem_nhds (half_lt_self hc0))
  have hcu : ∀ᶠ t in 𝓝 (0 : ℝ),
      referenceRootSpeedFactor D.w g r σ t < 2 * referenceRootSpeedFactor D.w g r σ 0 :=
    hccont.tendsto.eventually (Iio_mem_nhds (by linarith only [hc0]))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hphys.and (hnear.and (hgnear.and (hcl.and hcu))))
  have hdata (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :=
    hball (show t ∈ Metric.ball (0 : ℝ) δ by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using ht)
  refine ⟨g, δ, hg, hgpos, hδ, hdivide, ?_, ?_⟩
  · intro t ht
    have hd := hdata t ht
    exact ⟨hd.1, hd.2.2.1, fun x => hprofile _ hd.2.1 x⟩
  · intro z hz hsector
    have hw := contDiff_stateProfile_of_n01 hS hT hN z.1
    have hZ := contDiff_stateHeight_of_n01 hS hT hN z
    have hpoint (p : PolarPoint) (hp : p ∈ Ioo (-δ) δ ×ˢ univ) :
        ContDiffAt ℝ ∞
            (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
              (stateHeight D S C z) r σ) p ∧
          ContDiffAt ℝ ∞
            (orientedCharacteristicDrift (stateProfile D S C z.1)
              (stateHeight D S C z) r σ) p ∧
          0 < factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
            (stateHeight D S C z) r σ p ∧
          referenceRootSpeedFactor D.w g r σ 0 / 4 ≤
            factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
              (stateHeight D S C z) r σ p ∧
          factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
              (stateHeight D S C z) r σ p ≤
            4 * referenceRootSpeedFactor D.w g r σ 0 ∧
          (0 ≤ p.1 →
            characteristicSpeed (stateProfile D S C z.1) (stateHeight D S C z)
                (rootProfileShift r σ p) =
              Real.sqrt p.1 *
                factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
                  (stateHeight D S C z) r σ p) := by
      have hc := hdata p.1 hp.1
      have hmem : rootProfileShift r σ p ∈ annularOpen D := ⟨hc.1, mem_univ _⟩
      have hrp : 0 < (rootProfileShift r σ p).1 := ha.trans hc.1.1
      have hwp : 0 < D.w (rootProfileShift r σ p).1 := hwpos _ hc.1
      have hweq : stateProfile D S C z.1 (rootProfileShift r σ p).1 =
          D.w (rootProfileShift r σ p).1 := hprofile _ hc.2.1 z.1
      let Q := heightQ (profileEnergy (stateProfile D S C z.1) (rootProfileShift r σ p))
        (heightRadial (stateHeight D S C z) (rootProfileShift r σ p))
        (angularPartial (heightAngular (stateHeight D S C z)) (rootProfileShift r σ p))
      have hlow := (hN.2.2.2.2.2.2.2.2.2.1 z hz hsector (rootProfileShift r σ p) hmem).2.2
      have hratio : Q / stateProfile D S C z.1 (rootProfileShift r σ p).1 =
          Q / D.w (rootProfileShift r σ p).1 :=
        congrArg (fun a : ℝ => Q / a) hweq
      have hQl : (7 / 8 : ℝ) ≤ Q / D.w (rootProfileShift r σ p).1 :=
        hlow.1.trans_eq hratio
      have hQu : Q / D.w (rootProfileShift r σ p).1 ≤ (9 / 8 : ℝ) :=
        hratio.symm.trans_le hlow.2.1
      have hQpos : 0 < Q :=
        (mul_pos (by norm_num : (0 : ℝ) < 7 / 8) hwp).trans_le ((le_div_iff₀ hwp).mp hQl)
      have hDpos : 0 < polarDiscriminant (stateProfile D S C z.1)
          (stateHeight D S C z) (rootProfileShift r σ p) :=
        (by norm_num : (0 : ℝ) < 1 / 2).trans_le hlow.2.2.1
      have hs := contDiffAt_factoredCharacteristicField hwref hg hw hZ
        hrp hwp hc.2.2.1 hDpos hQpos
      have hb := factoredCharacteristicSpeed_reference_bounds
        hrp hwp hc.2.2.1 hQl hQu hlow.2.2.1 hlow.2.2.2
      refine ⟨hs.1, hs.2, factoredCharacteristicSpeed_pos
        hrp hwp hc.2.2.1 hDpos hQpos, ?_, ?_, ?_⟩
      · nlinarith only [hb.1, hc.2.2.2.1]
      · nlinarith only [hb.2, hc.2.2.2.2]
      · intro hx
        have hpeq : stateProfile D S C z.1 =ᶠ[𝓝 (rootProfileShift r σ p).1] D.w := by
          have hbin : (rootProfileShift r σ p).1 ∈ Metric.ball r ρ := by
            simpa only [Metric.mem_ball, Real.dist_eq, rootProfileShift] using hc.2.1
          filter_upwards [Metric.isOpen_ball.mem_nhds hbin] with y hy
          exact hprofile y (by simpa only [Metric.mem_ball, Real.dist_eq] using hy) z.1
        have hd : -deriv (stateProfile D S C z.1) (rootProfileShift r σ p).1 =
            p.1 * g p.1 := by
          rw [hpeq.deriv_eq]
          exact hdivide p.1
        exact characteristicSpeed_eq_sqrt_mul_factored (stateHeight D S C z) hx hweq hd
    exact ⟨fun p hp => (hpoint p hp).1.contDiffWithinAt,
      fun p hp => (hpoint p hp).2.1.contDiffWithinAt,
      fun p hp => (hpoint p hp).2.2⟩

end ContinuousFlexibility.Analysis
