module

public import ContinuousFlexibility.Analysis.WeakBranchCore

/-!
# An annular core from one nonzero solution

The geometric construction needs one scalar-equation solution, with its height
normalization and the uniform discriminant bound on the same state. It does
not require a family of solutions or parameter derivatives. The two global
smoothness premises concern the actual profile and decoded height at that
state; endpoint constants and nonradiality are then constructed from them.

This is the pointwise form of the construction in `WeakBranchCore`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem contDiff_right_primitive {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (b : ℝ) :
    ContDiff ℝ ∞ (fun r => ∫ t in b..r, w t) := by
  have hderiv (r : ℝ) : HasDerivAt (fun s => ∫ t in b..s, w t) (w r) r :=
    intervalIntegral.integral_hasDerivAt_right (hw.continuous.intervalIntegrable b r)
      hw.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuous.continuousAt
  have hd : deriv (fun r => ∫ t in b..r, w t) = w := funext fun r => (hderiv r).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun r => (hderiv r).differentiableAt, ?_⟩
  rwa [hd]

private theorem integral_zero_of_eq_zero_on_interval
    {w : ℝ → ℝ} {a b : ℝ} (h : ∀ t ∈ uIcc a b, w t = 0) :
    (∫ t in a..b, w t) = 0 :=
  (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) h).trans
    intervalIntegral.integral_zero

private theorem continuousAt_polar_discriminant_numerator {w : ℝ → ℝ}
    {z : PolarPoint → ℝ} {p : PolarPoint} (hw : ContDiff ℝ ∞ w)
    (hz : ContDiff ℝ ∞ z) (hr : p.1 ≠ 0) :
    ContinuousAt (polarDiscriminant w z) p ∧
      ContinuousAt (polarCurvatureNumerator w z) p := by
  have he : ContDiff ℝ ∞ (profileEnergy w) := contDiff_const.add ((hw.comp contDiff_fst).pow 2)
  have hk := contDiffAt_heightRadial (x := p) hz.contDiffAt (m := 1) (by simp)
  have hp := contDiffAt_heightAngular (x := p) hz.contDiffAt (m := 1) (by simp) hr
  have her := (contDiffAt_radialPartial (x := p) he.contDiffAt (m := 0) (by simp)).continuousAt
  have hkr := (contDiffAt_radialPartial hk (m := 0) (by norm_num)).continuousAt
  have hpr := (contDiffAt_radialPartial hp (m := 0) (by norm_num)).continuousAt
  have hpt := (contDiffAt_angularPartial hp (m := 0) (by norm_num)).continuousAt
  have hec : ContinuousAt (profileEnergy w) p := he.continuous.continuousAt
  have hkc := hk.continuousAt
  have hpc := hp.continuousAt
  have hc : ContinuousAt (fun y => 1 - heightAngular z y ^ 2) p :=
    continuousAt_const.sub (hpc.pow 2)
  constructor
  · exact (hec.mul hc).sub (hkc.pow 2)
  · exact (((hkc.add (hec.mul hpt)).mul hkr).sub
      ((hec.mul continuous_fst.continuousAt).mul (hpr.pow 2))).sub
      ((her.div_const 2).mul (hc.add (hkc.mul hpt)))

private theorem continuousAt_polar_residual {w : ℝ → ℝ} {z : PolarPoint → ℝ}
    {p : PolarPoint} (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) (hr : p.1 ≠ 0)
    (hpos : 0 < polarDiscriminant w z p) :
    ContinuousAt (polarCoordinateResidual w z) p := by
  obtain ⟨hd, hn⟩ := continuousAt_polar_discriminant_numerator hw hz hr
  have hi : ContinuousAt (fun y => inverseDThreeHalves (polarDiscriminant w z y)) p :=
    continuousAt_const.div₀ (hd.mul hd.sqrt)
      (mul_ne_zero hpos.ne' (Real.sqrt_pos.mpr hpos).ne')
  exact (hn.mul hi).div₀ continuous_fst.continuousAt hr

private theorem n01_discriminant_lower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (1 / 2 : ℝ) ≤ polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hbounds, _⟩ := hN
  exact (hbounds z hz hsector p hp).2.2.2.2.1

/-- A normalized scalar-equation solution at one nonzero parameter yields an
actual annular core once the profile and decoded height are globally smooth.
No return-equation or smooth-branch hypothesis enters the geometric construction. -/
theorem nonempty_flatAnnularCore_of_point_smooth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hS : IsPhysicalSpaces D T S)
    {x : AnnularState S} {q : ℝ} (hq₀ : q ≠ 0)
    (hnear : (x, q) ∈ stateNeighborhood S C base ε) (hsector : stateSector S x)
    (hrow : referenceRow D (stateU S x) = 1)
    (hscalar : ∀ p ∈ annularOpen D, scalarResidualField D S C (x, q) p = 0)
    (hw : ContDiff ℝ ∞ (stateProfile D S C x))
    (hdecode : ContDiff ℝ ∞ ((S.height (3 / 4 : ℝ)).decode x.1.1)) :
    Nonempty FlatAnnularCore := by
  let w := stateProfile D S C x
  let z := stateHeight D S C (x, q)
  let h := stateRadialHeight D S C x
  obtain ⟨_, hpgeom⟩ := hN.1.1
  obtain ⟨ha, hab, ⟨_, hwref⟩, _, hwpos, _, _⟩ := hpgeom.1
  obtain ⟨hχ, ⟨δ, hδ, _, hχleft, hχright⟩, _⟩ := hS.2.2.1
  have hmember := (hS.1 (3 / 4 : ℝ)).2.2.2.1 x.1.1
  have hwzero : ∀ r, r ≤ D.a ∨ D.b ≤ r → w r = 0 := by
    intro r hr
    unfold w stateProfile
    rw [hwref r hr, zero_mul]
  have hleft (r : ℝ) (hr : r ≤ D.a) : h r = h D.a := by
    have hzint : (∫ t in D.a..r, w t) = 0 :=
      integral_zero_of_eq_zero_on_interval fun t ht => by
        rw [uIcc_of_ge hr] at ht
        exact hwzero t (Or.inl ht.2)
    have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hw.continuous.intervalIntegrable D.b D.a) (hw.continuous.intervalIntegrable D.a r)
    change (∫ t in D.b..r, w t) = ∫ t in D.b..D.a, w t
    rw [← hsum, hzint, add_zero]
  have hright (r : ℝ) (hr : D.b ≤ r) : h r = 0 :=
    integral_zero_of_eq_zero_on_interval fun t ht => by
      rw [uIcc_of_le hr] at ht
      exact hwzero t (Or.inr ht.1)
  have hz : ContDiff ℝ ∞ z :=
    ((contDiff_right_primitive hw D.b).comp contDiff_fst).add
      (contDiff_const.mul (hdecode.add (contDiff_const.mul (hχ.comp contDiff_fst))))
  have hclosure {r θ : ℝ} (hr : r ∈ Icc D.a D.b) :
      (r, θ) ∈ closure (annularOpen D) := by
    rw [annularOpen, closure_prod_eq, closure_Ioo hab.ne, closure_univ]
    exact ⟨hr, mem_univ θ⟩
  have hDopen : ∀ p ∈ annularOpen D, (1 / 2 : ℝ) ≤ polarDiscriminant w z p :=
    fun _ hp => n01_discriminant_lower hN hnear hsector hp
  have hDclosed (r : ℝ) (hr : r ∈ Icc D.a D.b) (θ : ℝ) :
      0 < polarDiscriminant w z (r, θ) := by
    have hcont := (continuousAt_polar_discriminant_numerator (p := (r, θ))
      hw hz (ha.trans_le hr.1).ne').1
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      (ContinuousWithinAt.closure_le (hclosure (θ := θ) hr)
        continuousAt_const.continuousWithinAt hcont.continuousWithinAt hDopen)
  have hresOpen : MapsTo (polarCoordinateResidual w z) (annularOpen D) ({0} : Set ℝ) := by
    intro p hp
    have hr : p.1 ≠ 0 := (ha.trans hp.1.1).ne'
    exact mem_singleton_iff.mpr
      (polarCoordinateResidual_eq_zero_of_scalarResidualField hq₀ hr (hscalar p hp))
  refine ⟨{
    a := D.a
    b := D.b
    a_pos := ha
    a_lt_b := hab
    w := w
    z := z
    cLeft := h D.a + q * x.1.2
    cRight := 0
    smooth_w := hw
    smooth_z := hz
    w_pos := fun r hr => mul_pos (hwpos r hr) (Real.exp_pos _)
    w_zero := hwzero
    z_left := ?_
    z_right := ?_
    half_turn := ?_
    even := ?_
    discriminant_pos := hDclosed
    residual_zero := ?_
    nonradial := stateHeight_nonradial_of_referenceRow hab.le hq₀ hrow }⟩
  · intro r hr θ
    have hp : (r, θ) ∉ annularOpen D := fun hp => (not_lt_of_ge hr) hp.1.1
    have hd := hmember.2.2.2.1 (r, θ) hp
    change h r + q * (((S.height (3 / 4 : ℝ)).decode x.1.1) (r, θ) +
      x.1.2 * S.chiLeft r) = _
    simp only [hleft r hr, hd, hχleft r (by linarith), mul_one, zero_add]
  · intro r hr θ
    have hp : (r, θ) ∉ annularOpen D := fun hp => (not_lt_of_ge hr) hp.1.2
    have hd := hmember.2.2.2.1 (r, θ) hp
    change h r + q * (((S.height (3 / 4 : ℝ)).decode x.1.1) (r, θ) +
      x.1.2 * S.chiLeft r) = 0
    simp only [hright r hr, hd, hχright r (by linarith), mul_zero, add_zero]
  · intro p
    have hp : (p + ((0, Real.pi) : PolarPoint)).1 = p.1 := by simp
    simp only [z, stateHeight, stateU, heightPairField, hp, hmember.2.2.1 p]
  · intro r θ
    simp only [z, stateHeight, stateU, heightPairField, hmember.2.1 r θ]
  · intro r hr θ
    have hc := continuousAt_polar_residual hw hz (ha.trans_le hr.1).ne' (hDclosed r hr θ)
    simpa only [closure_singleton, mem_singleton_iff] using
      hc.continuousWithinAt.mem_closure (hclosure (θ := θ) hr) hresOpen

end ContinuousFlexibility.Statements
