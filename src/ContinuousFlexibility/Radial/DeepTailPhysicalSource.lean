module

public import ContinuousFlexibility.Statements.Radial
public import ContinuousFlexibility.Radial.Gauge
public import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
# The physical source identity on both deep tails

The outward coordinate is `r = exp (s * x)`, where `s * s = 1`.
Thus the left and right tails are specializations of the same derivative
calculation.  The normalization at the physical endpoint is included in
both the gauge and the density, including the exact nonhomogeneous factor.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff

private theorem radialJacobi_congr_germ {a r : ℝ} {w u v : ℝ → ℝ}
    (h : u =ᶠ[𝓝 r] v) : radialJacobi a w u r = radialJacobi a w v r := by
  have hf : (fun t => w t * deriv u t) =ᶠ[𝓝 r] (fun t => w t * deriv v t) := by
    filter_upwards [h.deriv] with t ht
    rw [ht]
  unfold radialJacobi
  rw [hf.deriv_eq, h.eq_of_nhds]

/-- The divided logarithmic gauge formula only requires two derivatives at
the logarithmic point, rather than global smoothness of the gauged height. -/
theorem radialJacobi_gauge_divided_at {a r : ℝ} {w V : ℝ → ℝ}
    (hr : 0 < r) (hw : DifferentiableAt ℝ w r) (hw₀ : w r ≠ 0)
    (hV : ContDiffAt ℝ 2 V (log r)) :
    radialJacobi a w (gaugeLift a V) r =
      w r * r ^ (a - 2) *
        (deriv (deriv V) (log r) +
          (r * deriv w r / w r + 2 * a - 1) * deriv V (log r) +
          a * (a - 1) * V (log r)) := by
  have hV₁ : DifferentiableAt ℝ (deriv V) (log r) :=
    (hV.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd := hasDerivAt_gaugeFirst (a := a) hr
    (hV.differentiableAt (by norm_num)).hasDerivAt hV₁.hasDerivAt
  have hf := hw.hasDerivAt.mul hd
  have heq : (fun t => w t * deriv (gaugeLift a V) t) =ᶠ[𝓝 r]
      (fun t => w t * gaugeFirst a V (deriv V) t) := by
    have hlog := (Real.continuousAt_log hr.ne').tendsto
    filter_upwards [eventually_gt_nhds hr,
      hlog.eventually (hV.eventually (by norm_num))] with t ht hVt
    rw [deriv_gaugeLift ht (hVt.differentiableAt (by norm_num))]
  have hactual := hf.congr_of_eventuallyEq heq
  unfold radialJacobi
  rw [hactual.deriv]
  unfold gaugeFirst gaugeLift
  simp only [Real.rpow_sub hr a 1, Real.rpow_sub hr a 2,
    Real.rpow_one, Real.rpow_two]
  field_simp [hr.ne', hw₀]
  ring

/-- Reflection and a constant gauge normalization in the exact source formula
at a point where the logarithmic height is twice continuously differentiable. -/
theorem radialJacobi_signed_gauge_source_at {a s c x : ℝ} {w V : ℝ → ℝ}
    (hs : s * s = 1) (hc : c ≠ 0)
    (hw : DifferentiableAt ℝ w (exp (s * x))) (hw₀ : w (exp (s * x)) ≠ 0)
    (hV : ContDiffAt ℝ 2 V x) :
    radialJacobi a w (gaugeLift a (fun y => c * V (s * y))) (exp (s * x)) =
      -(c * (exp (s * x)) ^ a * w (exp (s * x)) / (exp (s * x)) ^ 2) *
        (-(c ^ 2 * logGaugeWeight a w (s * x))⁻¹ *
          deriv (fun y => c ^ 2 * logGaugeWeight a w (s * y) * deriv V y) x -
          a * (a - 1) * V x) := by
  let W : ℝ → ℝ := fun y => c * V (s * y)
  have hsx : s * (s * x) = x := by rw [← mul_assoc, hs, one_mul]
  have hVs : ContDiffAt ℝ 2 V (s * (s * x)) := by simpa only [hsx] using hV
  have hW : ContDiffAt ℝ 2 W (s * x) :=
    contDiffAt_const.mul (hVs.comp (s * x) (contDiffAt_const.mul contDiffAt_id))
  have hWlog : ContDiffAt ℝ 2 W (log (exp (s * x))) := by
    simpa only [Real.log_exp] using hW
  have hV₁ : DifferentiableAt ℝ (deriv V) x :=
    (hV.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdW : deriv W = fun y => (c * s) * deriv V (s * y) := by
    funext y
    dsimp only [W]
    rw [deriv_const_mul_field, deriv_comp_mul_left]
    simp only [smul_eq_mul]
    ring
  have hddW : deriv (deriv W) (s * x) = c * deriv (deriv V) x := by
    rw [hdW, deriv_const_mul_field, deriv_comp_mul_left]
    simp only [smul_eq_mul, hsx]
    calc
      (c * s) * (s * deriv (deriv V) x) =
          c * (s * s) * deriv (deriv V) x := by ring
      _ = c * deriv (deriv V) x := by rw [hs, mul_one]
  have hwexp := hw.hasDerivAt.comp x (((hasDerivAt_id x).const_mul s).exp)
  have hexp := (((hasDerivAt_id x).const_mul s).const_mul (2 * a - 1)).exp
  have hf := ((hwexp.mul hexp).const_mul (c ^ 2)).mul hV₁.hasDerivAt
  change HasDerivAt
    (fun y => c ^ 2 * logGaugeWeight a w (s * y) * deriv V y) _ x at hf
  change radialJacobi a w (gaugeLift a W) (exp (s * x)) = _
  rw [radialJacobi_gauge_divided_at (exp_pos _) hw hw₀ hWlog]
  simp only [Real.log_exp]
  rw [hddW, hdW]
  simp only [W, hsx]
  rw [Real.rpow_sub (exp_pos _) a 2, Real.rpow_two, hf.deriv]
  unfold logGaugeWeight
  simp only [Function.comp_apply, Pi.mul_apply, id_eq, mul_one]
  field_simp [hc, hw₀, Real.exp_ne_zero] <;> ring

/-- The globally smooth specialization of the local reflected gauge identity. -/
theorem radialJacobi_signed_gauge_source {a s c x : ℝ} {w V : ℝ → ℝ}
    (hs : s * s = 1) (hc : c ≠ 0)
    (hw : DifferentiableAt ℝ w (exp (s * x))) (hw₀ : w (exp (s * x)) ≠ 0)
    (hV : ContDiff ℝ ∞ V) :
    radialJacobi a w (gaugeLift a (fun y => c * V (s * y))) (exp (s * x)) =
      -(c * (exp (s * x)) ^ a * w (exp (s * x)) / (exp (s * x)) ^ 2) *
        (-(c ^ 2 * logGaugeWeight a w (s * x))⁻¹ *
          deriv (fun y => c ^ 2 * logGaugeWeight a w (s * y) * deriv V y) x -
          a * (a - 1) * V x) :=
  radialJacobi_signed_gauge_source_at hs hc hw hw₀ (hV.contDiffAt.of_le (by simp))

/-- The normalized physical density is a constant multiple of the log-gauge
density, with the same identity for either orientation. -/
theorem normalizedPhysicalWeight_eq {R : ℝ} (hR : 0 < R)
    (a s x : ℝ) (w : ℝ → ℝ) :
    (exp (s * x) / R) ^ (2 * a) * w (exp (s * x)) / exp (s * x) =
      ((R ^ a)⁻¹) ^ 2 * logGaugeWeight a w (s * x) := by
  have hRpow : R ^ (2 * a) = (R ^ a) ^ (2 : ℕ) := by
    rw [mul_comm 2 a, Real.rpow_mul hR.le, Real.rpow_two]
  have he : exp ((2 * a - 1) * (s * x)) =
      exp ((s * x) * (2 * a)) / exp (s * x) := by
    rw [show (2 * a - 1) * (s * x) = (s * x) * (2 * a) - s * x by ring,
      Real.exp_sub]
  unfold logGaugeWeight
  rw [Real.div_rpow (exp_pos _).le hR.le, hRpow,
    Real.rpow_def_of_pos (exp_pos _), Real.log_exp, he]
  field_simp [(Real.rpow_pos_of_pos hR a).ne', Real.exp_ne_zero]

private theorem gaugeLift_germ_of_signed_relation {a s R l h x : ℝ}
    {u V : ℝ → ℝ} (hs : s * s = 1) (hR : 0 < R) (hx : x ∈ Ioo l h)
    (hu : ∀ y ∈ Ioo l h,
      u (exp (s * y)) = (exp (s * y) / R) ^ a * V y) :
    u =ᶠ[𝓝 (exp (s * x))] gaugeLift a (fun y => (R ^ a)⁻¹ * V (s * y)) := by
  have hsx : s * (s * x) = x := by rw [← mul_assoc, hs, one_mul]
  have hcont : ContinuousAt (fun r : ℝ => s * log r) (exp (s * x)) :=
    continuousAt_const.mul (Real.continuousAt_log (Real.exp_ne_zero (s * x)))
  have hlog : Tendsto (fun r : ℝ => s * log r) (𝓝 (exp (s * x))) (𝓝 x) := by
    simpa only [Real.log_exp, hsx] using hcont.tendsto
  filter_upwards [eventually_gt_nhds (exp_pos (s * x)),
    hlog.eventually (Ioo_mem_nhds hx.1 hx.2)] with r hr hmem
  have hinv : exp (s * (s * log r)) = r := by
    rw [← mul_assoc, hs, one_mul, Real.exp_log hr]
  have heq := hu (s * log r) hmem
  rw [hinv] at heq
  rw [heq, gaugeLift, Real.div_rpow hr.le hR.le]
  ring

/-- The source identity is local in the coefficient and in the gauge relation.
No tail estimates enter this calculation. -/
theorem radialJacobi_signed_physical_source_at {a s R l h x : ℝ}
    {w p u V : ℝ → ℝ} (hs : s * s = 1) (hR : 0 < R) (hx : x ∈ Ioo l h)
    (hw : DifferentiableAt ℝ w (exp (s * x))) (hw₀ : w (exp (s * x)) ≠ 0)
    (hV : ContDiffAt ℝ 2 V x)
    (hp : ∀ y ∈ Ioo l h,
      p y = (exp (s * y) / R) ^ (2 * a) * w (exp (s * y)) / exp (s * y))
    (hu : ∀ y ∈ Ioo l h,
      u (exp (s * y)) = (exp (s * y) / R) ^ a * V y) :
    radialJacobi a w u (exp (s * x)) =
      -((exp (s * x) / R) ^ a * w (exp (s * x)) / (exp (s * x)) ^ 2) *
        (-(p x)⁻¹ * deriv (fun y => p y * deriv V y) x - a * (a - 1) * V x) := by
  have hp' : p =ᶠ[𝓝 x]
      (fun y => ((R ^ a)⁻¹) ^ 2 * logGaugeWeight a w (s * y)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    rw [hp y hy, normalizedPhysicalWeight_eq hR]
  have hpderiv : (fun y => p y * deriv V y) =ᶠ[𝓝 x]
      (fun y => ((R ^ a)⁻¹) ^ 2 * logGaugeWeight a w (s * y) * deriv V y) := by
    filter_upwards [hp'] with y hy
    rw [hy]
  rw [radialJacobi_congr_germ (gaugeLift_germ_of_signed_relation hs hR hx hu),
    hp'.eq_of_nhds, hpderiv.deriv_eq]
  have hsource := radialJacobi_signed_gauge_source_at (a := a) hs
    (inv_ne_zero (Real.rpow_pos_of_pos hR a).ne') hw hw₀ hV
  rw [Real.div_rpow (exp_pos (s * x)).le hR.le a]
  simpa only [div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using hsource

/-- The local source identity applied to a globally smooth logarithmic height. -/
theorem radialJacobi_signed_physical_source {a s R l h x : ℝ}
    {w p u V : ℝ → ℝ} (hs : s * s = 1) (hR : 0 < R) (hx : x ∈ Ioo l h)
    (hw : DifferentiableAt ℝ w (exp (s * x))) (hw₀ : w (exp (s * x)) ≠ 0)
    (hV : ContDiff ℝ ∞ V)
    (hp : ∀ y ∈ Ioo l h,
      p y = (exp (s * y) / R) ^ (2 * a) * w (exp (s * y)) / exp (s * y))
    (hu : ∀ y ∈ Ioo l h,
      u (exp (s * y)) = (exp (s * y) / R) ^ a * V y) :
    radialJacobi a w u (exp (s * x)) =
      -((exp (s * x) / R) ^ a * w (exp (s * x)) / (exp (s * x)) ^ 2) *
        (-(p x)⁻¹ * deriv (fun y => p y * deriv V y) x - a * (a - 1) * V x) :=
  radialJacobi_signed_physical_source_at hs hR hx hw hw₀
    (hV.contDiffAt.of_le (by simp)) hp hu

end ContinuousFlexibility.Radial

namespace ContinuousFlexibility.Statements

open Set Filter Real
open scoped Topology ContDiff

/-- The physical source formula at an interior point requires only local
second-order regularity of the logarithmic solution. -/
theorem tailPhysicalSourceIdentity_at_of_relation {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} {V u : ℝ → ℝ} {x : ℝ}
    (hD : IsAccumulatingProfile D) (hrel : TailPhysicalRelation D T right j start)
    (hV : ContDiffAt ℝ 2 V x)
    (hUV : ∀ y ∈ Ioo T.entrance T.endpoint,
      u (tailPhysicalRadius right y) =
        (tailPhysicalRadius right y / (if right then D.b else D.a)) ^ ((j : ℝ) ^ 2) * V y)
    (hx : x ∈ Ioo T.entrance T.endpoint) :
    Radial.radialJacobi ((j : ℝ) ^ 2) D.w u (tailPhysicalRadius right x) =
      -((tailPhysicalRadius right x / (if right then D.b else D.a)) ^ ((j : ℝ) ^ 2) *
        D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x ^ 2) *
      (-(T.p x)⁻¹ * deriv (fun y => T.p y * deriv V y) x - T.Λ * V x) := by
  obtain ⟨C, hC⟩ := hD
  rcases hC.1 with ⟨ha, hab, hw, _, hwpos, _⟩
  let s : ℝ := if right then 1 else -1
  let R : ℝ := if right then D.b else D.a
  have hs : s * s = 1 := by cases right <;> norm_num [s]
  have hR : 0 < R := by
    cases right
    · exact ha
    · exact ha.trans hab
  have hradius : tailPhysicalRadius right = fun y => exp (s * y) := by
    funext y
    cases right <;> simp [tailPhysicalRadius, s]
  have hw₀ : D.w (exp (s * x)) ≠ 0 := by
    apply ne_of_gt (hwpos _ ?_)
    simpa only [hradius] using (hrel.2.2.1 x hx).1
  have hp : ∀ y ∈ Ioo T.entrance T.endpoint,
      T.p y = (exp (s * y) / R) ^ (2 * (j : ℝ) ^ 2) *
        D.w (exp (s * y)) / exp (s * y) := by
    intro y hy
    simpa only [hradius, R] using (hrel.2.2.1 y hy).2
  have hu : ∀ y ∈ Ioo T.entrance T.endpoint,
      u (exp (s * y)) = (exp (s * y) / R) ^ ((j : ℝ) ^ 2) * V y := by
    simpa only [hradius, R] using hUV
  have hsource := Radial.radialJacobi_signed_physical_source_at hs hR hx
    ((hw.1.differentiable (by simp)) _) hw₀ hV hp hu
  simpa only [hradius, R, hrel.1] using hsource

/-- The exact physical source formula follows from the profile geometry and
the stated physical relation, without shrinking the deep-tail constants. -/
theorem tailPhysicalSourceIdentity_of_relation {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} (hD : IsAccumulatingProfile D)
    (hrel : TailPhysicalRelation D T right j start) :
    TailPhysicalSourceIdentity D T right j := by
  intro V u hV _hu hUV x hx
  exact tailPhysicalSourceIdentity_at_of_relation hD hrel
    (hV.contDiffAt.of_le (by simp)) hUV hx

end ContinuousFlexibility.Statements
