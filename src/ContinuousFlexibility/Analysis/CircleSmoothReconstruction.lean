import ContinuousFlexibility.Analysis.CircleWeakPrimitive
import Mathlib.Topology.Instances.AddCircle.Defs

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology BigOperators

namespace ContinuousFlexibility.Statements

noncomputable section

set_option backward.isDefEq.respectTransparency false

private theorem periodic_deriv_of_contDiff {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hp : Function.Periodic φ Real.pi) : Function.Periodic (deriv φ) Real.pi := by
  intro x
  have h₁ : HasDerivAt (fun t : ℝ => t + Real.pi) 1 x :=
    (hasDerivAt_id x).add_const Real.pi
  have h₂ := ((hφ.differentiable (by simp) (x + Real.pi)).hasDerivAt).comp x h₁
  have he : (φ ∘ fun t : ℝ => t + Real.pi) = φ := funext hp
  rw [he, mul_one] at h₂
  exact h₂.deriv.symm

theorem hasWeakAngularDerivative_succ_adjacent {f d e : AngleL2} {b : ℕ}
    (hd : HasWeakAngularDerivative f d b) (he : HasWeakAngularDerivative f e (b + 1)) :
    HasWeakAngularDerivative d e 1 := by
  intro φ hφ hp
  have hd' := hd (deriv φ) (contDiff_infty_iff_deriv.mp hφ).2
    (periodic_deriv_of_contDiff hφ hp)
  have he' := he φ hφ hp
  rw [iteratedDeriv_succ'] at he'
  rw [he', iteratedDeriv_one, hd', pow_succ, pow_one]
  ring

theorem hasWeakAngularDerivative_unique {f d e : AngleL2} {b : ℕ}
    (hd : HasWeakAngularDerivative f d b) (he : HasWeakAngularDerivative f e b) : d = e := by
  apply Lp.ext
  have hz : ∀ᵐ x ∂angleMeasure, d x - e x = 0 := by
    apply ae_eq_zero_of_integral_periodic_angle ((integrable_angleL2 d).sub (integrable_angleL2 e))
    intro φ hφ hp
    have hφ₂ := memLp_angleMeasure_of_continuous hφ.continuous
    have hprodD : Integrable (fun x => d x * φ x) angleMeasure := (Lp.memLp d).integrable_mul hφ₂
    have hprodE : Integrable (fun x => e x * φ x) angleMeasure := (Lp.memLp e).integrable_mul hφ₂
    change (∫ x, (d x - e x) * φ x ∂angleMeasure) = 0
    simp only [sub_mul, integral_sub hprodD hprodE, hd φ hφ hp, he φ hφ hp, sub_self]
  exact hz.mono fun _ hx => sub_eq_zero.mp hx

theorem continuous_anglePeriodize_of_endpoint_eq {f : ℝ → ℝ} (hf : Continuous f)
    (he : f 0 = f Real.pi) : Continuous (anglePeriodize f) := by
  let : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩
  have hc : Continuous (AddCircle.liftIoc Real.pi 0 f) :=
    AddCircle.liftIoc_zero_continuous he hf.continuousOn
  have h : Continuous
      (AddCircle.liftIoc Real.pi 0 f ∘ fun x : ℝ => (x : AddCircle Real.pi)) :=
    hc.comp (AddCircle.continuous_mk' Real.pi)
  have hfun : (AddCircle.liftIoc Real.pi 0 f ∘ fun x : ℝ => (x : AddCircle Real.pi)) =
      anglePeriodize f := by
    funext x
    rfl
  rwa [hfun] at h

theorem angle_periodic_eq_of_eqOn_Ioc {f g : ℝ → ℝ}
    (hf : Function.Periodic f Real.pi) (hg : Function.Periodic g Real.pi)
    (h : EqOn f g (Ioc 0 Real.pi)) : f = g := by
  funext x
  let y := toIocMod Real.pi_pos 0 x
  let n := toIocDiv Real.pi_pos 0 x
  have hy : y ∈ Ioc (0 : ℝ) Real.pi := by
    simpa only [y, zero_add] using toIocMod_mem_Ioc Real.pi_pos 0 x
  have hx : y + n • Real.pi = x := toIocMod_add_toIocDiv_zsmul Real.pi_pos 0 x
  calc
    f x = f (y + n • Real.pi) := congrArg f hx.symm
    _ = f y := hf.zsmul n y
    _ = g y := h hy
    _ = g (y + n • Real.pi) := (hg.zsmul n y).symm
    _ = g x := congrArg g hx

theorem angle_periodic_eq_of_ae_eq {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfp : Function.Periodic f Real.pi) (hgp : Function.Periodic g Real.pi)
    (h : f =ᵐ[angleMeasure] g) : f = g :=
  angle_periodic_eq_of_eqOn_Ioc hfp hgp
    (Measure.eqOn_Ioc_of_ae_eq volume h hf.continuousOn hg.continuousOn)

/-- A tower of actual adjacent weak derivatives has a smooth periodic
representative. Each member represents the matching classical derivative. -/
theorem exists_smooth_periodic_of_weak_angular_tower (d : ℕ → AngleL2)
    (hw : ∀ b : ℕ, HasWeakAngularDerivative (d b) (d (b + 1)) 1) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ Function.Periodic f Real.pi ∧
      ∀ b : ℕ, (⇑(d b)) =ᵐ[angleMeasure] iteratedDeriv b f := by
  choose c hc hends using fun b => exists_angleIntegralPrimitive_rep_of_hasWeakAngularDerivative (hw b)
  let q (b : ℕ) (x : ℝ) : ℝ := c b + angleIntegralPrimitive (d (b + 1)) x
  let g (b : ℕ) : ℝ → ℝ := anglePeriodize (q b)
  have hg (b : ℕ) : Continuous (g b) :=
    continuous_anglePeriodize_of_endpoint_eq
      (continuous_const.add (continuous_angleIntegralPrimitive (d (b + 1)))) (hends b)
  have hper (b : ℕ) : Function.Periodic (g b) Real.pi := anglePeriodize_periodic (q b)
  have hmem : ∀ᵐ x ∂angleMeasure, x ∈ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem measurableSet_Ioc
  have hae (b : ℕ) : (⇑(d b)) =ᵐ[angleMeasure] g b := by
    filter_upwards [hc b, hmem] with x hx hm
    exact hx.trans (anglePeriodize_eqOn (q b) hm).symm
  have hI (b : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) Real.pi) :
      angleIntegralPrimitive (d b) x = ∫ y in 0..x, g b y := by
    rw [angleIntegralPrimitive_eq_integral_volume (d b) hx]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hx.1]
    exact (hae b).filter_mono (ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right hx.2) le_rfl))
  have hmean (b : ℕ) : (∫ y in (0 : ℝ)..Real.pi, g (b + 1) y) = 0 := by
    rw [← hI (b + 1) ⟨Real.pi_pos.le, le_rfl⟩]
    exact (angleIntegralPrimitive_endpoints (hw b)).2
  have hg_int (b : ℕ) :
      g b = fun x => c b + ∫ y in (0 : ℝ)..x, g (b + 1) y := by
    apply angle_periodic_eq_of_eqOn_Ioc (hper b)
    · intro x
      change c b + (∫ y in (0 : ℝ)..x + Real.pi, g (b + 1) y) =
        c b + ∫ y in (0 : ℝ)..x, g (b + 1) y
      rw [(hper (b + 1)).intervalIntegral_add_eq_add 0 x
        (fun a t => (hg (b + 1)).intervalIntegrable a t), zero_add, hmean b, add_zero]
    · intro x hx
      change anglePeriodize (q b) x = c b + ∫ y in (0 : ℝ)..x, g (b + 1) y
      rw [anglePeriodize_eqOn (q b) hx]
      exact congrArg (c b + ·) (hI (b + 1) ⟨hx.1.le, hx.2⟩)
  have hd (b : ℕ) (x : ℝ) : HasDerivAt (g b) (g (b + 1) x) x := by
    rw [hg_int b]
    exact (intervalIntegral.integral_hasDerivAt_right ((hg (b + 1)).intervalIntegrable 0 x)
      (hg (b + 1)).aestronglyMeasurable.stronglyMeasurableAtFilter
      (hg (b + 1)).continuousAt).const_add _
  have hder (b : ℕ) : deriv (g b) = g (b + 1) := funext fun x => (hd b x).deriv
  have hjet (b : ℕ) : iteratedDeriv b (g 0) = g b := by
    induction b with
    | zero => rw [iteratedDeriv_zero]
    | succ b ih => rw [iteratedDeriv_succ, ih, hder b]
  have hsmooth : ContDiff ℝ ∞ (g 0) := by
    apply contDiff_of_differentiable_iteratedDeriv
    intro b _
    rw [hjet b]
    exact fun x => (hd b x).differentiableAt
  refine ⟨g 0, hsmooth, hper 0, ?_⟩
  intro b
  rw [hjet b]
  exact hae b

def circleJetPureAngularIndex (b : ℕ) : CircleJetIndex b :=
  ⟨fun i => if i = 0 then ⟨b, Nat.lt_succ_self b⟩ else 0, by simp⟩

@[simp] theorem circleJetPureAngularIndex_order (b : ℕ) :
    ((circleJetPureAngularIndex b).val 0).val = b := by
  simp [circleJetPureAngularIndex]

@[simp] theorem circleJetPureAngularIndex_weight (b : ℕ) :
    ((circleJetPureAngularIndex b).val 1).val = 0 := by
  simp [circleJetPureAngularIndex]

variable {T : MaterialData} {hM : ∀ m, 0 < T.M (T.sample m)}

/-- The unweighted angular derivative of order b from the order-b level. -/
def circleJetAngularDerivative (u : CircleJetProjectiveLimit T hM) (m b : ℕ) : AngleL2 :=
  (u.val b).val m (circleJetPureAngularIndex b)

private theorem circleJetProjective_mem_graph (u : CircleJetProjectiveLimit T hM) (s : ℕ) :
    (u.val s).val ∈ circleJetGraph T s := by
  rw [← circleJetClosedSubmodule_carrier hM]
  exact (u.val s).property

theorem circleJetAngularDerivative_spec (u : CircleJetProjectiveLimit T hM) (m b : ℕ) :
    HasWeakAngularDerivative ((u.val 0).val m (zeroCircleJetIndex 0))
      (circleJetAngularDerivative u m b) b := by
  have hh := (mem_circleJetGraph_iff_normalized hM (u.val b).val).mp
    (circleJetProjective_mem_graph u b) m (circleJetPureAngularIndex b)
  rw [circleJetProjective_zero_eq u b m, circleJetNormalizedDerivative_apply] at hh
  simpa only [circleJetWeight, circleJetPureAngularIndex_order, circleJetPureAngularIndex_weight,
    pow_zero, inv_one, one_smul, circleJetAngularDerivative] using hh

theorem circleJetAngularDerivative_adjacent (u : CircleJetProjectiveLimit T hM) (m b : ℕ) :
    HasWeakAngularDerivative (circleJetAngularDerivative u m b)
      (circleJetAngularDerivative u m (b + 1)) 1 :=
  hasWeakAngularDerivative_succ_adjacent (circleJetAngularDerivative_spec u m b)
    (circleJetAngularDerivative_spec u m (b + 1))

theorem circleJetNormalizedDerivative_eq_angular (u : CircleJetProjectiveLimit T hM)
    (s m : ℕ) (j : CircleJetIndex s) :
    circleJetNormalizedDerivative T m j (u.val s).val =
      circleJetAngularDerivative u m (j.val 0).val := by
  have hh := (mem_circleJetGraph_iff_normalized hM (u.val s).val).mp
    (circleJetProjective_mem_graph u s) m j
  rw [circleJetProjective_zero_eq u s m] at hh
  exact hasWeakAngularDerivative_unique hh (circleJetAngularDerivative_spec u m (j.val 0).val)

/-- The smooth representative of the normalized order-zero jet. -/
def circleJetRawSmooth (u : CircleJetProjectiveLimit T hM) (m : ℕ) : ℝ → ℝ :=
  Classical.choose (exists_smooth_periodic_of_weak_angular_tower
    (circleJetAngularDerivative u m) (circleJetAngularDerivative_adjacent u m))

theorem circleJetRawSmooth_spec (u : CircleJetProjectiveLimit T hM) (m : ℕ) :
    ContDiff ℝ ∞ (circleJetRawSmooth u m) ∧ Function.Periodic (circleJetRawSmooth u m) Real.pi ∧
      ∀ b, (⇑(circleJetAngularDerivative u m b)) =ᵐ[angleMeasure]
        iteratedDeriv b (circleJetRawSmooth u m) :=
  Classical.choose_spec (exists_smooth_periodic_of_weak_angular_tower
    (circleJetAngularDerivative u m) (circleJetAngularDerivative_adjacent u m))

theorem circleJetRawSmooth_level_ae (u : CircleJetProjectiveLimit T hM)
    (s m : ℕ) (j : CircleJetIndex s) :
    (((u.val s).val m j) : ℝ → ℝ) =ᵐ[angleMeasure]
      fun x => circleJetWeight T m j * iteratedDeriv (j.val 0).val (circleJetRawSmooth u m) x := by
  obtain ⟨d, hd, hweighted⟩ := circleJetProjective_mem_graph u s m j
  have hd' : d = circleJetAngularDerivative u m (j.val 0).val := by
    rw [circleJetProjective_zero_eq u s m] at hd
    exact hasWeakAngularDerivative_unique hd (circleJetAngularDerivative_spec u m (j.val 0).val)
  rw [hd'] at hweighted
  filter_upwards [hweighted, (circleJetRawSmooth_spec u m).2.2 (j.val 0).val] with x hx hder
  exact hx.trans (congrArg (circleJetWeight T m j * ·) hder)

/-- Restore the unnormalized angular function at each sample. -/
def circleJetDecoded (u : CircleJetProjectiveLimit T hM) (γ : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  T.H (T.sample m) ^ γ * circleJetRawSmooth u m x

theorem circleJetDecoded_contDiff (u : CircleJetProjectiveLimit T hM) (γ : ℝ) (m : ℕ) :
    ContDiff ℝ ∞ (circleJetDecoded u γ m) :=
  contDiff_const.mul (circleJetRawSmooth_spec u m).1

theorem circleJetDecoded_periodic (u : CircleJetProjectiveLimit T hM) (γ : ℝ) (m : ℕ) :
    Function.Periodic (circleJetDecoded u γ m) Real.pi := by
  intro x
  exact congrArg (T.H (T.sample m) ^ γ * ·) ((circleJetRawSmooth_spec u m).2.1 x)

theorem circleJetDecoded_level_ae (hH : ∀ m, 0 < T.H (T.sample m))
    (u : CircleJetProjectiveLimit T hM) (γ : ℝ) (s m : ℕ) (j : CircleJetIndex s) :
    (((u.val s).val m j) : ℝ → ℝ) =ᵐ[angleMeasure]
      fun x => (circleJetWeight T m j * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv (j.val 0).val (circleJetDecoded u γ m) x := by
  have hscalar : T.H (T.sample m) ^ (-γ) * T.H (T.sample m) ^ γ = 1 := by
    rw [← Real.rpow_add (hH m), neg_add_cancel, Real.rpow_zero]
  filter_upwards [circleJetRawSmooth_level_ae u s m j] with x hx
  change (u.val s).val m j x = (circleJetWeight T m j * T.H (T.sample m) ^ (-γ)) *
    iteratedDeriv (j.val 0).val (fun y => T.H (T.sample m) ^ γ * circleJetRawSmooth u m y) x
  rw [hx, iteratedDeriv_const_mul_field]
  rw [← mul_assoc, mul_assoc (circleJetWeight T m j), hscalar, mul_one]

theorem circleJetDecoded_zero_ae (hH : ∀ m, 0 < T.H (T.sample m))
    (u : CircleJetProjectiveLimit T hM) (γ : ℝ) (s m : ℕ) :
    (((u.val s).val m (zeroCircleJetIndex s)) : ℝ → ℝ) =ᵐ[angleMeasure]
      fun x => T.H (T.sample m) ^ (-γ) * circleJetDecoded u γ m x := by
  simpa [circleJetWeight, zeroCircleJetIndex] using
    circleJetDecoded_level_ae hH u γ s m (zeroCircleJetIndex s)

private theorem ofReal_norm_sq_angleL2_of_ae_mul {v : AngleL2} {f : ℝ → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (h : (⇑v) =ᵐ[angleMeasure] fun x => c * f x) :
    ENNReal.ofReal (‖v‖ ^ 2) = ENNReal.ofReal (c ^ 2) * eLpNorm f 2 angleMeasure ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top v),
    eLpNorm_congr_ae h]
  change eLpNorm (c • f) 2 angleMeasure ^ 2 = _
  rw [eLpNorm_const_smul, mul_pow, Real.enorm_eq_ofReal_abs, abs_of_nonneg hc,
    ENNReal.ofReal_pow hc]

theorem circleJetDecoded_energy_eq (hH : ∀ m, 0 < T.H (T.sample m))
    (u : CircleJetProjectiveLimit T hM) (γ : ℝ) (s : ℕ) :
    (∑' m : ℕ, ∑ j : CircleJetIndex s,
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (circleJetDecoded u γ m)) 2 angleMeasure ^ 2) =
      ENNReal.ofReal (‖u.val s‖ ^ 2) := by
  let z := (u.val s).val
  change _ = ENNReal.ofReal (‖z‖ ^ 2)
  rw [circleJetHilbert_norm_sq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
    (circleJetHilbert_summable_sq z)]
  apply tsum_congr
  intro m
  rw [PiLp.norm_sq_eq_of_L2, ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  apply Finset.sum_congr rfl
  intro j _
  have hc : 0 ≤ circleJetWeight T m j * T.H (T.sample m) ^ (-γ) :=
    mul_nonneg (pow_nonneg (hM m).le _) (Real.rpow_nonneg (hH m).le _)
  exact (ofReal_norm_sq_angleL2_of_ae_mul hc (circleJetDecoded_level_ae hH u γ s m j)).symm

theorem circleJetDecoded_circleNorm (hH : ∀ m, 0 < T.H (T.sample m))
    (u : CircleJetProjectiveLimit T hM) (γ : ℝ) (s : ℕ) :
    ‖u.val s‖ = circleNorm T γ s (circleJetDecoded u γ) := by
  rw [circleNorm, circleJetDecoded_energy_eq hH u γ s, ENNReal.toReal_ofReal (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

theorem circleJetDecoded_circleMember (hH : ∀ m, 0 < T.H (T.sample m))
    (u : CircleJetProjectiveLimit T hM) (γ : ℝ) :
    CircleMember T γ (circleJetDecoded u γ) := by
  refine ⟨fun m => ⟨circleJetDecoded_contDiff u γ m, circleJetDecoded_periodic u γ m⟩,
    fun m b => memLp_angleMeasure_iteratedDeriv_of_contDiff (circleJetDecoded_contDiff u γ m) b,
    ?_⟩
  intro s
  rw [circleJetDecoded_energy_eq hH u γ s]
  exact ENNReal.ofReal_lt_top

end

end ContinuousFlexibility.Statements
