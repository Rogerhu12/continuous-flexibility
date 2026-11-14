module

public import ContinuousFlexibility.Radial.InnerDirichletCutoff
public import ContinuousFlexibility.Statements.RadialTargets
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The actual finite-interval Dirichlet energy domain

A smooth field with zero values at the two endpoints is approximated in all
three energy coordinates by supported smooth fields.  The endpoints are not
required to have zero derivatives.  All fields below are genuine Lebesgue
`L²` classes, and the closure is the frozen `IntervalEnergyCore` closure.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem innerDirichlet_indicator_memLp {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    MemLp ((Ioo a b).indicator f) 2 volume := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hf
  have hmem : MemLp f 2 (volume.restrict (Ioo a b)) :=
    MemLp.of_bound ((hf.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo) C
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        exact hC x (Ioo_subset_Icc_self hx))
  exact (memLp_indicator_iff_restrict measurableSet_Ioo).mpr hmem

def innerDirichletApprox (a b : ℝ) (u : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  innerDirichletCutoff a b ((n : ℝ) + 1) x * u x

theorem innerDirichletApprox_eq_zero {a b : ℝ} {u : ℝ → ℝ} (n : ℕ)
    {x : ℝ} (hx : x ∉ Ioo a b) : innerDirichletApprox a b u n x = 0 := by
  have hk : 0 < (n : ℝ) + 1 := by positivity
  rw [innerDirichletApprox, (innerDirichletCutoff_eventually_zero hk hx).eq_of_nhds, zero_mul]

theorem innerDirichletApprox_eventually_zero {a b : ℝ} {u : ℝ → ℝ} (n : ℕ)
    {x : ℝ} (hx : x ∉ Ioo a b) :
    innerDirichletApprox a b u n =ᶠ[𝓝 x] (fun _ => 0) := by
  have hk : 0 < (n : ℝ) + 1 := by positivity
  filter_upwards [innerDirichletCutoff_eventually_zero hk hx] with y hy
  exact show innerDirichletCutoff a b ((n : ℝ) + 1) y * u y = 0 by rw [hy, zero_mul]

theorem innerDirichletApprox_deriv_eq_zero {a b : ℝ} {u : ℝ → ℝ} (n : ℕ)
    {x : ℝ} (hx : x ∉ Ioo a b) : deriv (innerDirichletApprox a b u n) x = 0 :=
  (innerDirichletApprox_eventually_zero n hx).deriv_eq.trans (deriv_const x 0)

theorem innerDirichletApprox_contDiff {a b : ℝ} {u : ℝ → ℝ}
    (hu : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ u x) (n : ℕ) :
    ContDiff ℝ ∞ (innerDirichletApprox a b u n) :=
  innerDirichletCutoff_mul_contDiff (by positivity) hu

theorem innerDirichletApprox_hasCompactSupport (a b : ℝ) (u : ℝ → ℝ) (n : ℕ) :
    HasCompactSupport (innerDirichletApprox a b u n) :=
  (innerDirichletCutoff_hasCompactSupport (a := a) (b := b)
    (k := (n : ℝ) + 1) (by positivity)).mul_right

theorem innerDirichletApprox_memLp {a b : ℝ} {u : ℝ → ℝ}
    (hu : ContinuousOn u (Icc a b)) (n : ℕ) :
    MemLp (innerDirichletApprox a b u n) 2 volume := by
  have he : (Ioo a b).indicator (innerDirichletApprox a b u n) =
      innerDirichletApprox a b u n := by
    funext x
    by_cases hx : x ∈ Ioo a b
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx, innerDirichletApprox_eq_zero n hx]
  rw [← he]
  exact innerDirichlet_indicator_memLp
    ((innerDirichletCutoff_contDiff a b ((n : ℝ) + 1)).continuous.continuousOn.mul hu)

theorem innerDirichletApprox_eventually_eq {a b x : ℝ} {u : ℝ → ℝ}
    (hx : x ∈ Ioo a b) :
    ∀ᶠ n : ℕ in atTop, innerDirichletApprox a b u n =ᶠ[𝓝 x] u := by
  filter_upwards [innerDirichletCutoff_eventually_one_atTop hx] with n hn
  filter_upwards [hn] with y hy
  exact show innerDirichletCutoff a b ((n : ℝ) + 1) y * u y = u y by rw [hy, one_mul]

theorem innerDirichletApprox_abs_le (a b : ℝ) (u : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    |innerDirichletApprox a b u n x| ≤ |u x| := by
  rw [innerDirichletApprox, abs_mul,
    abs_of_nonneg (innerDirichletCutoff_nonneg a b ((n : ℝ) + 1) x)]
  exact (mul_le_mul_of_nonneg_right
    (innerDirichletCutoff_le_one a b ((n : ℝ) + 1) x) (abs_nonneg _)).trans_eq (one_mul _)

/-- The field and potential-energy coordinates only require bounded dominated
convergence; this statement does not require zero endpoint values. -/
theorem innerDirichletApprox_tendsto_L2 {a b : ℝ} {u : ℝ → ℝ}
    (hu : ContinuousOn u (Icc a b)) :
    Tendsto (fun n => (innerDirichletApprox_memLp hu n).toLp
      (innerDirichletApprox a b u n)) atTop
      (𝓝 ((innerDirichlet_indicator_memLp hu).toLp ((Ioo a b).indicator u))) := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hu
  let C : ℝ := max 0 C₀
  have hC : 0 ≤ C := le_max_left _ _
  have hbound : ∀ x ∈ Icc a b, |u x| ≤ C := by
    intro x hx
    simpa only [Real.norm_eq_abs] using (hC₀ x hx).trans (le_max_right 0 C₀)
  apply oscillator_tendsto_toLp_of_dominated
    (fun n => innerDirichletApprox_memLp hu n) (innerDirichlet_indicator_memLp hu)
    (innerDirichlet_indicator_memLp
      (show ContinuousOn (fun _ : ℝ => 2 * C) (Icc a b) from continuousOn_const))
  · intro n x
    by_cases hx : x ∈ Ioo a b
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, abs_of_nonneg (by positivity : 0 ≤ 2 * C)]
      exact (abs_sub _ _).trans (by
        have hf := innerDirichletApprox_abs_le a b u n x
        have huC := hbound x (Ioo_subset_Icc_self hx)
        linarith)
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
        innerDirichletApprox_eq_zero n hx, sub_self, abs_zero]
  · intro x
    by_cases hx : x ∈ Ioo a b
    · rw [Set.indicator_of_mem hx]
      apply (tendsto_congr' (show (fun n => innerDirichletApprox a b u n x) =ᶠ[atTop]
          (fun _ => u x) from ?_)).2 tendsto_const_nhds
      filter_upwards [innerDirichletApprox_eventually_eq (u := u) hx] with n hn
      exact hn.eq_of_nhds
    · rw [Set.indicator_of_notMem hx]
      have he : (fun n => innerDirichletApprox a b u n x) = (fun _ => 0) :=
        funext (fun n => innerDirichletApprox_eq_zero n hx)
      rw [he]
      exact tendsto_const_nhds

private theorem innerDirichletApprox_deriv_formula {a b k x : ℝ} {u : ℝ → ℝ}
    (hu : DifferentiableAt ℝ u x) :
    deriv (fun y => innerDirichletCutoff a b k y * u y) x =
      (deriv smoothTransition (k * (x - a) - 1) * k * u x) *
          smoothTransition (k * (b - x) - 1) -
        (deriv smoothTransition (k * (b - x) - 1) * k * u x) *
          smoothTransition (k * (x - a) - 1) +
        innerDirichletCutoff a b k x * deriv u x := by
  have hs : Differentiable ℝ smoothTransition :=
    (smoothTransition.contDiff : ContDiff ℝ ∞ smoothTransition).differentiable (by simp)
  have hL : HasDerivAt (fun y => smoothTransition (k * (y - a) - 1))
      (deriv smoothTransition (k * (x - a) - 1) * k) x := by
    simpa only [Function.comp_def, Pi.sub_apply, Pi.mul_apply, id_eq, mul_one] using
      (hs (k * (x - a) - 1)).hasDerivAt.comp x
        ((((hasDerivAt_id x).sub_const a).const_mul k).sub_const 1)
  have hR : HasDerivAt (fun y => smoothTransition (k * (b - y) - 1))
      (deriv smoothTransition (k * (b - x) - 1) * (-k)) x := by
    simpa only [Function.comp_def, Pi.sub_apply, Pi.mul_apply, id_eq, zero_sub, mul_neg,
      mul_one] using (hs (k * (b - x) - 1)).hasDerivAt.comp x
        ((((hasDerivAt_const x b).sub (hasDerivAt_id x)).const_mul k).sub_const 1)
  have h := ((hL.fun_mul hR).fun_mul hu.hasDerivAt).deriv
  dsimp only [innerDirichletCutoff] at h ⊢
  convert h using 1 <;> ring

/-- Endpoint zero values cancel the growing derivatives of the cutoffs. -/
theorem innerDirichletApprox_deriv_bound {a b C M : ℝ} {u : ℝ → ℝ}
    (hab : a < b) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (htransition : ∀ y, |deriv smoothTransition y| ≤ C)
    (hu : ∀ y ∈ Icc a b, DifferentiableAt ℝ u y)
    (hderiv : ∀ y ∈ Icc a b, |deriv u y| ≤ M)
    (ha : u a = 0) (hb : u b = 0) (n : ℕ) {x : ℝ} (hx : x ∈ Icc a b) :
    |deriv (innerDirichletApprox a b u n) x| ≤ (4 * C + 1) * M := by
  let k : ℝ := (n : ℝ) + 1
  have hk : 0 < k := by dsimp [k]; positivity
  have hleft : |u x| ≤ M * (x - a) := by
    simpa only [abs_of_nonneg (sub_nonneg.mpr hx.1)] using
      innerDirichlet_endpoint_bound hu hderiv ⟨le_rfl, hab.le⟩ hx ha
  have hright : |u x| ≤ M * (b - x) := by
    simpa only [abs_of_nonpos (sub_nonpos.mpr hx.2), neg_sub] using
      innerDirichlet_endpoint_bound hu hderiv ⟨hab.le, le_rfl⟩ hx hb
  have hL := innerTransition_deriv_mul_bound hk (sub_nonneg.mpr hx.1) hC hM
    htransition hleft
  have hR := innerTransition_deriv_mul_bound hk (sub_nonneg.mpr hx.2) hC hM
    htransition hright
  have hprod {v y : ℝ} (hv : |v| ≤ 2 * C * M) :
      |v * smoothTransition y| ≤ 2 * C * M := by
    rw [abs_mul, abs_of_nonneg (smoothTransition.nonneg _)]
    exact (mul_le_mul hv (smoothTransition.le_one _)
      (smoothTransition.nonneg _) (by positivity)).trans_eq (mul_one _)
  have hlast : |innerDirichletCutoff a b k x * deriv u x| ≤ M := by
    rw [abs_mul, abs_of_nonneg (innerDirichletCutoff_nonneg a b k x)]
    exact (mul_le_mul (innerDirichletCutoff_le_one a b k x) (hderiv x hx)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [show innerDirichletApprox a b u n = fun y => innerDirichletCutoff a b k y * u y from rfl,
    innerDirichletApprox_deriv_formula (hu x hx)]
  exact (abs_add_le _ _).trans ((add_le_add (abs_sub _ _) (le_refl _)).trans (by
    have hLL := hprod (y := k * (b - x) - 1) hL
    have hRR := hprod (y := k * (x - a) - 1) hR
    calc
      _ ≤ 2 * C * M + 2 * C * M + M := add_le_add (add_le_add hLL hRR) hlast
      _ = (4 * C + 1) * M := by ring))

theorem innerDirichlet_deriv_continuousOn {a b : ℝ} {u : ℝ → ℝ}
    (hu : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ u x) :
    ContinuousOn (deriv u) (Icc a b) := by
  intro x hx
  exact ((hu x hx).derivWithin (m := ∞) (by simp)).continuousAt.continuousWithinAt

theorem innerDirichletApprox_deriv_memLp {a b : ℝ} {u : ℝ → ℝ}
    (hu : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ u x) (n : ℕ) :
    MemLp (deriv (innerDirichletApprox a b u n)) 2 volume :=
  (innerDirichletApprox_contDiff hu n).continuous_deriv (by simp) |>.memLp_of_hasCompactSupport
    (innerDirichletApprox_hasCompactSupport a b u n).deriv

theorem innerDirichletApprox_deriv_tendsto_L2 {a b : ℝ} {u : ℝ → ℝ}
    (hab : a < b) (hu : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ u x)
    (ha : u a = 0) (hb : u b = 0) :
    Tendsto (fun n => (innerDirichletApprox_deriv_memLp hu n).toLp
      (deriv (innerDirichletApprox a b u n))) atTop
      (𝓝 ((innerDirichlet_indicator_memLp (innerDirichlet_deriv_continuousOn hu)).toLp
        ((Ioo a b).indicator (deriv u)))) := by
  obtain ⟨C, hC, htransition⟩ := innerTransition_deriv_bounded
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    (innerDirichlet_deriv_continuousOn hu)
  let M : ℝ := max 0 M₀
  have hM : 0 ≤ M := le_max_left _ _
  have hderiv : ∀ x ∈ Icc a b, |deriv u x| ≤ M := by
    intro x hx
    simpa only [Real.norm_eq_abs] using (hM₀ x hx).trans (le_max_right 0 M₀)
  have hdiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ u x :=
    fun x hx => (hu x hx).differentiableAt (by simp)
  apply oscillator_tendsto_toLp_of_dominated
    (fun n => innerDirichletApprox_deriv_memLp hu n)
    (innerDirichlet_indicator_memLp (innerDirichlet_deriv_continuousOn hu))
    (innerDirichlet_indicator_memLp
      (show ContinuousOn (fun _ : ℝ => (4 * C + 2) * M) (Icc a b) from continuousOn_const))
  · intro n x
    by_cases hx : x ∈ Ioo a b
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        abs_of_nonneg (by positivity : 0 ≤ (4 * C + 2) * M)]
      have hF := innerDirichletApprox_deriv_bound hab hC hM htransition hdiff hderiv ha hb n
        (Ioo_subset_Icc_self hx)
      have hf := hderiv x (Ioo_subset_Icc_self hx)
      exact (abs_sub _ _).trans (by linarith)
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
        innerDirichletApprox_deriv_eq_zero n hx, sub_self, abs_zero]
  · intro x
    by_cases hx : x ∈ Ioo a b
    · rw [Set.indicator_of_mem hx]
      apply (tendsto_congr' (show (fun n => deriv (innerDirichletApprox a b u n) x) =ᶠ[atTop]
          (fun _ => deriv u x) from ?_)).2 tendsto_const_nhds
      filter_upwards [innerDirichletApprox_eventually_eq (u := u) hx] with n hn
      exact hn.deriv_eq
    · rw [Set.indicator_of_notMem hx]
      have he : (fun n => deriv (innerDirichletApprox a b u n) x) = (fun _ => 0) :=
        funext (fun n => innerDirichletApprox_deriv_eq_zero n hx)
      rw [he]
      exact tendsto_const_nhds

/-- Smooth zero-endpoint fields belong to the actual Dirichlet energy closure.
The first derivatives at the endpoints are unrestricted. -/
theorem intervalEnergyClosure_of_smooth_zero_endpoints {a b : ℝ} {V φ : ℝ → ℝ}
    (hab : a < b) (hV : ContinuousOn V (Icc a b))
    (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ φ x) (ha : φ a = 0) (hb : φ b = 0)
    {u d q : RadialL2}
    (hu : (u : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator φ)
    (hd : (d : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv φ))
    (hq : (q : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (fun x => sqrt (1 + |V x|) * φ x)) :
    (u, d, q) ∈ closure (IntervalEnergyCore V a b) := by
  have hφc : ContinuousOn φ (Icc a b) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  let w : ℝ → ℝ := fun x => sqrt (1 + |V x|) * φ x
  have hw : ContinuousOn w (Icc a b) :=
    (continuousOn_const.add hV.abs).sqrt.mul hφc
  let U : ℕ → RadialL2 := fun n =>
    (innerDirichletApprox_memLp hφc n).toLp (innerDirichletApprox a b φ n)
  let D : ℕ → RadialL2 := fun n =>
    (innerDirichletApprox_deriv_memLp hφ n).toLp (deriv (innerDirichletApprox a b φ n))
  let Q : ℕ → RadialL2 := fun n =>
    (innerDirichletApprox_memLp hw n).toLp (innerDirichletApprox a b w n)
  have hU : Tendsto U atTop (𝓝 u) := by
    have he : (innerDirichlet_indicator_memLp hφc).toLp ((Ioo a b).indicator φ) = u := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp _).trans hu.symm
    simpa only [he] using innerDirichletApprox_tendsto_L2 hφc
  have hD : Tendsto D atTop (𝓝 d) := by
    have he : (innerDirichlet_indicator_memLp (innerDirichlet_deriv_continuousOn hφ)).toLp
        ((Ioo a b).indicator (deriv φ)) = d := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp _).trans hd.symm
    simpa only [he] using innerDirichletApprox_deriv_tendsto_L2 hab hφ ha hb
  have hQ : Tendsto Q atTop (𝓝 q) := by
    have he : (innerDirichlet_indicator_memLp hw).toLp ((Ioo a b).indicator w) = q := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp _).trans hq.symm
    simpa only [he] using innerDirichletApprox_tendsto_L2 hw
  apply mem_closure_of_tendsto (hU.prodMk_nhds (hD.prodMk_nhds hQ))
  apply Eventually.of_forall
  intro n
  refine ⟨⟨innerDirichletApprox a b φ n, innerDirichletApprox_contDiff hφ n,
    innerDirichletApprox_hasCompactSupport a b φ n,
    MemLp.coeFn_toLp (innerDirichletApprox_memLp hφc n),
    MemLp.coeFn_toLp (innerDirichletApprox_deriv_memLp hφ n), ?_⟩, ?_⟩
  · filter_upwards [MemLp.coeFn_toLp (innerDirichletApprox_memLp hw n)] with x hx
    rw [hx]
    dsimp only [innerDirichletApprox, w]
    ring
  · filter_upwards [ae_restrict_of_ae (MemLp.coeFn_toLp
      (innerDirichletApprox_memLp hφc n)), ae_restrict_mem measurableSet_Ioo.compl] with x hx hout
    exact hx.trans (innerDirichletApprox_eq_zero n hout)

/-- A continuous representative of an interval-supported class vanishes at
both endpoints as well as on the exterior. This is one statement for the two
ends, using regular closedness of the complement of the open interval. -/
theorem innerDirichlet_representative_zero_outside {a b : ℝ} {ψ : ℝ → ℝ}
    (hab : a < b) (hψ : Continuous ψ)
    (hs : ψ =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0)) :
    EqOn ψ (fun _ => 0) ((Ioo a b)ᶜ) := by
  apply MeasureTheory.Measure.eqOn_of_ae_eq hs hψ.continuousOn continuousOn_const
  simp only [interior_compl, closure_compl, closure_Ioo hab.ne, interior_Icc]
  exact Subset.rfl

theorem innerDirichlet_classical_pairing {a b : ℝ} {V φ ψ : ℝ → ℝ}
    (hab : a < b) (hV : ContinuousOn V (Icc a b))
    (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ φ x)
    (hψ : ContDiff ℝ ∞ ψ) (haψ : ψ a = 0) (hbψ : ψ b = 0) :
    (∫ x in a..b, (-deriv (deriv φ) x + V x * φ x) * ψ x) =
      (∫ x in a..b, deriv φ x * deriv ψ x) +
        ∫ x in a..b, V x * φ x * ψ x := by
  have hφc : ContinuousOn φ (Icc a b) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hφd : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ (deriv φ) x :=
    fun x hx => (hφ x hx).derivWithin (m := ∞) (by simp)
  have hd : ContinuousOn (deriv φ) (Icc a b) := innerDirichlet_deriv_continuousOn hφ
  have hdd : ContinuousOn (deriv (deriv φ)) (Icc a b) :=
    innerDirichlet_deriv_continuousOn hφd
  have hψc : ContinuousOn ψ (Icc a b) := hψ.continuous.continuousOn
  have hψd : ContinuousOn (deriv ψ) (Icc a b) :=
    (hψ.continuous_deriv (by simp)).continuousOn
  have hI₁ : IntervalIntegrable (fun x => deriv (deriv φ) x * ψ x) volume a b :=
    (hdd.mul hψc).intervalIntegrable_of_Icc hab.le
  have hI₂ : IntervalIntegrable (fun x => deriv φ x * deriv ψ x) volume a b :=
    (hd.mul hψd).intervalIntegrable_of_Icc hab.le
  have hIV : IntervalIntegrable (fun x => V x * φ x * ψ x) volume a b :=
    ((hV.mul hφc).mul hψc).intervalIntegrable_of_Icc hab.le
  have hparts : (∫ x in a..b,
      deriv (deriv φ) x * ψ x + deriv φ x * deriv ψ x) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le (hd.mul hψc)
      (fun x hx => ((hφd x (Ioo_subset_Icc_self hx)).differentiableAt (by simp)).hasDerivAt.mul
        ((hψ.differentiable (by simp) x).hasDerivAt)) (hI₁.add hI₂)
    simpa only [Pi.mul_apply, haψ, hbψ, mul_zero, sub_self] using h
  rw [intervalIntegral.integral_add hI₁ hI₂] at hparts
  calc
    (∫ x in a..b, (-deriv (deriv φ) x + V x * φ x) * ψ x) =
        -(∫ x in a..b, deriv (deriv φ) x * ψ x) +
          ∫ x in a..b, V x * φ x * ψ x := by
      calc
        (∫ x in a..b, (-deriv (deriv φ) x + V x * φ x) * ψ x) =
            ∫ x in a..b, -(deriv (deriv φ) x * ψ x) + V x * φ x * ψ x := by
          apply intervalIntegral.integral_congr
          intro x hx
          ring
        _ = -(∫ x in a..b, deriv (deriv φ) x * ψ x) +
            ∫ x in a..b, V x * φ x * ψ x := by
          simpa only [Pi.add_apply, Pi.neg_apply, intervalIntegral.integral_neg] using
            intervalIntegral.integral_add hI₁.neg hIV
    _ = (∫ x in a..b, deriv φ x * deriv ψ x) +
        ∫ x in a..b, V x * φ x * ψ x := by linarith

theorem innerDirichlet_pairing_indicator {a b : ℝ} (hab : a ≤ b)
    {u v : RadialL2} {f g : ℝ → ℝ}
    (hu : (u : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator f)
    (hv : (v : ℝ → ℝ) =ᵐ[volume] g) :
    ⟪u, v⟫_ℝ = ∫ x in a..b, f x * g x := by
  rw [L2.inner_def]
  calc
    (∫ x : ℝ, ⟪u x, v x⟫_ℝ) =
        ∫ x : ℝ, (Ioo a b).indicator (fun y => f y * g y) x := by
      apply integral_congr_ae
      filter_upwards [hu, hv] with x hux hvx
      rw [hux, hvx]
      by_cases hx : x ∈ Ioo a b
      · simp only [Set.indicator_of_mem hx, RCLike.inner_apply, conj_trivial]
        ring
      · simp only [Set.indicator_of_notMem hx, inner_zero_left]
    _ = ∫ x in Ioo a b, f x * g x := integral_indicator measurableSet_Ioo
    _ = ∫ x in a..b, f x * g x := by
      rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

/-- The actual differential equation of a smooth zero-endpoint field defines
an element of the frozen closed Dirichlet form graph. No domain membership,
trace theorem, or inverse property is an input. -/
theorem intervalFormGraph_of_smooth_zero_endpoints {a b : ℝ} {V φ : ℝ → ℝ}
    (hab : a < b) (hV : ContinuousOn V (Icc a b))
    (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ φ x) (ha : φ a = 0) (hb : φ b = 0)
    {u f : RadialL2}
    (hu : (u : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator φ)
    (hf : (f : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (fun x => -deriv (deriv φ) x + V x * φ x)) :
    IntervalFormGraph V a b u f := by
  have hφc : ContinuousOn φ (Icc a b) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hdc := innerDirichlet_deriv_continuousOn hφ
  have hqc : ContinuousOn (fun x => sqrt (1 + |V x|) * φ x) (Icc a b) :=
    (continuousOn_const.add hV.abs).sqrt.mul hφc
  have hvc : ContinuousOn (fun x => V x * φ x) (Icc a b) := hV.mul hφc
  let d : RadialL2 := (innerDirichlet_indicator_memLp hdc).toLp ((Ioo a b).indicator (deriv φ))
  let q : RadialL2 := (innerDirichlet_indicator_memLp hqc).toLp
    ((Ioo a b).indicator (fun x => sqrt (1 + |V x|) * φ x))
  let v : RadialL2 := (innerDirichlet_indicator_memLp hvc).toLp
    ((Ioo a b).indicator (fun x => V x * φ x))
  have hd : (d : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv φ) := MemLp.coeFn_toLp _
  have hq : (q : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (fun x => sqrt (1 + |V x|) * φ x) := MemLp.coeFn_toLp _
  have hv : (v : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (fun x => V x * φ x) := MemLp.coeFn_toLp _
  have hcore : IntervalEnergyCore V a b ⊆
      {p : RadialL2 × RadialL2 × RadialL2 |
        ⟪f, p.1⟫_ℝ = ⟪d, p.2.1⟫_ℝ + ⟪v, p.1⟫_ℝ} := by
    intro p hp
    obtain ⟨ψ, hψ, hcψ, hpψ, hpd, hpq⟩ := hp.1
    have hpψout : (p.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo a b)ᶜ)] ψ :=
      ae_restrict_of_ae hpψ
    have hψout : ψ =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0) :=
      Filter.EventuallyEq.trans (Filter.EventuallyEq.symm hpψout) hp.2
    have hzero : EqOn ψ (fun _ => 0) ((Ioo a b)ᶜ) :=
      innerDirichlet_representative_zero_outside hab hψ.continuous hψout
    have hψa : ψ a = 0 := hzero (by simp : a ∈ (Ioo a b)ᶜ)
    have hψb : ψ b = 0 := hzero (by simp : b ∈ (Ioo a b)ᶜ)
    change ⟪f, p.1⟫_ℝ = ⟪d, p.2.1⟫_ℝ + ⟪v, p.1⟫_ℝ
    rw [innerDirichlet_pairing_indicator hab.le hf hpψ,
      innerDirichlet_pairing_indicator hab.le hd hpd,
      innerDirichlet_pairing_indicator hab.le hv hpψ]
    exact innerDirichlet_classical_pairing hab hV hφ hψ hψa hψb
  have hclosed : IsClosed {p : RadialL2 × RadialL2 × RadialL2 |
      ⟪f, p.1⟫_ℝ = ⟪d, p.2.1⟫_ℝ + ⟪v, p.1⟫_ℝ} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  refine ⟨d, q, intervalEnergyClosure_of_smooth_zero_endpoints hab hV hφ ha hb hu hd hq,
    fun p hp => ?_⟩
  have hpairs := closure_minimal hcore hclosed hp
  have hpotential : ⟪v, p.1⟫_ℝ = ∫ x : ℝ, V x * u x * p.1 x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv, hu] with x hvx hux
    rw [hvx, hux]
    by_cases hx : x ∈ Ioo a b
    · simp only [Set.indicator_of_mem hx, RCLike.inner_apply, conj_trivial]
      ring
    · simp only [Set.indicator_of_notMem hx, inner_zero_left, mul_zero, zero_mul]
  exact hpairs.trans (congrArg (⟪d, p.2.1⟫_ℝ + ·) hpotential)

end ContinuousFlexibility.Radial
