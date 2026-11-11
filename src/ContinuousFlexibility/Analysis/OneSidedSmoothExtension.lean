import ContinuousFlexibility.Analysis.FlatExtension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Smooth extension across one regular endpoint

The construction uses compactly supported monomials with successively
smaller scales. Their lower derivatives are uniformly small, while the
specified derivative at the origin is unchanged. This supplies a single
smooth function realizing all prescribed endpoint jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff BigOperators

theorem exists_compact_iteratedDeriv_bound {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv k g x‖ ≤ C := by
  have hsupport : HasCompactSupport (iteratedDeriv k g) := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hs
    | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv
  obtain ⟨C, hC⟩ := hsupport.exists_bound_of_continuous
    (ContDiff.continuous_iteratedDeriv k hg (by simp))
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

def oneSidedJetBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- One compactly supported monomial, normalized by the factorial. -/
def oneSidedJetBase (c : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (c / (n.factorial : ℝ)) * x ^ n * oneSidedJetBump x

theorem contDiff_oneSidedJetBase (c : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (oneSidedJetBase c n) :=
  (contDiff_const.mul (contDiff_id.pow n)).mul oneSidedJetBump.contDiff

theorem hasCompactSupport_oneSidedJetBase (c : ℝ) (n : ℕ) :
    HasCompactSupport (oneSidedJetBase c n) :=
  oneSidedJetBump.hasCompactSupport.mul_left

theorem iteratedDeriv_oneSidedJetBase_zero (c : ℝ) (n k : ℕ) :
    iteratedDeriv k (oneSidedJetBase c n) 0 = if k = n then c else 0 := by
  have heq : oneSidedJetBase c n =ᶠ[𝓝 0] fun x => (c / (n.factorial : ℝ)) * x ^ n := by
    filter_upwards [oneSidedJetBump.eventuallyEq_one] with x hx
    simp only [oneSidedJetBase, hx, Pi.one_apply, mul_one]
  rw [heq.iteratedDeriv_eq k, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  by_cases hkn : k = n
  · rw [if_pos hkn, if_pos hkn]
    exact div_mul_cancel₀ c (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  · rw [if_neg hkn, if_neg hkn, Nat.cast_zero, mul_zero]

/-- Scaling preserves the target jet while suppressing lower derivatives. -/
def oneSidedScaledJet (n : ℕ) (ε : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ε ^ n * g (ε⁻¹ * x)

theorem contDiff_oneSidedScaledJet {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (ε : ℝ) : ContDiff ℝ ∞ (oneSidedScaledJet n ε g) :=
  contDiff_const.mul (hg.comp (contDiff_const.mul contDiff_id))

theorem iteratedDeriv_oneSidedScaledJet {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (n k : ℕ) (ε x : ℝ) :
    iteratedDeriv k (oneSidedScaledJet n ε g) x =
      (ε ^ n * (ε⁻¹) ^ k) * iteratedDeriv k g (ε⁻¹ * x) := by
  unfold oneSidedScaledJet
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul ((contDiff_infty.mp hg) k) (ε⁻¹)]
  ring

theorem oneSidedScaledJet_factor {ε : ℝ} (hε : 0 < ε) {k n : ℕ} (hkn : k ≤ n) :
    ε ^ n * (ε⁻¹) ^ k = ε ^ (n - k) := by
  rw [inv_pow]
  exact (pow_sub₀ ε hε.ne' hkn).symm

/-- A single positive scale makes every derivative below the target order
uniformly as small as prescribed. -/
theorem exists_oneSidedScaledJet_small {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ k < n, ∀ x, ‖iteratedDeriv k (oneSidedScaledJet n ε g) x‖ ≤ δ := by
  choose C hC₀ hC using fun k : ℕ => exists_compact_iteratedDeriv_bound hg hs k
  have hall : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∀ k ∈ Finset.range n, ε ^ (n - k) * C k < δ := by
    rw [eventually_all_finset]
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    have hcont : Continuous (fun ε : ℝ => ε ^ (n - k) * C k) :=
      (continuous_id.pow _).mul continuous_const
    have hlim : Tendsto (fun ε : ℝ => ε ^ (n - k) * C k) (𝓝 0) (𝓝 0) := by
      simpa only [zero_pow (Nat.sub_pos_of_lt hkn).ne', zero_mul] using hcont.tendsto (0 : ℝ)
    exact (hlim.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hδ)
  obtain ⟨ε, hsmall, hε⟩ :=
    (hall.and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one))).exists
  refine ⟨ε, hε.1, hε.2.le, ?_⟩
  intro k hkn x
  calc
    ‖iteratedDeriv k (oneSidedScaledJet n ε g) x‖ =
        ε ^ (n - k) * ‖iteratedDeriv k g (ε⁻¹ * x)‖ := by
      rw [iteratedDeriv_oneSidedScaledJet hg, oneSidedScaledJet_factor hε.1 hkn.le,
        norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hε.1.le _)]
    _ ≤ ε ^ (n - k) * C k :=
      mul_le_mul_of_nonneg_left (hC k _) (pow_nonneg hε.1.le _)
    _ ≤ δ := (hsmall k (Finset.mem_range.mpr hkn)).le

theorem iteratedDeriv_oneSidedScaledJet_zero {ε : ℝ} (hε : 0 < ε)
    (c : ℝ) (n k : ℕ) :
    iteratedDeriv k (oneSidedScaledJet n ε (oneSidedJetBase c n)) 0 =
      if k = n then c else 0 := by
  rw [iteratedDeriv_oneSidedScaledJet (contDiff_oneSidedJetBase c n), mul_zero,
    iteratedDeriv_oneSidedJetBase_zero]
  by_cases hkn : k = n
  · subst k
    simp only [if_pos rfl, oneSidedScaledJet_factor hε le_rfl, Nat.sub_self,
      pow_zero, one_mul]
  · rw [if_neg hkn, mul_zero]

/-- Borel's endpoint-jet construction in one real variable. A single smooth
function realizes every member of an arbitrary sequence of derivatives. -/
theorem exists_contDiff_prescribed_jets (a : ℕ → ℝ) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ ∀ k : ℕ, iteratedDeriv k g 0 = a k := by
  classical
  have hscale (n : ℕ) := exists_oneSidedScaledJet_small
    (contDiff_oneSidedJetBase (a n) n) (hasCompactSupport_oneSidedJetBase (a n) n) n
    (show 0 < (1 / 2 : ℝ) ^ n from pow_pos (by norm_num) _)
  choose ε hε₀ hε₁ hεsmall using hscale
  let f : ℕ → ℝ → ℝ := fun n => oneSidedScaledJet n (ε n) (oneSidedJetBase (a n) n)
  have hf (n : ℕ) : ContDiff ℝ ∞ (f n) :=
    contDiff_oneSidedScaledJet (contDiff_oneSidedJetBase (a n) n) n (ε n)
  choose C hC₀ hC using fun n k : ℕ =>
    exists_compact_iteratedDeriv_bound (contDiff_oneSidedJetBase (a n) n)
      (hasCompactSupport_oneSidedJetBase (a n) n) k
  let v : ℕ → ℕ → ℝ := fun k n =>
    if k < n then (1 / 2 : ℝ) ^ n else
      ‖(ε n) ^ n * ((ε n)⁻¹) ^ k‖ * C n k
  have hv (k : ℕ) : Summable (v k) := by
    have hgeo : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    apply hgeo.congr_atTop
    filter_upwards [eventually_gt_atTop k] with n hn
    simp only [v, if_pos hn]
  have hbound (k n : ℕ) (x : ℝ) : ‖iteratedDeriv k (f n) x‖ ≤ v k n := by
    dsimp only [v]
    split_ifs with hkn
    · exact hεsmall n k hkn x
    · dsimp only [f]
      rw [iteratedDeriv_oneSidedScaledJet (contDiff_oneSidedJetBase (a n) n), norm_mul]
      exact mul_le_mul_of_nonneg_left (hC n k _) (norm_nonneg _)
  have hboundF (k n : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hbound k n x
  refine ⟨fun x => ∑' n, f n x,
    contDiff_tsum (N := ⊤) hf (fun k _ => hv k) (fun k n x _ => hboundF k n x), ?_⟩
  intro k
  have hsum : iteratedDeriv k (fun x => ∑' n, f n x) 0 =
      ∑' n, iteratedDeriv k (f n) 0 := by
    simp only [iteratedDeriv_eq_equiv_comp, Function.comp_apply]
    rw [iteratedFDeriv_tsum (N := ⊤) hf (fun j _ => hv j)
      (fun j n x _ => hboundF j n x) (by simp)]
    exact ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) ℝ).symm.toContinuousLinearEquiv).map_tsum
  rw [hsum]
  have hjet (n : ℕ) : iteratedDeriv k (f n) 0 = if k = n then a n else 0 :=
    iteratedDeriv_oneSidedScaledJet_zero (hε₀ n) (a n) n k
  simp_rw [hjet]
  simp

/-- The flat-extension derivative argument is local at the left endpoint;
no assumption at the other endpoint is necessary. -/
theorem hasDerivAt_extendZeroLeft_Iio
    {a b : ℝ} {f g : ℝ → ℝ} (hab : a < b)
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x)
    (hf : Tendsto f (𝓝[>] a) (𝓝 0)) (hg : Tendsto g (𝓝[>] a) (𝓝 0))
    {x : ℝ} (hx : x < b) :
    HasDerivAt (extendZeroLeft a f) (extendZeroLeft a g x) x := by
  have hd (y : ℝ) (hy : y ∈ Ioo a b) :
      HasDerivAt (extendZeroLeft a f) (g y) y :=
    (hderiv y hy).congr_of_eventuallyEq (extendZeroLeft_eventuallyEq_of_gt f hy.1)
  by_cases hxa : x = a
  · subst x
    have hright : HasDerivWithinAt (extendZeroLeft a f) 0 (Ici a) a := by
      apply hasDerivWithinAt_Ici_of_tendsto_deriv
        (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
        (continuousAt_extendZeroLeft hf).continuousWithinAt (Ioo_mem_nhdsGT hab)
      apply hg.congr'
      filter_upwards [Ioo_mem_nhdsGT hab] with y hy
      exact (hd y hy).deriv.symm
    have hleft : HasDerivWithinAt (extendZeroLeft a f) 0 (Iic a) a := by
      apply (hasDerivWithinAt_const a (Iic a) (0 : ℝ)).congr_of_mem _ self_mem_Iic
      intro y hy
      exact extendZeroLeft_of_le hy
    simpa only [extendZeroLeft_of_le le_rfl, Iic_union_Ici, hasDerivWithinAt_univ]
      using hleft.union hright
  rcases lt_or_gt_of_ne hxa with hxa' | hax
  · simpa only [extendZeroLeft_of_le hxa'.le] using
      (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
        (extendZeroLeft_eventuallyEq_zero_of_lt f hxa')
  · simpa only [extendZeroLeft_of_gt hax] using hd x ⟨hax, hx⟩

/-- Iterated derivatives of a flat extension agree on the whole open set
to the left of the opposite endpoint. -/
theorem iteratedDeriv_extendZeroLeft_Iio
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : ContDiffOn ℝ ∞ f (Ioo a b))
    (hlim : ∀ n : ℕ, Tendsto (iteratedDeriv n f) (𝓝[>] a) (𝓝 0)) (n : ℕ) :
    EqOn (iteratedDeriv n (extendZeroLeft a f))
      (extendZeroLeft a (iteratedDeriv n f)) (Iio b) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]; exact Set.eqOn_refl _ _
  | succ n ih =>
    intro x hx
    rw [iteratedDeriv_succ, ih.deriv isOpen_Iio hx]
    apply HasDerivAt.deriv
    apply hasDerivAt_extendZeroLeft_Iio hab _ (hlim n) (hlim (n + 1)) hx
    intro y hy
    have hd := ((differentiableOn_iteratedDeriv_Ioo hf n y hy).differentiableAt
      (isOpen_Ioo.mem_nhds hy)).hasDerivAt
    simpa only [iteratedDeriv_succ] using hd

/-- All right-hand jets vanishing is enough for a smooth zero extension
across the left endpoint, locally on `(-∞, b)`. -/
theorem contDiffOn_extendZeroLeft_Iio
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : ContDiffOn ℝ ∞ f (Ioo a b))
    (hlim : ∀ n : ℕ, Tendsto (iteratedDeriv n f) (𝓝[>] a) (𝓝 0)) :
    ContDiffOn ℝ ∞ (extendZeroLeft a f) (Iio b) := by
  apply contDiffOn_of_differentiableOn_deriv
  intro n _
  have hd : DifferentiableOn ℝ (extendZeroLeft a (iteratedDeriv n f)) (Iio b) := by
    intro x hx
    apply DifferentiableAt.differentiableWithinAt
    apply HasDerivAt.differentiableAt
    apply hasDerivAt_extendZeroLeft_Iio hab _ (hlim n) (hlim (n + 1)) hx
    intro y hy
    have hdy := ((differentiableOn_iteratedDeriv_Ioo hf n y hy).differentiableAt
      (isOpen_Ioo.mem_nhds hy)).hasDerivAt
    simpa only [iteratedDeriv_succ] using hdy
  apply hd.congr
  intro x hx
  exact (iteratedDerivWithin_of_isOpen isOpen_Iio hx).trans
    (iteratedDeriv_extendZeroLeft_Iio hab hf hlim n hx)

/-- One-sided smoothness supplies actual right-hand limits of every
ordinary derivative; the endpoint values are the within-set jets. -/
theorem tendsto_iteratedDeriv_of_contDiffOn_Ico
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : ContDiffOn ℝ ∞ f (Ico a b))
    (k : ℕ) :
    Tendsto (iteratedDeriv k f) (𝓝[>] a)
      (𝓝 (iteratedDerivWithin k f (Ico a b) a)) := by
  have hc := hf.continuousOn_iteratedDerivWithin (m := k) (by simp) (uniqueDiffOn_Ico a b)
  have hlim := hc a ⟨le_rfl, hab⟩
  rw [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsGE hab] at hlim
  apply (hlim.mono_left (nhdsWithin_mono a Ioi_subset_Ici_self)).congr'
  filter_upwards [Ioo_mem_nhdsGT hab] with x hx
  exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ico a b)
    ((hf.contDiffAt (Ico_mem_nhds_iff.mpr hx)).of_le (by simp))
    (Ioo_subset_Ico_self hx)

/-- A function smooth on a half-open real interval has one genuine smooth
extension across its included endpoint. The extension agrees everywhere
on the original interval, including the endpoint. -/
theorem exists_contDiffOn_Iio_extension_of_Ico
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : ContDiffOn ℝ ∞ f (Ico a b)) :
    ∃ F : ℝ → ℝ, EqOn F f (Ico a b) ∧ ContDiffOn ℝ ∞ F (Iio b) := by
  obtain ⟨g₀, hg₀, hjet₀⟩ := exists_contDiff_prescribed_jets
    (fun k => iteratedDerivWithin k f (Ico a b) a)
  let g : ℝ → ℝ := fun x => g₀ (x - a)
  have hg : ContDiff ℝ ∞ g := hg₀.comp (contDiff_id.sub contDiff_const)
  have hjet (k : ℕ) : iteratedDeriv k g a = iteratedDerivWithin k f (Ico a b) a := by
    dsimp only [g]
    rw [iteratedDeriv_comp_sub_const]
    simpa only [sub_self] using hjet₀ k
  have hga : g a = f a := by
    simpa only [iteratedDeriv_zero, iteratedDerivWithin_zero] using hjet 0
  have hres : ContDiffOn ℝ ∞ (f - g) (Ico a b) := hf.sub hg.contDiffOn
  have hflat (k : ℕ) : Tendsto (iteratedDeriv k (f - g)) (𝓝[>] a) (𝓝 0) := by
    have hzero : iteratedDerivWithin k (f - g) (Ico a b) a = 0 := by
      rw [iteratedDerivWithin_sub (show a ∈ Ico a b from ⟨le_rfl, hab⟩)
        (uniqueDiffOn_Ico a b)
        ((hf a ⟨le_rfl, hab⟩).of_le (by simp))
        (hg.contDiffAt.contDiffWithinAt.of_le (by simp)),
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ico a b)
          (hg.contDiffAt.of_le (by simp)) ⟨le_rfl, hab⟩, hjet, sub_self]
    simpa only [hzero] using tendsto_iteratedDeriv_of_contDiffOn_Ico hab hres k
  let F : ℝ → ℝ := fun x => g x + extendZeroLeft a (f - g) x
  refine ⟨F, ?_, hg.contDiffOn.add (contDiffOn_extendZeroLeft_Iio hab
    (hres.mono Ioo_subset_Ico_self) hflat)⟩
  intro x hx
  dsimp only [F]
  by_cases hax : a < x
  · rw [extendZeroLeft_of_gt hax]
    simp only [Pi.sub_apply, add_sub_cancel]
  · have hxa : x = a := le_antisymm (not_lt.mp hax) hx.1
    subst x
    simpa only [extendZeroLeft_of_le le_rfl, add_zero] using hga

/-- The entrance-facing form: equality on `[a,b)`, full smoothness at `a`,
and smoothness throughout the open interior. -/
theorem exists_contDiffAt_extension_of_Ico
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : ContDiffOn ℝ ∞ f (Ico a b)) :
    ∃ F : ℝ → ℝ, EqOn F f (Ico a b) ∧ ContDiffAt ℝ ∞ F a ∧
      ContDiffOn ℝ ∞ F (Ioo a b) := by
  obtain ⟨F, hF, hFsmooth⟩ := exists_contDiffOn_Iio_extension_of_Ico hab hf
  exact ⟨F, hF, hFsmooth.contDiffAt (isOpen_Iio.mem_nhds hab),
    hFsmooth.mono (fun _ hx => hx.2)⟩

/-- Every smooth extension has exactly the original one-sided endpoint
jets, so choosing the exterior does not change entrance data. -/
theorem iteratedDeriv_eq_within_of_eqOn_Ico
    {a b : ℝ} {F f : ℝ → ℝ} (hab : a < b)
    (hF : ContDiffAt ℝ ∞ F a) (heq : EqOn F f (Ico a b)) (k : ℕ) :
    iteratedDeriv k F a = iteratedDerivWithin k f (Ico a b) a := by
  exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ico a b)
    (hF.of_le (by simp)) ⟨le_rfl, hab⟩).symm.trans
      (iteratedDerivWithin_congr heq ⟨le_rfl, hab⟩)

theorem hasDerivAt_of_smooth_extension_Ico
    {a b d : ℝ} {F f : ℝ → ℝ} (hab : a < b)
    (hF : ContDiffAt ℝ ∞ F a) (heq : EqOn F f (Ico a b))
    (hf : HasDerivWithinAt f d (Ico a b) a) : HasDerivAt F d a := by
  have hd : deriv F a = derivWithin f (Ico a b) a := by
    simpa only [iteratedDeriv_one, iteratedDerivWithin_one] using
      iteratedDeriv_eq_within_of_eqOn_Ico hab hF heq 1
  exact (hF.differentiableAt (by simp)).hasDerivAt.congr_deriv
    (hd.trans (hf.derivWithin (uniqueDiffOn_Ico a b a ⟨le_rfl, hab⟩)))

end ContinuousFlexibility.Analysis
