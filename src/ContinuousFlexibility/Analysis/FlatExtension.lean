module

public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Flat extension from actual one-sided derivative limits

The endpoint step in §7 (`prop:full-physical-tame`) follows the weighted
estimates: all ordinary derivatives tend to zero at an endpoint. This file
proves the ensuing extension theorem for actual derivatives of functions
with values in an arbitrary real normed space. It does not assume an
extension, endpoint differentiability, or the desired smoothness as data.

Weighted Sobolev embedding and uniform estimates in angle and construction
parameters are separate inputs needed to apply this one-dimensional result
to the manuscript's weighted spaces.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

variable {F : Type*} [NormedAddCommGroup F]

/-- Retain the function to the right of `a` and set it to zero on the left,
including the endpoint. The original value `f a` is irrelevant. -/
def extendZeroLeft (a : ℝ) (f : ℝ → F) (x : ℝ) : F :=
  if a < x then f x else 0

@[simp] theorem extendZeroLeft_of_gt {a x : ℝ} {f : ℝ → F} (hx : a < x) :
    extendZeroLeft a f x = f x := by simp [extendZeroLeft, hx]

@[simp] theorem extendZeroLeft_of_le {a x : ℝ} {f : ℝ → F} (hx : x ≤ a) :
    extendZeroLeft a f x = 0 := by simp [extendZeroLeft, not_lt.mpr hx]

theorem extendZeroLeft_eventuallyEq_of_gt {a x : ℝ} (f : ℝ → F) (hx : a < x) :
    extendZeroLeft a f =ᶠ[𝓝 x] f := by
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact extendZeroLeft_of_gt hy

theorem extendZeroLeft_eventuallyEq_zero_of_lt {a x : ℝ} (f : ℝ → F) (hx : x < a) :
    extendZeroLeft a f =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
  exact extendZeroLeft_of_le hy.le

/-- A genuine one-sided zero limit makes the chosen zero extension
continuous at the endpoint, regardless of the original endpoint value. -/
theorem continuousAt_extendZeroLeft {a : ℝ} {f : ℝ → F}
    (hlim : Tendsto f (𝓝[>] a) (𝓝 0)) : ContinuousAt (extendZeroLeft a f) a := by
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · simp only [ContinuousWithinAt, extendZeroLeft_of_le le_rfl]
    have heq : (fun _ : ℝ => (0 : F)) =ᶠ[𝓝[<] a] extendZeroLeft a f := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (extendZeroLeft_of_le hx.le).symm
    exact tendsto_const_nhds.congr' heq
  · simp only [ContinuousWithinAt, extendZeroLeft_of_le le_rfl]
    have heq : f =ᶠ[𝓝[>] a] extendZeroLeft a f := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (extendZeroLeft_of_gt hx).symm
    exact hlim.congr' heq

variable [NormedSpace ℝ F]

/-- Differentiation commutes with the actual zero extension when both the
function and its actual derivative have zero one-sided limits. -/
theorem hasDerivAt_extendZeroLeft
    {a : ℝ} {f g : ℝ → F}
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt f (g x) x)
    (hf : Tendsto f (𝓝[>] a) (𝓝 0)) (hg : Tendsto g (𝓝[>] a) (𝓝 0)) (x : ℝ) :
    HasDerivAt (extendZeroLeft a f) (extendZeroLeft a g x) x := by
  apply hasDerivAt_of_hasDerivAt_of_ne' (x := a) _
    (continuousAt_extendZeroLeft hf) (continuousAt_extendZeroLeft hg) x
  intro y hya
  rcases lt_or_gt_of_ne hya with hy | hy
  · simpa only [extendZeroLeft_of_le hy.le] using
      (hasDerivAt_const y (0 : F)).congr_of_eventuallyEq
        (extendZeroLeft_eventuallyEq_zero_of_lt f hy)
  · simpa only [extendZeroLeft_of_gt hy] using
      (hderiv y hy).congr_of_eventuallyEq (extendZeroLeft_eventuallyEq_of_gt f hy)

/-- Interior smoothness supplies differentiability of every actual
ordinary derivative on the open half-axis. -/
theorem differentiableOn_iteratedDeriv_Ioi
    {a : ℝ} {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Ioi a)) (n : ℕ) :
    DifferentiableOn ℝ (iteratedDeriv n f) (Ioi a) := by
  apply (hf.differentiableOn_iteratedDerivWithin (m := n)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
    isOpen_Ioi.uniqueDiffOn).congr
  intro x hx
  exact (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm

/-- Every derivative of the zero extension is exactly the zero extension
of the corresponding actual derivative. This includes order zero. -/
theorem iteratedDeriv_extendZeroLeft
    {a : ℝ} {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Ioi a))
    (hlim : ∀ n : ℕ, Tendsto (iteratedDeriv n f) (𝓝[>] a) (𝓝 0)) (n : ℕ) :
    iteratedDeriv n (extendZeroLeft a f) = extendZeroLeft a (iteratedDeriv n f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    apply HasDerivAt.deriv
    apply hasDerivAt_extendZeroLeft _ (hlim n) (hlim (n + 1))
    intro y hy
    have hd := ((differentiableOn_iteratedDeriv_Ioi hf n y hy).differentiableAt
      (isOpen_Ioi.mem_nhds hy)).hasDerivAt
    simpa only [iteratedDeriv_succ] using hd

/-- Actual `C∞` flat extension from actual one-sided limits of all
ordinary derivatives. No differentiability at the endpoint is assumed. -/
theorem contDiff_extendZeroLeft
    {a : ℝ} {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Ioi a))
    (hlim : ∀ n : ℕ, Tendsto (iteratedDeriv n f) (𝓝[>] a) (𝓝 0)) :
    ContDiff ℝ ∞ (extendZeroLeft a f) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [iteratedDeriv_extendZeroLeft hf hlim n]
  intro x
  apply HasDerivAt.differentiableAt
  apply hasDerivAt_extendZeroLeft _ (hlim n) (hlim (n + 1)) x
  intro y hy
  have hd := ((differentiableOn_iteratedDeriv_Ioi hf n y hy).differentiableAt
    (isOpen_Ioi.mem_nhds hy)).hasDerivAt
  simpa only [iteratedDeriv_succ] using hd

theorem iteratedDeriv_extendZeroLeft_eq_zero
    {a x : ℝ} {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Ioi a))
    (hlim : ∀ n : ℕ, Tendsto (iteratedDeriv n f) (𝓝[>] a) (𝓝 0))
    (hx : x ≤ a) (n : ℕ) : iteratedDeriv n (extendZeroLeft a f) x = 0 := by
  rw [iteratedDeriv_extendZeroLeft hf hlim n]
  exact extendZeroLeft_of_le hx

/-- Constant extension is obtained by extending the actual deviation from
the endpoint constant. -/
def extendConstantLeft (a : ℝ) (c : F) (f : ℝ → F) (x : ℝ) : F :=
  c + extendZeroLeft a (fun y => f y - c) x

theorem contDiff_extendConstantLeft
    {a : ℝ} {c : F} {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Ioi a))
    (hlim : ∀ n : ℕ,
      Tendsto (iteratedDeriv n (fun x => f x - c)) (𝓝[>] a) (𝓝 0)) :
    ContDiff ℝ ∞ (extendConstantLeft a c f) :=
  contDiff_const.add (contDiff_extendZeroLeft (hf.sub contDiffOn_const) hlim)

omit [NormedSpace ℝ F] in
theorem extendConstantLeft_of_le {a x : ℝ} {c : F} {f : ℝ → F} (hx : x ≤ a) :
    extendConstantLeft a c f x = c := by
  simp [extendConstantLeft, extendZeroLeft_of_le hx]

omit [NormedSpace ℝ F] in
theorem extendConstantLeft_of_gt {a x : ℝ} {c : F} {f : ℝ → F} (hx : a < x) :
    extendConstantLeft a c f x = f x := by
  simp [extendConstantLeft, extendZeroLeft_of_gt hx]

theorem iteratedDeriv_extendConstantLeft_eq_zero
    {a x : ℝ} {c : F} {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Ioi a))
    (hlim : ∀ n : ℕ,
      Tendsto (iteratedDeriv n (fun x => f x - c)) (𝓝[>] a) (𝓝 0))
    (hx : x ≤ a) {n : ℕ} (hn : 0 < n) :
    iteratedDeriv n (extendConstantLeft a c f) x = 0 := by
  unfold extendConstantLeft
  rw [iteratedDeriv_const_add hn]
  exact iteratedDeriv_extendZeroLeft_eq_zero (hf.sub contDiffOn_const) hlim hx n

/-- The actual zero extension from a bounded open interval. Both original
endpoint values and all values outside the interval are discarded. -/
def extendZeroOutside (a b : ℝ) (f : ℝ → F) (x : ℝ) : F :=
  if x ∈ Ioo a b then f x else 0

omit [NormedSpace ℝ F] in
@[simp] theorem extendZeroOutside_of_mem {a b x : ℝ} {f : ℝ → F}
    (hx : x ∈ Ioo a b) : extendZeroOutside a b f x = f x := by
  simp [extendZeroOutside, hx]

omit [NormedSpace ℝ F] in
@[simp] theorem extendZeroOutside_of_notMem {a b x : ℝ} {f : ℝ → F}
    (hx : x ∉ Ioo a b) : extendZeroOutside a b f x = 0 := by
  simp [extendZeroOutside, hx]

omit [NormedSpace ℝ F] in
theorem extendZeroOutside_eventuallyEq_of_mem {a b x : ℝ} (f : ℝ → F)
    (hx : x ∈ Ioo a b) : extendZeroOutside a b f =ᶠ[𝓝 x] f := by
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact extendZeroOutside_of_mem hy

omit [NormedSpace ℝ F] in
theorem extendZeroOutside_eventuallyEq_zero_of_lt {a b x : ℝ} (f : ℝ → F)
    (hx : x < a) : extendZeroOutside a b f =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
  exact extendZeroOutside_of_notMem (fun h => (not_lt.mpr hy.le) h.1)

omit [NormedSpace ℝ F] in
theorem extendZeroOutside_eventuallyEq_zero_of_gt {a b x : ℝ} (f : ℝ → F)
    (hx : b < x) : extendZeroOutside a b f =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact extendZeroOutside_of_notMem (fun h => (not_lt.mpr hy.le) h.2)

omit [NormedSpace ℝ F] in
theorem continuousAt_extendZeroOutside_left
    {a b : ℝ} {f : ℝ → F} (hab : a < b)
    (hlim : Tendsto f (𝓝[>] a) (𝓝 0)) : ContinuousAt (extendZeroOutside a b f) a := by
  have ha : extendZeroOutside a b f a = 0 :=
    extendZeroOutside_of_notMem (by simp)
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · simp only [ContinuousWithinAt, ha]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (extendZeroOutside_of_notMem (fun h => (not_lt.mpr hx.le) h.1)).symm
  · simp only [ContinuousWithinAt, ha]
    apply hlim.congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx
    exact (extendZeroOutside_of_mem hx).symm

omit [NormedSpace ℝ F] in
theorem continuousAt_extendZeroOutside_right
    {a b : ℝ} {f : ℝ → F} (hab : a < b)
    (hlim : Tendsto f (𝓝[<] b) (𝓝 0)) : ContinuousAt (extendZeroOutside a b f) b := by
  have hb : extendZeroOutside a b f b = 0 :=
    extendZeroOutside_of_notMem (by simp)
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · simp only [ContinuousWithinAt, hb]
    apply hlim.congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with x hx
    exact (extendZeroOutside_of_mem hx).symm
  · simp only [ContinuousWithinAt, hb]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (extendZeroOutside_of_notMem (fun h => (not_lt.mpr hx.le) h.2)).symm

/-- Both endpoint derivatives are proved by one-sided derivative limits
and the constant derivative on the exterior half-axis. -/
theorem hasDerivAt_extendZeroOutside
    {a b : ℝ} {f g : ℝ → F} (hab : a < b)
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 0)) (hfb : Tendsto f (𝓝[<] b) (𝓝 0))
    (hga : Tendsto g (𝓝[>] a) (𝓝 0)) (hgb : Tendsto g (𝓝[<] b) (𝓝 0)) (x : ℝ) :
    HasDerivAt (extendZeroOutside a b f) (extendZeroOutside a b g x) x := by
  have hd (y : ℝ) (hy : y ∈ Ioo a b) :
      HasDerivAt (extendZeroOutside a b f) (g y) y :=
    (hderiv y hy).congr_of_eventuallyEq (extendZeroOutside_eventuallyEq_of_mem f hy)
  have hdiff : DifferentiableOn ℝ (extendZeroOutside a b f) (Ioo a b) :=
    fun y hy => (hd y hy).differentiableAt.differentiableWithinAt
  by_cases hxa : x = a
  · subst x
    have hright : HasDerivWithinAt (extendZeroOutside a b f) 0 (Ici a) a := by
      apply hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
        (continuousAt_extendZeroOutside_left hab hfa).continuousWithinAt
        (Ioo_mem_nhdsGT hab)
      apply hga.congr'
      filter_upwards [Ioo_mem_nhdsGT hab] with y hy
      exact (hd y hy).deriv.symm
    have hleft : HasDerivWithinAt (extendZeroOutside a b f) 0 (Iic a) a := by
      apply (hasDerivWithinAt_const a (Iic a) (0 : F)).congr_of_mem _ self_mem_Iic
      intro y hy
      exact extendZeroOutside_of_notMem (fun h => (not_lt.mpr hy) h.1)
    simpa using hleft.union hright
  by_cases hxb : x = b
  · subst x
    have hleft : HasDerivWithinAt (extendZeroOutside a b f) 0 (Iic b) b := by
      apply hasDerivWithinAt_Iic_of_tendsto_deriv hdiff
        (continuousAt_extendZeroOutside_right hab hfb).continuousWithinAt
        (Ioo_mem_nhdsLT hab)
      apply hgb.congr'
      filter_upwards [Ioo_mem_nhdsLT hab] with y hy
      exact (hd y hy).deriv.symm
    have hright : HasDerivWithinAt (extendZeroOutside a b f) 0 (Ici b) b := by
      apply (hasDerivWithinAt_const b (Ici b) (0 : F)).congr_of_mem _ self_mem_Ici
      intro y hy
      exact extendZeroOutside_of_notMem (fun h => (not_lt.mpr hy) h.2)
    simpa using hleft.union hright
  by_cases hax : a < x
  · by_cases hxb' : x < b
    · simpa only [extendZeroOutside_of_mem ⟨hax, hxb'⟩] using hd x ⟨hax, hxb'⟩
    · have hbx : b < x := lt_of_le_of_ne (not_lt.mp hxb') (Ne.symm hxb)
      simpa [extendZeroOutside, not_lt.mpr hbx.le] using
        (hasDerivAt_const x (0 : F)).congr_of_eventuallyEq
          (extendZeroOutside_eventuallyEq_zero_of_gt f hbx)
  · have hxa' : x < a := lt_of_le_of_ne (not_lt.mp hax) hxa
    simpa [extendZeroOutside, not_lt.mpr hxa'.le] using
      (hasDerivAt_const x (0 : F)).congr_of_eventuallyEq
        (extendZeroOutside_eventuallyEq_zero_of_lt f hxa')

theorem differentiableOn_iteratedDeriv_Ioo
    {a b : ℝ} {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Ioo a b)) (n : ℕ) :
    DifferentiableOn ℝ (iteratedDeriv n f) (Ioo a b) := by
  apply (hf.differentiableOn_iteratedDerivWithin (m := n)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n) isOpen_Ioo.uniqueDiffOn).congr
  intro x hx
  exact (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm

theorem iteratedDeriv_extendZeroOutside
    {a b : ℝ} {f : ℝ → F} (hab : a < b) (hf : ContDiffOn ℝ ∞ f (Ioo a b))
    (hleft : ∀ n : ℕ, Tendsto (iteratedDeriv n f) (𝓝[>] a) (𝓝 0))
    (hright : ∀ n : ℕ, Tendsto (iteratedDeriv n f) (𝓝[<] b) (𝓝 0)) (n : ℕ) :
    iteratedDeriv n (extendZeroOutside a b f) =
      extendZeroOutside a b (iteratedDeriv n f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    apply HasDerivAt.deriv
    apply hasDerivAt_extendZeroOutside hab _
      (hleft n) (hright n) (hleft (n + 1)) (hright (n + 1))
    intro y hy
    have hd := ((differentiableOn_iteratedDeriv_Ioo hf n y hy).differentiableAt
      (isOpen_Ioo.mem_nhds hy)).hasDerivAt
    simpa only [iteratedDeriv_succ] using hd

/-- A function smooth only in a bounded open interval, whose actual
derivatives of every order tend to zero at both ends, has a genuine smooth
zero extension on all of `ℝ`. -/
theorem contDiff_extendZeroOutside
    {a b : ℝ} {f : ℝ → F} (hab : a < b) (hf : ContDiffOn ℝ ∞ f (Ioo a b))
    (hleft : ∀ n : ℕ, Tendsto (iteratedDeriv n f) (𝓝[>] a) (𝓝 0))
    (hright : ∀ n : ℕ, Tendsto (iteratedDeriv n f) (𝓝[<] b) (𝓝 0)) :
    ContDiff ℝ ∞ (extendZeroOutside a b f) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [iteratedDeriv_extendZeroOutside hab hf hleft hright n]
  intro x
  apply HasDerivAt.differentiableAt
  apply hasDerivAt_extendZeroOutside hab _
    (hleft n) (hright n) (hleft (n + 1)) (hright (n + 1)) x
  intro y hy
  have hd := ((differentiableOn_iteratedDeriv_Ioo hf n y hy).differentiableAt
    (isOpen_Ioo.mem_nhds hy)).hasDerivAt
  simpa only [iteratedDeriv_succ] using hd

theorem iteratedDeriv_extendZeroOutside_eq_zero
    {a b x : ℝ} {f : ℝ → F} (hab : a < b) (hf : ContDiffOn ℝ ∞ f (Ioo a b))
    (hleft : ∀ n : ℕ, Tendsto (iteratedDeriv n f) (𝓝[>] a) (𝓝 0))
    (hright : ∀ n : ℕ, Tendsto (iteratedDeriv n f) (𝓝[<] b) (𝓝 0))
    (hx : x ∉ Ioo a b) (n : ℕ) : iteratedDeriv n (extendZeroOutside a b f) x = 0 := by
  rw [iteratedDeriv_extendZeroOutside hab hf hleft hright n]
  exact extendZeroOutside_of_notMem hx

/-- Keep a globally smooth reference outside the interval, and extend the
flat deviation by zero. This is the form needed for a height with two
possibly different endpoint constants: the reference may be a smooth
endpoint step with those constants. -/
def extendByReference (a b : ℝ) (g f : ℝ → F) (x : ℝ) : F :=
  g x + extendZeroOutside a b (fun y => f y - g y) x

theorem contDiff_extendByReference
    {a b : ℝ} {f g : ℝ → F} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f (Ioo a b)) (hg : ContDiff ℝ ∞ g)
    (hleft : ∀ n : ℕ,
      Tendsto (iteratedDeriv n (fun x => f x - g x)) (𝓝[>] a) (𝓝 0))
    (hright : ∀ n : ℕ,
      Tendsto (iteratedDeriv n (fun x => f x - g x)) (𝓝[<] b) (𝓝 0)) :
    ContDiff ℝ ∞ (extendByReference a b g f) :=
  hg.add (contDiff_extendZeroOutside hab (hf.sub hg.contDiffOn) hleft hright)

omit [NormedSpace ℝ F] in
theorem extendByReference_of_mem {a b x : ℝ} {f g : ℝ → F} (hx : x ∈ Ioo a b) :
    extendByReference a b g f x = f x := by
  simp [extendByReference, extendZeroOutside_of_mem hx]

omit [NormedSpace ℝ F] in
theorem extendByReference_of_notMem {a b x : ℝ} {f g : ℝ → F} (hx : x ∉ Ioo a b) :
    extendByReference a b g f x = g x := by
  simp [extendByReference, extendZeroOutside_of_notMem hx]

/-- Every actual jet of the extension agrees with the reference at both
endpoints and everywhere outside the original interval. -/
theorem iteratedDeriv_extendByReference_eq
    {a b x : ℝ} {f g : ℝ → F} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f (Ioo a b)) (hg : ContDiff ℝ ∞ g)
    (hleft : ∀ n : ℕ,
      Tendsto (iteratedDeriv n (fun x => f x - g x)) (𝓝[>] a) (𝓝 0))
    (hright : ∀ n : ℕ,
      Tendsto (iteratedDeriv n (fun x => f x - g x)) (𝓝[<] b) (𝓝 0))
    (hx : x ∉ Ioo a b) (n : ℕ) :
    iteratedDeriv n (extendByReference a b g f) x = iteratedDeriv n g x := by
  have hext := contDiff_extendZeroOutside hab (hf.sub hg.contDiffOn) hleft hright
  unfold extendByReference
  rw [iteratedDeriv_fun_add (hg.contDiffAt.of_le (by simp))
    (hext.contDiffAt.of_le (by simp)),
    iteratedDeriv_extendZeroOutside_eq_zero hab (hf.sub hg.contDiffOn) hleft hright hx n,
    add_zero]

end ContinuousFlexibility.Analysis
