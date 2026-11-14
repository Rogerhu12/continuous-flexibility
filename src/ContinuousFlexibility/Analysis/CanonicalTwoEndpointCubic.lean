module

public import ContinuousFlexibility.Analysis.CanonicalCubicPointwise
public import ContinuousFlexibility.Analysis.TransmissionJetAlgebra

/-!
# Cubic division at both endpoints

Dividing first at the left endpoint and then at the reflected right endpoint
gives a smooth quotient by `x³ (R-x)³`.  Six derivatives of the numerator
control every requested derivative of the quotient, with constant `1 / 36`
independent of the interval length.  All three vanishing jets at both
endpoints are explicit hypotheses.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

/-- Removing the cubic zero at the origin preserves every vanishing jet at
any other point.  The proof cancels the nonzero multiplier `x³` jet by jet. -/
theorem cubicQuotient_zero_jet_of_zero_jets
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0) (hf2 : iteratedDeriv 2 f 0 = 0)
    {x : ℝ} (hx : x ≠ 0) (n : ℕ) :
    (∀ i : ℕ, i ≤ n → iteratedDeriv i f x = 0) →
      iteratedDeriv n (cubicQuotient f) x = 0 := by
  have hq : ContDiff ℝ ∞ (cubicQuotient f) := contDiff_cubicQuotient hf hf0 hf1 hf2
  have ha : ContDiff ℝ ∞ (fun y : ℝ => y ^ 3) := contDiff_id.pow 3
  have hfactor : (fun y : ℝ => y ^ 3 * cubicQuotient f y) = f :=
    funext (cube_mul_cubicQuotient hf0)
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hvan
      have hprod :
          iteratedDeriv n (fun y : ℝ => y ^ 3 * cubicQuotient f y) x =
            iteratedDeriv n (fun y : ℝ => y ^ 3 * (0 : ℝ)) x := by
        rw [hfactor]
        simpa only [mul_zero, iteratedDeriv_fun_const_zero] using hvan n le_rfl
      have h := iteratedDeriv_eq_of_mul_eq_of_lower_jets
        (a := fun y : ℝ => y ^ 3) (f := cubicQuotient f) (g := fun _ : ℝ => 0)
        ha hq contDiff_const n (pow_ne_zero 3 hx)
        (fun i hi => by
          have hi0 := ih i hi (fun j hj => hvan j (hj.trans hi.le))
          simpa only [iteratedDeriv_fun_const_zero] using hi0)
        hprod
      simpa only [iteratedDeriv_fun_const_zero] using h

/-- Reflection changes the sign of an odd derivative but preserves its
absolute value at every order. -/
theorem abs_iteratedDeriv_comp_const_sub (f : ℝ → ℝ) (R : ℝ) (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (fun t : ℝ => f (R - t)) x| =
      |iteratedDeriv n f (R - x)| := by
  rw [iteratedDeriv_comp_const_sub]
  simp only [smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

private theorem scalar_cubic_boundary_jets {f : ℝ → ℝ}
    (h : ∀ i : ℕ, i ≤ 2 → iteratedDeriv i f 0 = 0) :
    f 0 = 0 ∧ deriv f 0 = 0 ∧ iteratedDeriv 2 f 0 = 0 := by
  refine ⟨?_, ?_, h 2 le_rfl⟩
  · simpa only [iteratedDeriv_zero] using h 0 (by decide)
  · simpa only [iteratedDeriv_one] using h 1 (by decide)

private theorem reflected_cubicQuotient_boundary_jets
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0) (hf2 : iteratedDeriv 2 f 0 = 0)
    {R : ℝ} (hR : 0 < R)
    (hjets : ∀ i : ℕ, i ≤ 2 → iteratedDeriv i f R = 0) :
    (∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun t : ℝ => cubicQuotient f (R - t)) 0 = 0) := by
  intro i hi
  have hqi := cubicQuotient_zero_jet_of_zero_jets hf hf0 hf1 hf2 hR.ne' i
    (fun j hj => hjets j (hj.trans hi))
  rw [iteratedDeriv_comp_const_sub]
  simp only [sub_zero, hqi, smul_zero]

/-- Sequentially remove the cubic zero at zero and at the reflected right
endpoint.  This definition includes the smooth removable endpoint values. -/
def twoEndpointCubicQuotient (f : ℝ → ℝ) (R x : ℝ) : ℝ :=
  cubicQuotient (fun t : ℝ => cubicQuotient f (R - t)) (R - x)

/-- On the open interval, the regularization is the actual quotient by the
cube of the endpoint-distance product. -/
theorem twoEndpointCubicQuotient_eq_div (f : ℝ → ℝ) {R x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) R) :
    twoEndpointCubicQuotient f R x = f x / (x * (R - x)) ^ 3 := by
  unfold twoEndpointCubicQuotient
  rw [cubicQuotient, ite_eq_right (sub_pos.mpr hx.2).ne']
  have hreflect : R - (R - x) = x := by ring
  rw [hreflect, cubicQuotient, ite_eq_right hx.1.ne', div_div, ← mul_pow]

/-- The regularized two-endpoint quotient is globally smooth. -/
theorem contDiff_twoEndpointCubicQuotient {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {R : ℝ} (hR : 0 < R)
    (hleft : ∀ i : ℕ, i ≤ 2 → iteratedDeriv i f 0 = 0)
    (hright : ∀ i : ℕ, i ≤ 2 → iteratedDeriv i f R = 0) :
    ContDiff ℝ ∞ (twoEndpointCubicQuotient f R) := by
  obtain ⟨hf0, hf1, hf2⟩ := scalar_cubic_boundary_jets hleft
  have hq : ContDiff ℝ ∞ (cubicQuotient f) := contDiff_cubicQuotient hf hf0 hf1 hf2
  have hg : ContDiff ℝ ∞ (fun t : ℝ => cubicQuotient f (R - t)) :=
    hq.comp (contDiff_const.sub contDiff_id)
  obtain ⟨hg0, hg1, hg2⟩ := scalar_cubic_boundary_jets
    (reflected_cubicQuotient_boundary_jets hf hf0 hf1 hf2 hR hright)
  exact (contDiff_cubicQuotient hg hg0 hg1 hg2).comp (contDiff_const.sub contDiff_id)

/-- The two endpoint divisions cost six derivatives, with no additional
inverse power of the interval length in the bound. -/
theorem abs_iteratedDeriv_twoEndpointCubicQuotient_le
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {R : ℝ} (hR : 0 < R)
    (hleft : ∀ i : ℕ, i ≤ 2 → iteratedDeriv i f 0 = 0)
    (hright : ∀ i : ℕ, i ≤ 2 → iteratedDeriv i f R = 0)
    (s : ℕ) {M y : ℝ}
    (hbound : ∀ x ∈ Icc (0 : ℝ) R, |iteratedDeriv (s + 6) f x| ≤ M)
    (hy : y ∈ Icc (0 : ℝ) R) :
    |iteratedDeriv s (twoEndpointCubicQuotient f R) y| ≤ M / 36 := by
  obtain ⟨hf0, hf1, hf2⟩ := scalar_cubic_boundary_jets hleft
  let g : ℝ → ℝ := fun t => cubicQuotient f (R - t)
  have hq : ContDiff ℝ ∞ (cubicQuotient f) := contDiff_cubicQuotient hf hf0 hf1 hf2
  have hg : ContDiff ℝ ∞ g := hq.comp (contDiff_const.sub contDiff_id)
  obtain ⟨hg0, hg1, hg2⟩ := scalar_cubic_boundary_jets
    (reflected_cubicQuotient_boundary_jets hf hf0 hf1 hf2 hR hright)
  have hgbound : ∀ x ∈ Icc (0 : ℝ) R, |iteratedDeriv (s + 3) g x| ≤ M / 6 := by
    intro x hx
    change |iteratedDeriv (s + 3) (fun t => cubicQuotient f (R - t)) x| ≤ M / 6
    rw [abs_iteratedDeriv_comp_const_sub]
    apply abs_iteratedDeriv_cubicQuotient_le_sixth hf hf0 hf1 hf2 (s + 3)
    · intro t ht
      simpa only [Nat.add_assoc] using hbound t ht
    · exact ⟨sub_nonneg.mpr hx.2, sub_le_self _ hx.1⟩
  change |iteratedDeriv s (fun x => cubicQuotient g (R - x)) y| ≤ M / 36
  rw [abs_iteratedDeriv_comp_const_sub]
  calc
    |iteratedDeriv s (cubicQuotient g) (R - y)| ≤ (M / 6) / 6 :=
      abs_iteratedDeriv_cubicQuotient_le_sixth hg hg0 hg1 hg2 s hgbound
        ⟨sub_nonneg.mpr hy.2, sub_le_self _ hy.1⟩
    _ = M / 36 := by ring

/-- The same regularization on an arbitrary ordered interval. -/
def intervalCubicQuotient (f : ℝ → ℝ) (l r x : ℝ) : ℝ :=
  twoEndpointCubicQuotient (fun y : ℝ => f (l + y)) (r - l) (x - l)

theorem intervalCubicQuotient_eq_div (f : ℝ → ℝ) {l r x : ℝ} (hx : x ∈ Ioo l r) :
    intervalCubicQuotient f l r x = f x / ((x - l) * (r - x)) ^ 3 := by
  unfold intervalCubicQuotient
  rw [twoEndpointCubicQuotient_eq_div _
    (show x - l ∈ Ioo (0 : ℝ) (r - l) from
      ⟨sub_pos.mpr hx.1, sub_lt_sub_right hx.2 l⟩)]
  have hleft : l + (x - l) = x := by ring
  have hright : (r - l) - (x - l) = r - x := by ring
  rw [hleft, hright]

/-- Translation to the actual component endpoints preserves the estimate.
The only geometric condition is `l < r`; no width lower bound is imposed. -/
theorem abs_iteratedDeriv_intervalCubicQuotient_le
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {l r : ℝ} (hlr : l < r)
    (hleft : ∀ i : ℕ, i ≤ 2 → iteratedDeriv i f l = 0)
    (hright : ∀ i : ℕ, i ≤ 2 → iteratedDeriv i f r = 0)
    (s : ℕ) {M y : ℝ}
    (hbound : ∀ x ∈ Icc l r, |iteratedDeriv (s + 6) f x| ≤ M)
    (hy : y ∈ Icc l r) :
    |iteratedDeriv s (intervalCubicQuotient f l r) y| ≤ M / 36 := by
  let g : ℝ → ℝ := fun t => f (l + t)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  have hgl : ∀ i : ℕ, i ≤ 2 → iteratedDeriv i g 0 = 0 := by
    intro i hi
    simpa only [g, iteratedDeriv_comp_const_add, add_zero] using hleft i hi
  have hgr : ∀ i : ℕ, i ≤ 2 → iteratedDeriv i g (r - l) = 0 := by
    intro i hi
    have hsum : l + (r - l) = r := by ring
    simpa only [g, iteratedDeriv_comp_const_add, hsum] using hright i hi
  have hgb : ∀ x ∈ Icc (0 : ℝ) (r - l), |iteratedDeriv (s + 6) g x| ≤ M := by
    intro x hx
    have hmem : l + x ∈ Icc l r := by constructor <;> linarith [hx.1, hx.2]
    simpa only [g, iteratedDeriv_comp_const_add] using hbound (l + x) hmem
  change |iteratedDeriv s (fun x => twoEndpointCubicQuotient g (r - l) (x - l)) y| ≤ M / 36
  rw [iteratedDeriv_comp_sub_const]
  exact abs_iteratedDeriv_twoEndpointCubicQuotient_le hg (sub_pos.mpr hlr) hgl hgr s hgb
    ⟨sub_nonneg.mpr hy.1, sub_le_sub_right hy.2 l⟩

end ContinuousFlexibility.Analysis
