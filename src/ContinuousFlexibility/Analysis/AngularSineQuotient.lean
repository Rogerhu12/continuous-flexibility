module

public import ContinuousFlexibility.Analysis.AngularTaylorDivision
public import ContinuousFlexibility.Analysis.DoubledSineFactor
public import ContinuousFlexibility.Analysis.LocalMixedProductBounds

/-!
# Actual smooth removal of a sine factor or its square

A single Bool parameter selects the simple and squared numerators. At
each sine zero the removable value is the actual angular Taylor value.
The fixed smooth inverse of sin(2x)/x identifies this definition with a
globally smooth expression on a neighborhood of each zero. No continuity
or differentiability of a prospective stored coefficient is an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def sineFactorOrder (square : Bool) : ℕ := if square then 2 else 1

def sineFactorTaylor (square : Bool) (F : PolarPoint → ℝ) (c : ℝ) : PolarPoint → ℝ :=
  if square then squaredAngularTaylorQuotient F c else angularTaylorQuotient F c

theorem contDiff_sineFactorTaylor {F : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (square : Bool) (c : ℝ) :
    ContDiff ℝ ∞ (sineFactorTaylor square F c) := by
  cases square
  · exact contDiff_angularTaylorQuotient hF c
  · exact contDiff_squaredAngularTaylorQuotient hF c

theorem sineFactorTaylor_factor {F : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (square : Bool) (c : ℝ)
    (hzero : ∀ r : ℝ, F (r, c) = 0)
    (hfirst : square = true → ∀ r : ℝ, mixedDerivative 0 1 F (r, c) = 0)
    (p : PolarPoint) :
    F p = (p.2 - c) ^ sineFactorOrder square * sineFactorTaylor square F c p := by
  cases square
  · simpa only [sineFactorOrder, sineFactorTaylor, Bool.false_eq_true, ↓reduceIte, pow_one]
      using angularTaylorQuotient_factor hF c hzero p
  · exact squaredAngularTaylorQuotient_factor hF c hzero (hfirst rfl) p

def angularSineQuotient (square : Bool) (F : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  if Real.sin (2 * p.2) = 0 then
    (Real.cos (2 * p.2) / 2) ^ sineFactorOrder square *
      sineFactorTaylor square F p.2 p
  else F p / Real.sin (2 * p.2) ^ sineFactorOrder square

private theorem doubledSine_cos_sq {c : ℝ} (hc : Real.sin (2 * c) = 0) :
    Real.cos (2 * c) ^ 2 = 1 := by
  have h := Real.sin_sq_add_cos_sq (2 * c)
  rw [hc, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] at h
  exact h

/-- On the same fixed window at any sine zero, the actual quotient is
the genuine Taylor quotient times a fixed smooth multiplier. -/
theorem angularSineQuotient_eq_local
    {q ψ : ℝ → ℝ} (hq0 : q 0 = 2)
    (hqfactor : ∀ x : ℝ, Real.sin (2 * x) = x * q x)
    (hqpos : ∀ x ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2), 0 < q x)
    (hψq : ∀ x ∈ Icc (-(Real.pi / 3)) (Real.pi / 3), ψ x * q x = 1)
    {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F)
    (square : Bool) (c : ℝ) (hc : Real.sin (2 * c) = 0)
    (hzero : ∀ r : ℝ, F (r, c) = 0)
    (hfirst : square = true → ∀ r : ℝ, mixedDerivative 0 1 F (r, c) = 0)
    {p : PolarPoint}
    (hp : p.2 - c ∈ Ioo (-(Real.pi / 3)) (Real.pi / 3)) :
    angularSineQuotient square F p =
      (Real.cos (2 * c) * ψ (p.2 - c)) ^ sineFactorOrder square *
        sineFactorTaylor square F c p := by
  have hcos := doubledSine_cos_sq hc
  have hcos0 : Real.cos (2 * c) ≠ 0 := by
    intro h
    rw [h] at hcos
    norm_num at hcos
  have hqx : q (p.2 - c) ≠ 0 := by
    apply (hqpos (p.2 - c) ?_).ne'
    constructor <;> linarith [hp.1, hp.2, Real.pi_pos]
  have hsine : Real.sin (2 * p.2) =
      (p.2 - c) * Real.cos (2 * c) * q (p.2 - c) := by
    rw [show 2 * p.2 = 2 * (p.2 - c) + 2 * c by ring,
      Real.sin_add, hc, mul_zero, add_zero, hqfactor]
    ring
  have hψx := hψq (p.2 - c) ⟨hp.1.le, hp.2.le⟩
  have hbase : (Real.cos (2 * c) * ψ (p.2 - c)) * Real.sin (2 * p.2) = p.2 - c := by
    calc
      _ = Real.cos (2 * c) ^ 2 * (ψ (p.2 - c) * q (p.2 - c)) * (p.2 - c) := by
        rw [hsine]
        ring
      _ = _ := by rw [hcos, hψx]; ring
  by_cases hs : Real.sin (2 * p.2) = 0
  · have hx : p.2 = c := by
      have hprod : (p.2 - c) * Real.cos (2 * c) * q (p.2 - c) = 0 :=
        hsine.symm.trans hs
      have hleft : (p.2 - c) * Real.cos (2 * c) = 0 :=
        (mul_eq_zero.mp hprod).resolve_right hqx
      exact sub_eq_zero.mp ((mul_eq_zero.mp hleft).resolve_right hcos0)
    have hψzero : ψ 0 = 1 / 2 := by
      have h := hψq 0 ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      rw [hq0] at h
      linarith
    have hmult : Real.cos (2 * c) * ψ 0 = Real.cos (2 * c) / 2 := by
      rw [hψzero]
      ring
    simp only [angularSineQuotient, hx, if_pos hc, sub_self, hmult]
  · rw [angularSineQuotient, if_neg hs]
    apply (div_eq_iff (pow_ne_zero (sineFactorOrder square) hs)).mpr
    calc
      F p = (p.2 - c) ^ sineFactorOrder square * sineFactorTaylor square F c p :=
        sineFactorTaylor_factor hF square c hzero hfirst p
      _ = ((Real.cos (2 * c) * ψ (p.2 - c)) * Real.sin (2 * p.2)) ^
          sineFactorOrder square * sineFactorTaylor square F c p := by rw [hbase]
      _ = _ := by rw [mul_pow]; ring

/-- The removable definition is genuinely smooth on the full plane.
For the square, only the genuine first angular zero jet is additionally
required at each sine zero. -/
theorem contDiff_angularSineQuotient
    {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) (square : Bool)
    (hzero : ∀ c : ℝ, Real.sin (2 * c) = 0 → ∀ r : ℝ, F (r, c) = 0)
    (hfirst : square = true → ∀ c : ℝ, Real.sin (2 * c) = 0 →
      ∀ r : ℝ, mixedDerivative 0 1 F (r, c) = 0) :
    ContDiff ℝ ∞ (angularSineQuotient square F) := by
  obtain ⟨q, ψ, _, hq0, hqfactor, hqpos, hψ, hψq, _⟩ :=
    exists_doubledSine_factor_and_inverse
  have hsin : ContDiff ℝ ∞ (fun p : PolarPoint => Real.sin (2 * p.2)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : Real.sin (2 * p.2) = 0
  · let c : ℝ := p.2
    have hlocal : ContDiff ℝ ∞ (fun y : PolarPoint =>
        (Real.cos (2 * c) * ψ (y.2 - c)) ^ sineFactorOrder square *
          sineFactorTaylor square F c y) :=
      ((contDiff_const.mul (hψ.comp (contDiff_snd.sub contDiff_const))).pow _).mul
        (contDiff_sineFactorTaylor hF square c)
    have hwindow : {y : PolarPoint | y.2 - c ∈
        Ioo (-(Real.pi / 3)) (Real.pi / 3)} ∈ 𝓝 p := by
      apply (isOpen_Ioo.preimage (continuous_snd.sub continuous_const)).mem_nhds
      change p.2 - p.2 ∈ Ioo (-(Real.pi / 3)) (Real.pi / 3)
      rw [sub_self]
      constructor <;> linarith [Real.pi_pos]
    apply hlocal.contDiffAt.congr_of_eventuallyEq
    filter_upwards [hwindow] with y hy
    exact angularSineQuotient_eq_local hq0 hqfactor hqpos hψq hF square c hp
      (hzero c hp) (fun h => hfirst h c hp) hy
  · have hsopen : IsOpen {y : PolarPoint | Real.sin (2 * y.2) ≠ 0} :=
      isOpen_ne_fun hsin.continuous continuous_const
    have hlocal : ContDiffAt ℝ ∞
        (fun y : PolarPoint => F y / Real.sin (2 * y.2) ^ sineFactorOrder square) p :=
      hF.contDiffAt.div (hsin.contDiffAt.pow _) (pow_ne_zero _ hp)
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [hsopen.mem_nhds hp] with y hy
    simp only [angularSineQuotient, if_neg hy]

/-- The construction removes precisely the requested sine power. -/
theorem angularSineQuotient_factor
    {F : PolarPoint → ℝ} (square : Bool)
    (hzero : ∀ c : ℝ, Real.sin (2 * c) = 0 → ∀ r : ℝ, F (r, c) = 0)
    (p : PolarPoint) :
    F p = Real.sin (2 * p.2) ^ sineFactorOrder square * angularSineQuotient square F p := by
  by_cases hp : Real.sin (2 * p.2) = 0
  · have hz : F p = 0 := hzero p.2 hp p.1
    cases square <;> simp only [sineFactorOrder, Bool.false_eq_true, ↓reduceIte,
      hp, zero_pow (by decide : (2 : ℕ) ≠ 0), pow_one, zero_mul, hz]
  · rw [angularSineQuotient, if_neg hp]
    field_simp [pow_ne_zero (sineFactorOrder square) hp]

end ContinuousFlexibility.Analysis
