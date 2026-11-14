module

public import ContinuousFlexibility.Radial.BufferLocalPrimitive
public import ContinuousFlexibility.Radial.PositiveBufferRegularity

/-!
# Local regularity of the actual weak Schrödinger equation

The weak energy domain supplies a first weak derivative.  Applying the
one-dimensional primitive theorem twice turns a weak equation with a
continuous source into a classical equation. Smooth coefficients and source
then give the smooth representatives required by positive-buffer surgery.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- The local weak equation uses the actual compactly supported tests. -/
def PositiveBufferLocalWeakEquation (V : ℝ → ℝ) (u : RadialL2)
    (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ Ioo a b →
    (∫ x : ℝ, f x * φ x) = ∫ x : ℝ, u x * (-deriv (deriv φ) x + V x * φ x)

/-- The differential equation identifies the second weak derivative. -/
theorem positiveBuffer_second_weak_derivative {V f U : ℝ → ℝ}
    {u d : RadialL2} {a b : ℝ}
    (hV : Continuous V) (hf : Continuous f) (hU : Continuous U)
    (hue : (u : ℝ → ℝ) =ᵐ[volume] U) (hud : WeakRadialDerivative u d)
    (heq : PositiveBufferLocalWeakEquation V u f a b)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ioo a b) :
    (∫ x : ℝ, d x * deriv φ x) = -(∫ x : ℝ, (V x * U x - f x) * φ x) := by
  have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
  have hφ'' := (contDiff_infty_iff_deriv.mp hφ').2
  have huLI := (Lp.memLp u).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  have huφ'' : Integrable (fun x : ℝ => u x * deriv (deriv φ) x) volume := by
    simpa only [smul_eq_mul] using
      huLI.integrable_smul_right_of_hasCompactSupport hφ''.continuous hcφ.deriv.deriv
  have hVUφ : Integrable (fun x : ℝ => V x * U x * φ x) volume :=
    ((hV.mul hU).mul hφ.continuous).integrable_of_hasCompactSupport hcφ.mul_left
  have hfφ : Integrable (fun x : ℝ => f x * φ x) volume :=
    (hf.mul hφ.continuous).integrable_of_hasCompactSupport hcφ.mul_left
  have htest := heq φ hφ hcφ hsφ
  have hfirst := hud (deriv φ) hφ' hcφ.deriv
  have hsplit : (∫ x : ℝ, u x * (-deriv (deriv φ) x + V x * φ x)) =
      -(∫ x : ℝ, u x * deriv (deriv φ) x) + ∫ x : ℝ, V x * U x * φ x := by
    calc
      _ = ∫ x : ℝ, -(u x * deriv (deriv φ) x) + V x * U x * φ x := by
        apply integral_congr_ae
        filter_upwards [hue] with x hx
        rw [hx]
        ring
      _ = _ := by
        have hn : Integrable (fun x : ℝ => -(u x * deriv (deriv φ) x)) volume := by
          apply huφ''.neg.congr
          filter_upwards [] with x
          exact Pi.neg_apply (fun y : ℝ => u y * deriv (deriv φ) y) x
        rw [integral_add hn hVUφ, integral_neg]
  have hsource : (∫ x : ℝ, (V x * U x - f x) * φ x) =
      (∫ x : ℝ, V x * U x * φ x) - ∫ x : ℝ, f x * φ x := by
    simp_rw [sub_mul]
    exact integral_sub hVUφ hfφ
  rw [hsplit, hfirst] at htest
  rw [hsource]
  linarith

/-- A continuous energy representative and the local weak equation produce
two actual classical derivatives. No choice of an `L²` representative is
treated as pointwise differentiable. -/
theorem positiveBuffer_local_classical_representative {V f : ℝ → ℝ}
    {u d : RadialL2} {a b : ℝ} (hab : a < b)
    (hV : Continuous V) (hf : Continuous f) (hud : WeakRadialDerivative u d)
    (heq : PositiveBufferLocalWeakEquation V u f a b) :
    ∃ U D : ℝ → ℝ, Continuous U ∧ Continuous D ∧
      (u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] U ∧
      (d : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] D ∧
      (∀ x ∈ Ioo a b, HasDerivAt U (D x) x) ∧
      (∀ x ∈ Ioo a b, HasDerivAt D (V x * U x - f x) x) := by
  obtain ⟨U₀, hU₀, hu₀, _, _⟩ := buffer_weakDerivative_continuousRepresentative hud
  let q (x : ℝ) := V x * U₀ x - f x
  have hq : Continuous q := (hV.mul hU₀).sub hf
  have hdLI := (Lp.memLp d).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  obtain ⟨D, hD, hdD, _, hDderiv⟩ :=
    buffer_localWeakDerivative_classicalRepresentative hab hdLI hq.locallyIntegrable
      hq.continuousOn (positiveBuffer_second_weak_derivative hV hf hU₀ hu₀ hud heq)
  have hfirst : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x : ℝ, u x * deriv φ x) = -(∫ x : ℝ, D x * φ x) := by
    intro φ hφ hcφ hsφ
    rw [hud φ hφ hcφ]
    congr 1
    apply integral_congr_ae
    have hdD' := (ae_restrict_iff' measurableSet_Ioo).mp hdD
    filter_upwards [hdD'] with x hx
    by_cases hxI : x ∈ Ioo a b
    · rw [hx hxI]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hxI (hsφ ht))]
      simp only [mul_zero]
  have huLI := (Lp.memLp u).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  obtain ⟨U, hU, huU, _, hUderiv⟩ :=
    buffer_localWeakDerivative_classicalRepresentative hab huLI hD.locallyIntegrable
      hD.continuousOn hfirst
  have hUU₀ : EqOn U U₀ (Ioo a b) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq
      (huU.symm.trans (ae_restrict_of_ae hu₀)) isOpen_Ioo hU.continuousOn hU₀.continuousOn
  refine ⟨U, D, hU, hD, huU, hdD, hUderiv, ?_⟩
  intro x hx
  simpa only [q, ← hUU₀ hx] using hDderiv x hx

/-- Smooth local data give the actual smooth Schrödinger representative. -/
theorem positiveBuffer_local_smooth_representative {V f : ℝ → ℝ}
    {u d : RadialL2} {a b : ℝ} (hab : a < b)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (hud : WeakRadialDerivative u d)
    (heq : PositiveBufferLocalWeakEquation V u f a b) :
    ∃ U : ℝ → ℝ, Continuous U ∧
      (u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] U ∧
      ContDiffOn ℝ ∞ U (Ioo a b) ∧
      ∀ x ∈ Ioo a b, -deriv (deriv U) x + V x * U x = f x := by
  obtain ⟨U, D, hU, _, huU, _, hUderiv, hDderiv⟩ :=
    positiveBuffer_local_classical_representative hab hV.continuous hf.continuous hud heq
  have hDderiv' : ∀ x ∈ Ioo a b, HasDerivAt D (V x * U x + (-f x)) x := by
    simpa only [sub_eq_add_neg] using hDderiv
  have hsm := positiveBuffer_classical_contDiffOn isOpen_Ioo hV.contDiffOn
    hf.neg.contDiffOn hUderiv hDderiv'
  refine ⟨U, hU, huU, hsm.1, ?_⟩
  intro x hx
  simpa only [neg_neg] using positiveBuffer_classical_equation isOpen_Ioo hUderiv hDderiv' hx

end ContinuousFlexibility.Radial
