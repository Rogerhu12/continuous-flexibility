module

public import ContinuousFlexibility.Radial.CentralSpectralGap

/-!
# Actual whole-line differential pairings with Hermite functions

The test function is not assumed to solve an eigen-equation. Its actual
oscillator image belongs to Lebesgue `L²`, and all integrations by parts
below follow from explicit `L¹` product conditions. This identifies the
Hermite coefficients of the actual differential image on the stated
smooth energy domain. It does not identify a full distributional or
Friedrichs domain.

This supplies the differential-to-coefficient bridge for Section 4,
`eq:central-spectrum-new` and the closed realization used in `eq:rad-eq-sc3`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- `φ ψ''` is genuinely integrable even though neither `ψ''` nor
`X²ψ` is separately assumed to belong to `L²`. -/
theorem integrable_mul_second_of_oscillator_image
    {j : ℝ} {φ ψ : ℝ → ℝ}
    (hφ : OscillatorEnergyDomain φ) (hψ : OscillatorEnergyDomain ψ)
    (hHψ : MemLp (oscillatorExpression j ψ) 2 volume) :
    Integrable (fun x => φ x * deriv (deriv ψ) x) volume := by
  have hp := hφ.2.2.2.integrable_mul hψ.2.2.2
  have hq := hφ.2.1.integrable_mul hHψ
  convert (hp.const_mul (j ^ 2)).sub hq using 1
  funext x
  simp only [Pi.sub_apply, Pi.mul_apply, oscillatorExpression]
  ring

/-- Green symmetry follows from two actual integrations by parts on
the whole line; it is not an extra domain axiom. -/
theorem oscillatorExpression_pairing_symm
    {j : ℝ} {φ ψ : ℝ → ℝ}
    (hφ : OscillatorEnergyDomain φ) (hψ : OscillatorEnergyDomain ψ)
    (hHφ : MemLp (oscillatorExpression j φ) 2 volume)
    (hHψ : MemLp (oscillatorExpression j ψ) 2 volume) :
    (∫ x : ℝ, φ x * oscillatorExpression j ψ x) =
      ∫ x : ℝ, ψ x * oscillatorExpression j φ x := by
  have hφψ := integrable_mul_second_of_oscillator_image hφ hψ hHψ
  have hψφ := integrable_mul_second_of_oscillator_image hψ hφ hHφ
  have hI := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => (hφ.1.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hψ.1.differentiable_deriv_two x).hasDerivAt)
    hφψ (hφ.2.2.1.integrable_mul hψ.2.2.1) (hφ.2.1.integrable_mul hψ.2.2.1)
  have hJ := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => (hψ.1.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hφ.1.differentiable_deriv_two x).hasDerivAt)
    hψφ (hψ.2.2.1.integrable_mul hφ.2.2.1) (hψ.2.1.integrable_mul hφ.2.2.1)
  have hs : (∫ x : ℝ, φ x * deriv (deriv ψ) x) =
      ∫ x : ℝ, ψ x * deriv (deriv φ) x := by
    rw [hI, hJ]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hz : (∫ x : ℝ,
      φ x * oscillatorExpression j ψ x - ψ x * oscillatorExpression j φ x) = 0 := by
    calc
      _ = ∫ x : ℝ, ψ x * deriv (deriv φ) x - φ x * deriv (deriv ψ) x := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [oscillatorExpression]
        ring
      _ = 0 := by rw [integral_sub hψφ hφψ, hs, sub_self]
  have hleft : Integrable (fun x => φ x * oscillatorExpression j ψ x) volume :=
    hφ.2.1.integrable_mul hHψ
  have hright : Integrable (fun x => ψ x * oscillatorExpression j φ x) volume :=
    hψ.2.1.integrable_mul hHφ
  rw [integral_sub hleft hright] at hz
  exact sub_eq_zero.mp hz

/-- Coefficients of the actual oscillator image are the Hermite
coefficients multiplied by the true eigenvalue. -/
theorem oscillator_normalizedHermite_pairing
    {j : ℝ} (hj : 0 < j) {ψ : ℝ → ℝ}
    (hψ : OscillatorEnergyDomain ψ)
    (hHψ : MemLp (oscillatorExpression j ψ) 2 volume) (n : ℕ) :
    (∫ x : ℝ, oscillatorExpression j ψ x * normalizedOscillatorHermite j n x) =
      j * (2 * (n : ℝ) + 1) *
        (∫ x : ℝ, ψ x * normalizedOscillatorHermite j n x) := by
  have hφ := normalizedOscillatorHermite_energyDomain hj n
  have hHφ : MemLp (oscillatorExpression j (normalizedOscillatorHermite j n)) 2 volume := by
    convert hφ.2.1.const_mul (j * (2 * (n : ℝ) + 1)) using 1
    funext x
    exact normalizedOscillatorHermite_equation hj n x
  calc
    _ = ∫ x : ℝ, normalizedOscillatorHermite j n x * oscillatorExpression j ψ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = ∫ x : ℝ, ψ x * oscillatorExpression j (normalizedOscillatorHermite j n) x :=
      oscillatorExpression_pairing_symm hφ hψ hHφ hHψ
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [normalizedOscillatorHermite_equation hj n x]
      ring

theorem central_liouvilleSchrodinger_eq_oscillator_shift
    (j : ℝ) (ψ : ℝ → ℝ) (x : ℝ) :
    liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ x =
      oscillatorExpression j ψ x +
        (centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA) * ψ x := by
  rw [central_liouvilleSchrodinger]
  simp only [oscillatorExpression]
  ring

/-- The genuine central and oscillator images differ by a bounded scalar
multiple of the actual `L²` input. -/
theorem central_memLp_image_iff
    {j : ℝ} {ψ : ℝ → ℝ} (hψ : OscillatorEnergyDomain ψ) :
    MemLp (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ) 2 volume ↔
      MemLp (oscillatorExpression j ψ) 2 volume := by
  constructor
  · intro h
    convert h.sub (hψ.2.1.const_mul (centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA)) using 1
    funext x
    simp only [Pi.sub_apply, central_liouvilleSchrodinger_eq_oscillator_shift]
    ring
  · intro h
    convert h.add (hψ.2.1.const_mul (centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA)) using 1
    funext x
    simp only [Pi.add_apply, central_liouvilleSchrodinger_eq_oscillator_shift]

/-- The actual central differential expression has exactly the proved
central spectral level in each Hermite pairing on the stated domain. -/
theorem central_normalizedHermite_pairing
    {j : ℝ} (hj : 0 < j) {ψ : ℝ → ℝ}
    (hψ : OscillatorEnergyDomain ψ)
    (hHψ : MemLp (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ) 2 volume)
    (n : ℕ) :
    (∫ x : ℝ,
      liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ x *
        normalizedOscillatorHermite j n x) =
      centralSpectralLevel j n * (∫ x : ℝ, ψ x * normalizedOscillatorHermite j n x) := by
  have hH := (central_memLp_image_iff hψ).mp hHψ
  have hpair := oscillator_normalizedHermite_pairing hj hψ hH n
  have hprod : Integrable (fun x => oscillatorExpression j ψ x *
      normalizedOscillatorHermite j n x) volume :=
    hH.integrable_mul (normalizedOscillatorHermite_energyDomain hj n).2.1
  have hinput : Integrable (fun x => ψ x * normalizedOscillatorHermite j n x) volume :=
    hψ.2.1.integrable_mul (normalizedOscillatorHermite_energyDomain hj n).2.1
  calc
    _ = ∫ x : ℝ, oscillatorExpression j ψ x * normalizedOscillatorHermite j n x +
        (centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA) *
          (ψ x * normalizedOscillatorHermite j n x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [central_liouvilleSchrodinger_eq_oscillator_shift]
      ring
    _ = (∫ x : ℝ, oscillatorExpression j ψ x * normalizedOscillatorHermite j n x) +
        (centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA) *
          (∫ x : ℝ, ψ x * normalizedOscillatorHermite j n x) := by
      rw [integral_add hprod (hinput.const_mul _), integral_const_mul]
    _ = _ := by rw [hpair]; unfold centralSpectralLevel; ring

theorem oscillatorEnergyDomain_zero : OscillatorEnergyDomain (fun _ : ℝ => 0) := by
  refine ⟨contDiff_const, MemLp.zero', ?_, ?_⟩ <;> simp

theorem oscillatorEnergyDomain_add {φ ψ : ℝ → ℝ}
    (hφ : OscillatorEnergyDomain φ) (hψ : OscillatorEnergyDomain ψ) :
    OscillatorEnergyDomain (fun x => φ x + ψ x) := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, ?_, ?_⟩
  · have hd : deriv (fun x => φ x + ψ x) = fun x => deriv φ x + deriv ψ x := by
      funext x
      exact ((hφ.1.differentiable (by norm_num) x).hasDerivAt.add
        (hψ.1.differentiable (by norm_num) x).hasDerivAt).deriv
    rw [hd]
    exact hφ.2.2.1.add hψ.2.2.1
  · convert hφ.2.2.2.add hψ.2.2.2 using 1
    funext x
    simp only [Pi.add_apply]
    ring

theorem oscillatorEnergyDomain_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, OscillatorEnergyDomain (f i)) :
    OscillatorEnergyDomain (fun x => ∑ i ∈ s, f i x) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa only [Finset.sum_empty] using oscillatorEnergyDomain_zero
  | @insert i s hi ih =>
    intro hf
    have hs := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
    simpa only [Finset.sum_insert hi] using
      oscillatorEnergyDomain_add (hf i (Finset.mem_insert_self i s)) hs

theorem oscillatorExpression_add (j : ℝ) {φ ψ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) (x : ℝ) :
    oscillatorExpression j (fun y => φ y + ψ y) x =
      oscillatorExpression j φ x + oscillatorExpression j ψ x := by
  have hd : deriv (fun y => φ y + ψ y) = fun y => deriv φ y + deriv ψ y := by
    funext y
    exact ((hφ.differentiable (by norm_num) y).hasDerivAt.add
      (hψ.differentiable (by norm_num) y).hasDerivAt).deriv
  have hdd : deriv (deriv (fun y => φ y + ψ y)) x =
      deriv (deriv φ) x + deriv (deriv ψ) x := by
    rw [hd]
    exact ((hφ.differentiable_deriv_two x).hasDerivAt.add
      (hψ.differentiable_deriv_two x).hasDerivAt).deriv
  simp only [oscillatorExpression, hdd]
  ring

theorem oscillatorExpression_finset_sum {ι : Type*} (j : ℝ) (s : Finset ι)
    (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (x : ℝ) :
    oscillatorExpression j (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, oscillatorExpression j (f i) x := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp [oscillatorExpression]
  | @insert i s hi ih =>
    intro hf
    have hs : ∀ k ∈ s, ContDiff ℝ 2 (f k) :=
      fun k hk => hf k (Finset.mem_insert_of_mem hk)
    simp only [Finset.sum_insert hi]
    rw [oscillatorExpression_add j (hf i (Finset.mem_insert_self i s)) (ContDiff.sum hs) x,
      ih hs]

/-- Finite combinations are actual globally smooth functions, before
passing to any `L²` equivalence classes or graph closure. -/
def finiteHermiteFunction (j : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) : ℝ → ℝ :=
  fun x => ∑ n ∈ s, a n * normalizedOscillatorHermite j n x

theorem contDiff_normalizedOscillatorHermite (j : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (normalizedOscillatorHermite j n) :=
  (contDiff_polynomialGaussian j (oscillatorHermitePolynomial j n)).div_const _

theorem contDiff_finiteHermiteFunction (j : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) :
    ContDiff ℝ ∞ (finiteHermiteFunction j s a) :=
  ContDiff.sum (fun n _ => contDiff_const.mul (contDiff_normalizedOscillatorHermite j n))

theorem finiteHermiteFunction_energyDomain {j : ℝ} (hj : 0 < j)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    OscillatorEnergyDomain (finiteHermiteFunction j s a) :=
  oscillatorEnergyDomain_finset_sum s _ (fun n _ =>
    oscillatorEnergyDomain_const_mul (normalizedOscillatorHermite_energyDomain hj n) (a n))

/-- The finite Hermite graph uses the genuine oscillator derivatives. -/
theorem oscillatorExpression_finiteHermiteFunction {j : ℝ} (hj : 0 < j)
    (s : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    oscillatorExpression j (finiteHermiteFunction j s a) x =
      ∑ n ∈ s, a n * (j * (2 * (n : ℝ) + 1)) * normalizedOscillatorHermite j n x := by
  unfold finiteHermiteFunction
  rw [oscillatorExpression_finset_sum j s _
    (fun n _ => (contDiff_const.mul (contDiff_normalizedOscillatorHermite j n)).of_le (by simp)) x]
  apply Finset.sum_congr rfl
  intro n _
  rw [oscillatorExpression_const_mul
    ((contDiff_normalizedOscillatorHermite j n).of_le (by simp)),
    normalizedOscillatorHermite_equation hj n x]
  ring

/-- The finite central graph likewise uses the actual radius and density
in the actual Liouville differential expression. -/
theorem centralExpression_finiteHermiteFunction {j : ℝ} (hj : 0 < j)
    (s : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
      (finiteHermiteFunction j s a) x =
      ∑ n ∈ s, a n * centralSpectralLevel j n * normalizedOscillatorHermite j n x := by
  rw [central_liouvilleSchrodinger_eq_oscillator_shift,
    oscillatorExpression_finiteHermiteFunction hj]
  unfold finiteHermiteFunction
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  unfold centralSpectralLevel
  ring

end ContinuousFlexibility.Radial
