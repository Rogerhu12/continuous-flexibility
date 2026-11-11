import ContinuousFlexibility.Radial.PositiveBufferEnergyForm

/-!
# Compact smooth lifts and the actual variational equation

Compact smooth functions have canonical lifts into the actual weighted energy
space. Testing a stationary field with these lifts recovers its local weak
Schrödinger equation. A scaled fixed cutoff supplies a unit value at any cut.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem positiveBufferCompact_weight_memLp {V φ : ℝ → ℝ}
    (hV : Continuous V) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    MemLp (fun x => sqrt (1 + |V x|) * φ x) 2 volume :=
  (((continuous_const.add hV.abs).sqrt).mul hφ.continuous).memLp_of_hasCompactSupport
    hc.mul_left

/-- A compact smooth test is lifted with its actual derivative and actual
potential weight, without a choice of an abstract completion element. -/
def positiveBufferCompactEnergyLift (V : ℝ → ℝ) (hV : Continuous V)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    PositiveBufferEnergy V := by
  let ht := compactSmooth_morseEnergyDomain hφ hc
  let hw := positiveBufferCompact_weight_memLp hV hφ hc
  refine ⟨WithLp.toLp 2 ![ht.2.1.toLp φ, ht.2.2.1.toLp (deriv φ),
    hw.toLp (fun x => sqrt (1 + |V x|) * φ x)], ?_⟩
  refine ⟨(morseWeakDerivative_iff_public _ _).mp (morseWeakDerivativeL2_of_energyDomain ht), ?_⟩
  filter_upwards [MemLp.coeFn_toLp ht.2.1, MemLp.coeFn_toLp hw] with x hu hweight
  change hw.toLp (fun x => sqrt (1 + |V x|) * φ x) x =
    sqrt (1 + |V x|) * ht.2.1.toLp φ x
  rw [hu, hweight]

theorem positiveBufferCompactEnergyLift_base_ae (V : ℝ → ℝ) (hV : Continuous V)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (positiveBufferEnergyCoordinate V 0 (positiveBufferCompactEnergyLift V hV φ hφ hc) : ℝ → ℝ)
      =ᵐ[volume] φ := MemLp.coeFn_toLp _

theorem positiveBufferCompactEnergyLift_derivative_ae (V : ℝ → ℝ) (hV : Continuous V)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (positiveBufferEnergyCoordinate V 1 (positiveBufferCompactEnergyLift V hV φ hφ hc) : ℝ → ℝ)
      =ᵐ[volume] deriv φ := MemLp.coeFn_toLp _

theorem positiveBufferCompactEnergyLift_mem_supported (V : ℝ → ℝ) (hV : Continuous V)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s : Set ℝ) (hs : MeasurableSet s) (hφs : Function.support φ ⊆ s) :
    positiveBufferCompactEnergyLift V hV φ hφ hc ∈ positiveBufferSupportedEnergyGraph V s hs := by
  apply (mem_positiveBufferSupportedEnergyGraph_iff V s hs _).mpr
  apply (ae_restrict_iff' hs.compl).mpr
  filter_upwards [positiveBufferCompactEnergyLift_base_ae V hV φ hφ hc] with x hx hxs
  rw [hx]
  exact Function.notMem_support.mp (fun hφx => hxs (hφs hφx))

theorem positiveBufferEnergyForm_compact_right (V : ℝ → ℝ) (hV : Continuous V)
    (u : PositiveBufferEnergy V) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    positiveBufferEnergyForm V hV u (positiveBufferCompactEnergyLift V hV φ hφ hc) =
      (∫ x : ℝ, positiveBufferEnergyCoordinate V 1 u x * deriv φ x) +
      ∫ x : ℝ, V x * positiveBufferEnergyCoordinate V 0 u x * φ x := by
  rw [positiveBufferEnergyForm_eq_integral, positiveBufferL2_inner_integral]
  congr 1
  · apply integral_congr_ae
    filter_upwards [positiveBufferCompactEnergyLift_derivative_ae V hV φ hφ hc] with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [positiveBufferCompactEnergyLift_base_ae V hV φ hφ hc] with x hx
    rw [hx]

/-- Stationarity in the supported variation space is the local weak
Schrödinger equation against every compact smooth test in that region. -/
theorem positiveBuffer_stationary_weak_equation (V : ℝ → ℝ) (hV : Continuous V)
    (s : Set ℝ) (hs : MeasurableSet s) (u : PositiveBufferEnergy V)
    (hu : ∀ v : PositiveBufferEnergy V, v ∈ positiveBufferSupportedEnergyGraph V s hs →
      positiveBufferEnergyForm V hV u v = 0)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφs : Function.support φ ⊆ s) :
    (∫ x : ℝ, positiveBufferEnergyCoordinate V 0 u x * deriv (deriv φ) x) =
      ∫ x : ℝ, V x * positiveBufferEnergyCoordinate V 0 u x * φ x := by
  have hv := hu (positiveBufferCompactEnergyLift V hV φ hφ hc)
    (positiveBufferCompactEnergyLift_mem_supported V hV φ hφ hc s hs hφs)
  rw [positiveBufferEnergyForm_compact_right] at hv
  have hd := positiveBufferEnergy_derivative_weak V u (deriv φ)
    (contDiff_infty_iff_deriv.mp hφ).2 hc.deriv
  linarith

/-- A fixed smooth cutoff at the inverse-mass scale supplies the same unit
trace lift at either cut. -/
def positiveBufferTraceLift (c m x : ℝ) : ℝ := oscillatorCutoff (m * (x - c))

theorem contDiff_positiveBufferTraceLift (c m : ℝ) :
    ContDiff ℝ ∞ (positiveBufferTraceLift c m) :=
  contDiff_oscillatorCutoff.comp ((contDiff_id.sub_const c).const_mul m)

theorem positiveBufferTraceLift_at_cut (c m : ℝ) : positiveBufferTraceLift c m c = 1 := by
  apply oscillatorCutoff_eq_one
  simp

theorem positiveBufferTraceLift_eq_zero {c m x : ℝ} (hm : 0 < m)
    (hx : 2 / m ≤ |x - c|) : positiveBufferTraceLift c m x = 0 := by
  apply oscillatorCutoff_eq_zero
  rw [abs_mul, abs_of_pos hm]
  exact (div_le_iff₀ hm).mp hx |>.trans_eq (mul_comm _ _)

theorem positiveBufferTraceLift_hasCompactSupport (c : ℝ) {m : ℝ} (hm : 0 < m) :
    HasCompactSupport (positiveBufferTraceLift c m) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (c - 2 / m) (c + 2 / m)))
  intro x hx
  apply positiveBufferTraceLift_eq_zero hm
  by_contra hn
  have habs : |x - c| < 2 / m := lt_of_not_ge hn
  have hpair := abs_lt.mp habs
  exact hx ⟨by linarith [hpair.1], by linarith [hpair.2]⟩

theorem positiveBufferTraceLift_abs_le_one (c m x : ℝ) :
    |positiveBufferTraceLift c m x| ≤ 1 := by
  rw [positiveBufferTraceLift, abs_of_nonneg (oscillatorCutoff_nonneg _)]
  exact oscillatorCutoff_le_one _

theorem deriv_positiveBufferTraceLift (c m x : ℝ) :
    deriv (positiveBufferTraceLift c m) x = m * deriv oscillatorCutoff (m * (x - c)) := by
  have h := (contDiff_oscillatorCutoff.differentiable (by simp) _).hasDerivAt.comp x
    (((hasDerivAt_id x).sub_const c).const_mul m)
  convert h.deriv using 1 <;> ring

theorem positiveBufferTraceLift_deriv_abs_le (c : ℝ) {m : ℝ} (hm : 0 ≤ m) (x : ℝ) :
    |deriv (positiveBufferTraceLift c m) x| ≤ m * morseCutoffDerivativeConstant := by
  rw [deriv_positiveBufferTraceLift, abs_mul, abs_of_nonneg hm]
  exact mul_le_mul_of_nonneg_left
    ((Classical.choose_spec oscillatorCutoff_derivative_bounds).2.1 (m * (x - c))) hm

theorem positiveBufferTraceLift_tsupport_subset (c : ℝ) {m : ℝ} (hm : 0 < m) :
    tsupport (positiveBufferTraceLift c m) ⊆ Icc (c - 2 / m) (c + 2 / m) := by
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  by_contra hn
  apply hx
  apply positiveBufferTraceLift_eq_zero hm
  by_contra hh
  have hpair := abs_lt.mp (lt_of_not_ge hh)
  exact hn ⟨by linarith [hpair.1], by linarith [hpair.2]⟩

/-- The compact lift has energy of order the barrier mass, using only the
upper potential bound in the cut layer. The constant is independent of the
potential away from that layer and of the mass. -/
theorem positiveBufferTraceLift_energy_bound {V : ℝ → ℝ} (hV : Continuous V)
    (c : ℝ) {m C₀ : ℝ} (hm : 0 < m) (hC₀ : 0 ≤ C₀)
    (hupper : ∀ x, |x - c| ≤ 2 / m → V x ≤ C₀ * m ^ 2) :
    (∫ x : ℝ, deriv (positiveBufferTraceLift c m) x ^ 2 +
      V x * positiveBufferTraceLift c m x ^ 2) ≤
      4 * (morseCutoffDerivativeConstant ^ 2 + C₀) * m := by
  let φ := positiveBufferTraceLift c m
  let I := Icc (c - 2 / m) (c + 2 / m)
  let E (x : ℝ) := deriv φ x ^ 2 + V x * φ x ^ 2
  have hφ := contDiff_positiveBufferTraceLift c m
  have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
  have hzero (x : ℝ) (hx : x ∉ I) : E x = 0 := by
    have ht : x ∉ tsupport φ := fun hmem => hx (positiveBufferTraceLift_tsupport_subset c hm hmem)
    dsimp [E]
    rw [image_eq_zero_of_notMem_tsupport ht, deriv_of_notMem_tsupport ht]
    simp
  have hE : Integrable E volume :=
    ((hφ'.continuous.pow 2).add (hV.mul (hφ.continuous.pow 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.intro isCompact_Icc hzero)
  have hbound (x : ℝ) (hx : x ∈ I) :
      E x ≤ (morseCutoffDerivativeConstant ^ 2 + C₀) * m ^ 2 := by
    have hK := morseCutoffDerivativeConstant_nonneg
    have hd := positiveBufferTraceLift_deriv_abs_le c hm.le x
    have hd2 := (sq_le_sq₀ (abs_nonneg (deriv φ x)) (mul_nonneg hm.le hK)).mpr hd
    rw [sq_abs] at hd2
    have hφ0 : 0 ≤ φ x := oscillatorCutoff_nonneg _
    have hφ1 : φ x ≤ 1 := oscillatorCutoff_le_one _
    have hφ2 : φ x ^ 2 ≤ 1 := by nlinarith [mul_nonneg hφ0 (sub_nonneg.mpr hφ1)]
    have hx' : |x - c| ≤ 2 / m := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hv := (mul_le_mul_of_nonneg_right (hupper x hx') (sq_nonneg (φ x))).trans
      (mul_le_mul_of_nonneg_left hφ2 (mul_nonneg hC₀ (sq_nonneg m)))
    dsimp [E]
    nlinarith
  have hI : c - 2 / m ≤ c + 2 / m := by
    have hpos : 0 ≤ 2 / m := by positivity
    linarith
  have h := setIntegral_mono_on hE.integrableOn
    (integrableOn_const (μ := volume) (s := I)
      (C := (morseCutoffDerivativeConstant ^ 2 + C₀) * m ^ 2))
    measurableSet_Icc hbound
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero, setIntegral_const,
    Real.volume_real_Icc_of_le hI, smul_eq_mul] at h
  have he : ((c + 2 / m) - (c - 2 / m)) *
      ((morseCutoffDerivativeConstant ^ 2 + C₀) * m ^ 2) =
        4 * (morseCutoffDerivativeConstant ^ 2 + C₀) * m := by
    field_simp [hm.ne']
    <;> ring
  simpa only [he] using h

end ContinuousFlexibility.Radial
