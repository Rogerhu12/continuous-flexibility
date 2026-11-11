import ContinuousFlexibility.Radial.PositiveBufferEnergySpace

/-!
# Coercivity of the actual positive-buffer energy

The continuous bilinear form from `PositiveBufferEnergySpace` is identified with
the physical potential integral. On fields supported where `V ≥ m²`, its
coercivity constant is `m² / (m² + 2)` in the exact Hilbert graph norm. This is
the variational existence input for finite-buffer and exterior problems.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

local instance (V : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    NormedSpace ℝ (positiveBufferSupportedEnergyGraph V s hs) :=
  Submodule.normedSpace (positiveBufferSupportedEnergyGraph V s hs)

theorem positiveBufferL2_inner_integral (u v : RadialL2) :
    ⟪u, v⟫_ℝ = ∫ x : ℝ, u x * v x := by
  rw [L2.inner_def]
  congr 1
  funext x
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem positiveBufferL2_norm_sq_integral (u : RadialL2) :
    ‖u‖ ^ 2 = ∫ x : ℝ, u x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, positiveBufferL2_inner_integral]
  congr 1
  funext x
  ring

theorem positiveBufferPotentialMultiplier_ae (V : ℝ → ℝ) (hV : Continuous V) (u : RadialL2) :
    (positiveBufferPotentialMultiplier V hV u : ℝ → ℝ) =ᵐ[volume]
      (fun x => positiveBufferPotentialCoefficient V x * u x) :=
  morseL2Mul_coeFn (positiveBufferPotentialCoefficient V)
    (continuous_positiveBufferPotentialCoefficient hV) 1
    (positiveBufferPotentialCoefficient_abs_le_one V) u

theorem positiveBufferPotentialCoefficient_weight (V : ℝ → ℝ) (x : ℝ) :
    positiveBufferPotentialCoefficient V x * sqrt (1 + |V x|) ^ 2 = V x := by
  rw [sq_sqrt (by positivity), positiveBufferPotentialCoefficient]
  exact div_mul_cancel₀ _ (by positivity)

theorem positiveBufferPotential_pairing_ae (V : ℝ → ℝ) (hV : Continuous V)
    (u v : PositiveBufferEnergy V) :
    (fun x => positiveBufferPotentialMultiplier V hV (positiveBufferEnergyCoordinate V 2 u) x *
      positiveBufferEnergyCoordinate V 2 v x) =ᵐ[volume]
    (fun x => V x * positiveBufferEnergyCoordinate V 0 u x *
      positiveBufferEnergyCoordinate V 0 v x) := by
  filter_upwards [positiveBufferPotentialMultiplier_ae V hV (positiveBufferEnergyCoordinate V 2 u),
    positiveBufferEnergy_weight_ae V u, positiveBufferEnergy_weight_ae V v] with x hm hu hv
  rw [hm, hu, hv]
  calc
    _ = (positiveBufferPotentialCoefficient V x * sqrt (1 + |V x|) ^ 2) *
        positiveBufferEnergyCoordinate V 0 u x * positiveBufferEnergyCoordinate V 0 v x := by ring
    _ = _ := by rw [positiveBufferPotentialCoefficient_weight]

theorem positiveBufferPotential_pairing_integrable (V : ℝ → ℝ) (hV : Continuous V)
    (u v : PositiveBufferEnergy V) :
    Integrable (fun x => V x * positiveBufferEnergyCoordinate V 0 u x *
      positiveBufferEnergyCoordinate V 0 v x) volume :=
  ((Lp.memLp (positiveBufferPotentialMultiplier V hV (positiveBufferEnergyCoordinate V 2 u))).integrable_mul
    (Lp.memLp (positiveBufferEnergyCoordinate V 2 v))).congr
      (positiveBufferPotential_pairing_ae V hV u v)

theorem positiveBufferEnergyForm_eq_integral (V : ℝ → ℝ) (hV : Continuous V)
    (u v : PositiveBufferEnergy V) :
    positiveBufferEnergyForm V hV u v =
      ⟪positiveBufferEnergyCoordinate V 1 u, positiveBufferEnergyCoordinate V 1 v⟫_ℝ +
      ∫ x : ℝ, V x * positiveBufferEnergyCoordinate V 0 u x *
        positiveBufferEnergyCoordinate V 0 v x := by
  rw [positiveBufferEnergyForm_apply,
    positiveBufferL2_inner_integral
      (positiveBufferPotentialMultiplier V hV (positiveBufferEnergyCoordinate V 2 u))
      (positiveBufferEnergyCoordinate V 2 v)]
  exact congrArg (fun t : ℝ => ⟪positiveBufferEnergyCoordinate V 1 u,
    positiveBufferEnergyCoordinate V 1 v⟫_ℝ + t)
    (integral_congr_ae (positiveBufferPotential_pairing_ae V hV u v))

theorem positiveBufferEnergyForm_symm (V : ℝ → ℝ) (hV : Continuous V)
    (u v : PositiveBufferEnergy V) :
    positiveBufferEnergyForm V hV u v = positiveBufferEnergyForm V hV v u := by
  rw [positiveBufferEnergyForm_eq_integral, positiveBufferEnergyForm_eq_integral,
    real_inner_comm (positiveBufferEnergyCoordinate V 1 v) (positiveBufferEnergyCoordinate V 1 u)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem positiveBufferEnergy_weight_sq_ae (V : ℝ → ℝ) (u : PositiveBufferEnergy V) :
    (fun x => positiveBufferEnergyCoordinate V 2 u x ^ 2) =ᵐ[volume]
      (fun x => (1 + |V x|) * positiveBufferEnergyCoordinate V 0 u x ^ 2) := by
  filter_upwards [positiveBufferEnergy_weight_ae V u] with x hx
  rw [hx, mul_pow, sq_sqrt (by positivity)]

theorem positiveBufferEnergy_weight_lower_bound {V : ℝ → ℝ} {m : ℝ}
    (s : Set ℝ) (hs : MeasurableSet s) (hVm : ∀ x ∈ s, m ^ 2 ≤ V x)
    (u : PositiveBufferEnergy V) (hu : u ∈ positiveBufferSupportedEnergyGraph V s hs) :
    (1 + m ^ 2) * ‖positiveBufferEnergyCoordinate V 0 u‖ ^ 2 ≤
      ‖positiveBufferEnergyCoordinate V 2 u‖ ^ 2 := by
  have hout := (ae_restrict_iff' hs.compl).mp
    ((mem_positiveBufferSupportedEnergyGraph_iff V s hs u).mp hu)
  have hle : (fun x => (1 + m ^ 2) * positiveBufferEnergyCoordinate V 0 u x ^ 2) ≤ᵐ[volume]
      (fun x => positiveBufferEnergyCoordinate V 2 u x ^ 2) := by
    filter_upwards [positiveBufferEnergy_weight_sq_ae V u, hout] with x hx ho
    rw [hx]
    by_cases hxs : x ∈ s
    · have hv : 0 ≤ V x := (sq_nonneg m).trans (hVm x hxs)
      rw [abs_of_nonneg hv]
      exact mul_le_mul_of_nonneg_right (by linarith [hVm x hxs]) (sq_nonneg _)
    · rw [ho hxs]
      simp
  have h := integral_mono_ae
    ((Lp.memLp (positiveBufferEnergyCoordinate V 0 u)).integrable_sq.const_mul (1 + m ^ 2))
    (Lp.memLp (positiveBufferEnergyCoordinate V 2 u)).integrable_sq hle
  rwa [integral_const_mul, ← positiveBufferL2_norm_sq_integral,
    ← positiveBufferL2_norm_sq_integral] at h

theorem positiveBufferEnergyForm_supported_self {V : ℝ → ℝ} (hV : Continuous V)
    (s : Set ℝ) (hs : MeasurableSet s) (hVnonneg : ∀ x ∈ s, 0 ≤ V x)
    (u : PositiveBufferEnergy V) (hu : u ∈ positiveBufferSupportedEnergyGraph V s hs) :
    positiveBufferEnergyForm V hV u u =
      ‖positiveBufferEnergyCoordinate V 1 u‖ ^ 2 +
      ‖positiveBufferEnergyCoordinate V 2 u‖ ^ 2 -
      ‖positiveBufferEnergyCoordinate V 0 u‖ ^ 2 := by
  have hout := (ae_restrict_iff' hs.compl).mp
    ((mem_positiveBufferSupportedEnergyGraph_iff V s hs u).mp hu)
  have hid : (fun x => V x * positiveBufferEnergyCoordinate V 0 u x *
      positiveBufferEnergyCoordinate V 0 u x) =ᵐ[volume]
      (fun x => positiveBufferEnergyCoordinate V 2 u x ^ 2 -
        positiveBufferEnergyCoordinate V 0 u x ^ 2) := by
    filter_upwards [positiveBufferEnergy_weight_sq_ae V u, hout] with x hx ho
    rw [hx]
    by_cases hxs : x ∈ s
    · rw [abs_of_nonneg (hVnonneg x hxs)]
      ring
    · rw [ho hxs]
      simp
  rw [positiveBufferEnergyForm_eq_integral, real_inner_self_eq_norm_sq,
    integral_congr_ae hid,
    integral_sub (Lp.memLp (positiveBufferEnergyCoordinate V 2 u)).integrable_sq
      (Lp.memLp (positiveBufferEnergyCoordinate V 0 u)).integrable_sq,
    ← positiveBufferL2_norm_sq_integral, ← positiveBufferL2_norm_sq_integral]
  ring

/-- Quantitative coercivity on the actual supported energy subspace. -/
theorem positiveBufferEnergyForm_supported_coercive_bound {V : ℝ → ℝ} (hV : Continuous V)
    {m : ℝ} (hm : 0 < m) (s : Set ℝ) (hs : MeasurableSet s)
    (hVm : ∀ x ∈ s, m ^ 2 ≤ V x) (u : PositiveBufferEnergy V)
    (hu : u ∈ positiveBufferSupportedEnergyGraph V s hs) :
    (m ^ 2 / (m ^ 2 + 2)) * ‖u‖ ^ 2 ≤ positiveBufferEnergyForm V hV u u := by
  have hlow := positiveBufferEnergy_weight_lower_bound s hs hVm u hu
  rw [positiveBufferEnergy_norm_sq,
    positiveBufferEnergyForm_supported_self hV s hs (fun x hx => (sq_nonneg m).trans (hVm x hx)) u hu]
  have hden : 0 < m ^ 2 + 2 := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith [sq_nonneg ‖positiveBufferEnergyCoordinate V 1 u‖]

theorem positiveBufferEnergyForm_supported_isCoercive {V : ℝ → ℝ} (hV : Continuous V)
    {m : ℝ} (hm : 0 < m) (s : Set ℝ) (hs : MeasurableSet s)
    (hVm : ∀ x ∈ s, m ^ 2 ≤ V x) :
    IsCoercive ((positiveBufferEnergyForm V hV).bilinearComp
      (positiveBufferSupportedEnergyGraph V s hs).subtypeL
      (positiveBufferSupportedEnergyGraph V s hs).subtypeL) := by
  refine ⟨m ^ 2 / (m ^ 2 + 2), by positivity, fun u => ?_⟩
  simpa only [ContinuousLinearMap.bilinearComp_apply, Submodule.subtypeL_apply,
    Submodule.norm_coe, pow_two, mul_assoc] using
    positiveBufferEnergyForm_supported_coercive_bound hV hm s hs hVm (u : PositiveBufferEnergy V) u.property

/-- An actual global energy field with a chosen exterior lift and stationary
physical equation on the positive region. The lift fixes the boundary trace. -/
theorem positiveBuffer_exists_unique_supported_stationary {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (hV : Continuous V) {m : ℝ} (hm : 0 < m)
    (s : Set ℝ) (hs : MeasurableSet s) (hVm : ∀ x ∈ s, m ^ 2 ≤ V x)
    (lift : PositiveBufferEnergy V) :
    ∃! u : PositiveBufferEnergy V,
      u - lift ∈ positiveBufferSupportedEnergyGraph V s hs ∧
      ∀ v : PositiveBufferEnergy V, v ∈ positiveBufferSupportedEnergyGraph V s hs →
        positiveBufferEnergyForm V hV u v = 0 := by
  letI := positiveBufferEnergy_completeSpace hreal
  exact positiveBuffer_exists_unique_stationary_of_restrict (positiveBufferEnergyForm V hV)
    (positiveBufferSupportedEnergyGraph V s hs)
    (positiveBufferSupportedEnergyGraph_isClosed V s hs)
    (positiveBufferEnergyForm_supported_isCoercive hV hm s hs hVm) lift

end ContinuousFlexibility.Radial
