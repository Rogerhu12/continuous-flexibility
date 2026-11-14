module

public import ContinuousFlexibility.Analysis.CanonicalFixedPositiveFamily
public import ContinuousFlexibility.Analysis.OneSidedEndpointHeight

/-!
# The retained low logarithmic bound for the actual positive height

The selected collar is identified with its original explicit width.
The existing width-margin theorem then gives the smallness required by
the Taylor and exponential consumers. No new collar, low envelope or
sampled material estimate is selected.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

/-- The exact reciprocal equality identifies the same selected collar
with the original construction, including its low logarithmic margin. -/
theorem n04Realization_fixedPositive_log_smallness
    {D : ReferenceData}
    {B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi)}
    {n : ℕ} {κ M H Clog Mσ δ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ}
    (hcontrols : N04FixedPositiveFamilyControls B n κ M H Clog Mσ δ)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) :
    let Mlow : ℝ := Clog i * H i ^ (2 * n + 1)
    0 ≤ Mlow ∧ ((n + 1 : ℕ) : ℝ) * Mlow * δ i ≤ 1 := by
  obtain ⟨_hκ, _hκone, _hκinv, _hM, hH, hClog, _hMσ,
      hδ, hδρ, _hδone, hrecip, _hJ⟩ := hcontrols i
  let ρ : ℝ := min ((n04PositiveRight i - n04PositiveLeft i) / 4)
    (min (B.centerLeft i - n04PositiveLeft i) (n04PositiveRight i - B.centerRight i))
  let Mlow : ℝ := Clog i * H i ^ (2 * n + 1)
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hMlow : 0 ≤ Mlow :=
    mul_nonneg hClog.le (pow_nonneg (zero_le_one.trans hH) _)
  have hwidth : δ i = oneSidedEndpointHeightWidth n ρ Mlow := by
    calc
      δ i = ((δ i)⁻¹)⁻¹ := (inv_inv _).symm
      _ = oneSidedEndpointHeightWidth n ρ Mlow :=
        congrArg (fun t : ℝ => t⁻¹) hrecip
  have hsmall : ((n + 1 : ℕ) : ℝ) * Mlow *
      oneSidedEndpointHeightWidth n ρ Mlow ≤ 1 :=
    (oneSidedEndpointHeightWidth_margins n hρ hMlow).2.2.2.2
  rw [← hwidth] at hsmall
  exact ⟨hMlow, hsmall⟩

/-- The retained constructor bound supplies all low logarithmic inputs
of the degree-three actual height consumer on the same parameter set.
The parameter map only selects states from the existing neighborhood. -/
theorem n04Realization_actualFixedPositiveHeight_log_data
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi)}
    {κ M H Clog Mσ δ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ}
    {base : ℕ} {ε : ℝ}
    (src : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (hcontrols : N04FixedPositiveFamilyControls B 3 κ M H Clog Mσ δ)
    (hlog : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ i side j, 0 < j → j ≤ 3 → ∀ θ,
        |positiveHeightTaylorData (n04PositiveLeft i) (n04PositiveRight i) (fun _ => 1)
          (fun side => n04PositiveSourceHeight (src i side) K z) side j θ| ≤
          Clog i * H i ^ 7)
    {X : Type*} (U : Set X) (state : X → AnnularState S × ℝ)
    (hstate : ∀ x ∈ U, state x ∈ stateNeighborhood S C base ε)
    (hsector : ∀ x ∈ U, stateSector S (state x).1)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) :
    let Mlow : ℝ := Clog i * H i ^ 7
    0 ≤ Mlow ∧
      (∀ x ∈ U, ∀ side j, 0 < j → j ≤ 3 → ∀ θ,
        |positiveHeightTaylorData (n04PositiveLeft i) (n04PositiveRight i) (fun _ => 1)
          (fun side => n04PositiveSourceHeight (src i side) K (state x)) side j θ| ≤ Mlow) ∧
      (4 : ℝ) * Mlow * δ i ≤ 1 := by
  have hsmall := n04Realization_fixedPositive_log_smallness hcontrols i
  refine ⟨hsmall.1, ?_, hsmall.2⟩
  intro x hx side j hj hj3 θ
  exact hlog (state x) (hstate x hx) (hsector x hx) i side j hj hj3 θ

end ContinuousFlexibility.Analysis
