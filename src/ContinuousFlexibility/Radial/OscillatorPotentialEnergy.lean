module

public import ContinuousFlexibility.Radial.OscillatorClosedForm
public import ContinuousFlexibility.Radial.CentralRadialWeightedInverse

/-!
# The actual absolute-potential energy domain

The third coordinate is the genuine multiplier sqrt (1 + |V|), not a
renamed position coordinate. Bounded measurable coordinate maps identify
its weak-derivative graph with the physical position energy graph. No
smoothness of the absolute-potential multiplier is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

def centralPotentialConstant (j : ℝ) : ℝ :=
  centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA

def centralPotentialValue (j x : ℝ) : ℝ := j ^ 2 * x ^ 2 + centralPotentialConstant j

def potentialEnergyWeight (j x : ℝ) : ℝ := sqrt (1 + |centralPotentialValue j x|)

def potentialEnergyWeightConstant (j : ℝ) : ℝ := sqrt (1 + |centralPotentialConstant j|)

theorem continuous_potentialEnergyWeight (j : ℝ) : Continuous (potentialEnergyWeight j) := by
  unfold potentialEnergyWeight centralPotentialValue
  exact continuous_sqrt.comp
    (continuous_const.add ((continuous_const.mul (continuous_id.pow 2)).add continuous_const).abs)

theorem potentialEnergyWeight_pos (j x : ℝ) : 0 < potentialEnergyWeight j x :=
  sqrt_pos.mpr (by positivity)

theorem potentialEnergyWeightConstant_pos (j : ℝ) : 0 < potentialEnergyWeightConstant j := by
  unfold potentialEnergyWeightConstant
  positivity

theorem potentialEnergyWeight_sq (j x : ℝ) :
    potentialEnergyWeight j x ^ 2 = 1 + |centralPotentialValue j x| :=
  sq_sqrt (by positivity)

theorem potentialEnergyWeightConstant_sq (j : ℝ) :
    potentialEnergyWeightConstant j ^ 2 = 1 + |centralPotentialConstant j| :=
  sq_sqrt (by positivity)

private theorem potential_value_identity (j x : ℝ) :
    centralPotentialValue j x = (j * x) ^ 2 + centralPotentialConstant j := by
  unfold centralPotentialValue
  ring

theorem potentialEnergyWeight_controls_position (j x : ℝ) :
    |j * x| ≤ potentialEnergyWeightConstant j * potentialEnergyWeight j x := by
  have hv : (j * x) ^ 2 ≤ |centralPotentialValue j x| + |centralPotentialConstant j| := by
    have hid := potential_value_identity j x
    have h1 := le_abs_self (centralPotentialValue j x)
    have h2 := neg_le_abs (centralPotentialConstant j)
    linarith
  have hs : |j * x| ^ 2 ≤
      (potentialEnergyWeightConstant j * potentialEnergyWeight j x) ^ 2 := by
    rw [sq_abs, mul_pow (potentialEnergyWeightConstant j) (potentialEnergyWeight j x) 2,
      potentialEnergyWeight_sq, potentialEnergyWeightConstant_sq]
    nlinarith [mul_nonneg (abs_nonneg (centralPotentialValue j x))
      (abs_nonneg (centralPotentialConstant j))]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg
    (potentialEnergyWeightConstant_pos j).le (potentialEnergyWeight_pos j x).le)).mp hs

theorem potentialEnergyWeight_le_linear (j x : ℝ) :
    potentialEnergyWeight j x ≤ potentialEnergyWeightConstant j * (1 + |j * x|) := by
  have hv : |centralPotentialValue j x| ≤ (j * x) ^ 2 + |centralPotentialConstant j| := by
    rw [potential_value_identity]
    have hsquare : |(j * x) ^ 2| = (j * x) ^ 2 := abs_of_nonneg (sq_nonneg (j * x))
    calc
      _ ≤ |(j * x) ^ 2| + |centralPotentialConstant j| :=
        abs_add_le ((j * x) ^ 2) (centralPotentialConstant j)
      _ = _ := congrArg (fun t : ℝ => t + |centralPotentialConstant j|) hsquare
  have hs : potentialEnergyWeight j x ^ 2 ≤
      potentialEnergyWeightConstant j ^ 2 * (1 + (j * x) ^ 2) := by
    rw [potentialEnergyWeight_sq, potentialEnergyWeightConstant_sq]
    nlinarith [mul_nonneg (abs_nonneg (centralPotentialConstant j)) (sq_nonneg (j * x))]
  have hlin : 1 + (j * x) ^ 2 ≤ (1 + |j * x|) ^ 2 := by
    nlinarith [abs_nonneg (j * x), sq_abs (j * x)]
  have hsq := hs.trans (mul_le_mul_of_nonneg_left hlin (sq_nonneg (potentialEnergyWeightConstant j)))
  rw [← mul_pow] at hsq
  exact (sq_le_sq₀ (potentialEnergyWeight_pos j x).le
    (mul_nonneg (potentialEnergyWeightConstant_pos j).le (by positivity))).mp hsq

def potentialPositionCoefficient (j x : ℝ) : ℝ := j * x / potentialEnergyWeight j x

def potentialBaseCoefficient (j x : ℝ) : ℝ :=
  potentialEnergyWeight j x / (1 + |j * x|)

def potentialSignedCoefficient (j x : ℝ) : ℝ :=
  potentialBaseCoefficient j x * ((j * x) / |j * x|)

theorem measurable_potentialPositionCoefficient (j : ℝ) :
    Measurable (potentialPositionCoefficient j) :=
  (measurable_const.mul measurable_id).div (continuous_potentialEnergyWeight j).measurable

theorem measurable_potentialBaseCoefficient (j : ℝ) :
    Measurable (potentialBaseCoefficient j) :=
  (continuous_potentialEnergyWeight j).measurable.div
    (measurable_const.add (continuous_abs.measurable.comp (measurable_const.mul measurable_id)))

theorem measurable_potentialSignedCoefficient (j : ℝ) :
    Measurable (potentialSignedCoefficient j) :=
  (measurable_potentialBaseCoefficient j).mul
    ((measurable_const.mul measurable_id).div
      (continuous_abs.measurable.comp (measurable_const.mul measurable_id)))

theorem potentialPositionCoefficient_abs_le (j x : ℝ) :
    |potentialPositionCoefficient j x| ≤ potentialEnergyWeightConstant j := by
  unfold potentialPositionCoefficient
  rw [abs_div, abs_of_pos (potentialEnergyWeight_pos j x)]
  exact (div_le_iff₀ (potentialEnergyWeight_pos j x)).mpr
    (potentialEnergyWeight_controls_position j x)

theorem potentialBaseCoefficient_abs_le (j x : ℝ) :
    |potentialBaseCoefficient j x| ≤ potentialEnergyWeightConstant j := by
  unfold potentialBaseCoefficient
  rw [abs_div, abs_of_pos (potentialEnergyWeight_pos j x),
    abs_of_pos (by positivity : (0 : ℝ) < 1 + |j * x|)]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 1 + |j * x|)).mpr
    (potentialEnergyWeight_le_linear j x)

theorem potentialSignedCoefficient_abs_le (j x : ℝ) :
    |potentialSignedCoefficient j x| ≤ potentialEnergyWeightConstant j := by
  unfold potentialSignedCoefficient
  rw [abs_mul, abs_div, abs_abs]
  by_cases hx : j * x = 0
  · rw [hx, abs_zero, zero_div, mul_zero]
    exact (potentialEnergyWeightConstant_pos j).le
  · rw [div_self (abs_ne_zero.mpr hx), mul_one]
    exact potentialBaseCoefficient_abs_le j x

theorem potentialPositionCoefficient_mul_weight (j x : ℝ) :
    potentialPositionCoefficient j x * potentialEnergyWeight j x = j * x :=
  div_mul_cancel₀ _ (potentialEnergyWeight_pos j x).ne'

theorem potentialEnergyWeight_decomposition (j x : ℝ) :
    potentialBaseCoefficient j x + (j * x) * potentialSignedCoefficient j x =
      potentialEnergyWeight j x := by
  have hsign : (j * x) * ((j * x) / |j * x|) = |j * x| := by
    by_cases hx : j * x = 0
    · rw [hx, abs_zero, zero_div, mul_zero]
    · calc
        _ = (j * x) ^ 2 / |j * x| := by ring
        _ = |j * x| ^ 2 / |j * x| := by rw [sq_abs]
        _ = |j * x| := by field_simp [abs_ne_zero.mpr hx]
  unfold potentialSignedCoefficient
  calc
    _ = potentialBaseCoefficient j x * (1 + |j * x|) := by
      rw [show (j * x) * (potentialBaseCoefficient j x * ((j * x) / |j * x|)) =
        potentialBaseCoefficient j x * ((j * x) * ((j * x) / |j * x|)) by ring, hsign]
      ring
    _ = _ := div_mul_cancel₀ _ (by positivity : (1 + |j * x| : ℝ) ≠ 0)

def potentialPositionMultiplier (j : ℝ) : HermiteL2 →L[ℝ] HermiteL2 :=
  boundedScalarMultiplier _ (measurable_potentialPositionCoefficient j)
    (potentialEnergyWeightConstant j) (potentialPositionCoefficient_abs_le j)

def potentialBaseMultiplier (j : ℝ) : HermiteL2 →L[ℝ] HermiteL2 :=
  boundedScalarMultiplier _ (measurable_potentialBaseCoefficient j)
    (potentialEnergyWeightConstant j) (potentialBaseCoefficient_abs_le j)

def potentialSignedMultiplier (j : ℝ) : HermiteL2 →L[ℝ] HermiteL2 :=
  boundedScalarMultiplier _ (measurable_potentialSignedCoefficient j)
    (potentialEnergyWeightConstant j) (potentialSignedCoefficient_abs_le j)

theorem potentialPositionMultiplier_ae (j : ℝ) (u : HermiteL2) :
    (potentialPositionMultiplier j u : ℝ → ℝ) =ᵐ[volume]
      (fun x => potentialPositionCoefficient j x * u x) :=
  boundedScalarMultiplier_ae _ _ _ _ u

theorem potentialBaseMultiplier_ae (j : ℝ) (u : HermiteL2) :
    (potentialBaseMultiplier j u : ℝ → ℝ) =ᵐ[volume]
      (fun x => potentialBaseCoefficient j x * u x) :=
  boundedScalarMultiplier_ae _ _ _ _ u

theorem potentialSignedMultiplier_ae (j : ℝ) (u : HermiteL2) :
    (potentialSignedMultiplier j u : ℝ → ℝ) =ᵐ[volume]
      (fun x => potentialSignedCoefficient j x * u x) :=
  boundedScalarMultiplier_ae _ _ _ _ u

private def potentialTripleAssemble (f0 f1 f2 : PhysicalEnergyTriple →L[ℝ] HermiteL2) :
    PhysicalEnergyTriple →L[ℝ] PhysicalEnergyTriple :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => HermiteL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![f0, f1, f2])

private def potentialProj (i : Fin 3) : PhysicalEnergyTriple →L[ℝ] HermiteL2 :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => HermiteL2) i

def potentialToPosition (j : ℝ) : PhysicalEnergyTriple →L[ℝ] PhysicalEnergyTriple :=
  potentialTripleAssemble (potentialProj 0) (potentialProj 1)
    ((potentialPositionMultiplier j).comp (potentialProj 2))

def positionToPotential (j : ℝ) : PhysicalEnergyTriple →L[ℝ] PhysicalEnergyTriple :=
  potentialTripleAssemble (potentialProj 0) (potentialProj 1)
    (((potentialBaseMultiplier j).comp (potentialProj 0)) +
      ((potentialSignedMultiplier j).comp (potentialProj 2)))

@[simp] theorem potentialToPosition_zero (j : ℝ) (z : PhysicalEnergyTriple) :
    potentialToPosition j z 0 = z 0 := rfl

@[simp] theorem potentialToPosition_one (j : ℝ) (z : PhysicalEnergyTriple) :
    potentialToPosition j z 1 = z 1 := rfl

@[simp] theorem potentialToPosition_two (j : ℝ) (z : PhysicalEnergyTriple) :
    potentialToPosition j z 2 = potentialPositionMultiplier j (z 2) := rfl

@[simp] theorem positionToPotential_zero (j : ℝ) (z : PhysicalEnergyTriple) :
    positionToPotential j z 0 = z 0 := rfl

@[simp] theorem positionToPotential_one (j : ℝ) (z : PhysicalEnergyTriple) :
    positionToPotential j z 1 = z 1 := rfl

@[simp] theorem positionToPotential_two (j : ℝ) (z : PhysicalEnergyTriple) :
    positionToPotential j z 2 = potentialBaseMultiplier j (z 0) + potentialSignedMultiplier j (z 2) := rfl

/-- The graph is defined by actual weak differentiation and actual
absolute-potential multiplication, before any coordinate identification. -/
def potentialEnergyGraph (j : ℝ) : Submodule ℝ PhysicalEnergyTriple where
  carrier := {z | HasWeakDerivativeL2 (z 0) (z 1) ∧
    (z 2 : ℝ → ℝ) =ᵐ[volume] (fun x => potentialEnergyWeight j x * z 0 x)}
  zero_mem' := by
    refine ⟨hasWeakDerivativeL2_zero, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx
    change (0 : HermiteL2) x = potentialEnergyWeight j x * (0 : HermiteL2) x
    rw [hx]
    simp
  add_mem' := by
    intro z w hz hw
    refine ⟨hz.1.add hw.1, ?_⟩
    filter_upwards [hz.2, hw.2, Lp.coeFn_add (z 2) (w 2),
      Lp.coeFn_add (z 0) (w 0)] with x hzx hwx h2 h0
    change (z 2 + w 2) x = potentialEnergyWeight j x * (z 0 + w 0) x
    rw [h2, h0]
    simp only [Pi.add_apply]
    rw [hzx, hwx]
    ring
  smul_mem' := by
    intro a z hz
    refine ⟨hz.1.smul a, ?_⟩
    filter_upwards [hz.2, Lp.coeFn_smul a (z 2), Lp.coeFn_smul a (z 0)] with x hz2 h2 h0
    change (a • z 2) x = potentialEnergyWeight j x * (a • z 0) x
    rw [h2, h0]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hz2]
    ring

theorem potentialToPosition_mem {j : ℝ} {z : PhysicalEnergyTriple}
    (hz : z ∈ potentialEnergyGraph j) : potentialToPosition j z ∈ physicalEnergyGraph j := by
  refine ⟨hz.1, ?_⟩
  filter_upwards [hz.2, potentialPositionMultiplier_ae j (z 2)] with x hw ha
  change potentialPositionMultiplier j (z 2) x = j * x * z 0 x
  rw [ha, hw, ← mul_assoc, potentialPositionCoefficient_mul_weight]

theorem positionToPotential_mem {j : ℝ} {z : PhysicalEnergyTriple}
    (hz : z ∈ physicalEnergyGraph j) : positionToPotential j z ∈ potentialEnergyGraph j := by
  refine ⟨hz.1, ?_⟩
  filter_upwards [hz.2, potentialBaseMultiplier_ae j (z 0),
    potentialSignedMultiplier_ae j (z 2),
    Lp.coeFn_add (potentialBaseMultiplier j (z 0)) (potentialSignedMultiplier j (z 2))]
    with x hx hb hd ha
  change (potentialBaseMultiplier j (z 0) + potentialSignedMultiplier j (z 2)) x =
    potentialEnergyWeight j x * z 0 x
  rw [ha]
  simp only [Pi.add_apply]
  rw [hb, hd, hx]
  calc
    _ = (potentialBaseCoefficient j x + (j * x) * potentialSignedCoefficient j x) * z 0 x := by ring
    _ = _ := by rw [potentialEnergyWeight_decomposition]

theorem positionToPotential_potentialToPosition {j : ℝ} {z : PhysicalEnergyTriple}
    (hz : z ∈ potentialEnergyGraph j) : positionToPotential j (potentialToPosition j z) = z := by
  have hh := positionToPotential_mem (potentialToPosition_mem hz)
  apply PiLp.ext
  intro i
  fin_cases i
  · rfl
  · rfl
  · apply Lp.ext
    filter_upwards [hh.2, hz.2] with x hf hz2
    change (positionToPotential j (potentialToPosition j z) 2) x =
      potentialEnergyWeight j x * z 0 x at hf
    exact hf.trans hz2.symm

theorem potentialToPosition_positionToPotential {j : ℝ} {z : PhysicalEnergyTriple}
    (hz : z ∈ physicalEnergyGraph j) : potentialToPosition j (positionToPotential j z) = z := by
  have hh := positionToPotential_mem hz
  apply PiLp.ext
  intro i
  fin_cases i
  · rfl
  · rfl
  · apply Lp.ext
    filter_upwards [potentialPositionMultiplier_ae j (positionToPotential j z 2), hh.2, hz.2]
      with x ha hw hz2
    change potentialPositionMultiplier j (positionToPotential j z 2) x = z 2 x
    change (positionToPotential j z 2) x = potentialEnergyWeight j x * z 0 x at hw
    rw [ha, hw, ← mul_assoc, potentialPositionCoefficient_mul_weight]
    exact hz2.symm

theorem mem_potentialEnergyGraph_iff (j : ℝ) (z : PhysicalEnergyTriple) :
    z ∈ potentialEnergyGraph j ↔
      potentialToPosition j z ∈ physicalEnergyGraph j ∧
        positionToPotential j (potentialToPosition j z) = z := by
  constructor
  · intro hz
    exact ⟨potentialToPosition_mem hz, positionToPotential_potentialToPosition hz⟩
  · rintro ⟨hp, heq⟩
    have hh := positionToPotential_mem hp
    rwa [heq] at hh

/-- Closedness follows from genuine bounded coordinate maps and the
proved physical graph, not from a spectral definition of the new domain. -/
theorem potentialEnergyGraph_isClosed (j : ℝ) :
    IsClosed (potentialEnergyGraph j : Set PhysicalEnergyTriple) := by
  have heq : (potentialEnergyGraph j : Set PhysicalEnergyTriple) =
      {z | potentialToPosition j z ∈ physicalEnergyGraph j} ∩
        {z | positionToPotential j (potentialToPosition j z) = z} := by
    ext z
    exact mem_potentialEnergyGraph_iff j z
  rw [heq]
  exact ((physicalEnergyGraph_isClosed j).preimage (potentialToPosition j).continuous).inter
    (isClosed_eq ((positionToPotential j).continuous.comp (potentialToPosition j).continuous) continuous_id)

abbrev PotentialEnergySpace (j : ℝ) := potentialEnergyGraph j

instance potentialEnergySpace_completeSpace (j : ℝ) : CompleteSpace (PotentialEnergySpace j) :=
  (potentialEnergyGraph_isClosed j).isComplete.completeSpace_coe

def potentialEnergyToPhysical (j : ℝ) : PotentialEnergySpace j →L[ℝ] PhysicalEnergySpace j :=
  ((potentialToPosition j).comp (potentialEnergyGraph j).subtypeL).codRestrict
    (physicalEnergyGraph j) (fun z => potentialToPosition_mem z.property)

def physicalEnergyToPotential (j : ℝ) : PhysicalEnergySpace j →L[ℝ] PotentialEnergySpace j :=
  ((positionToPotential j).comp (physicalEnergyGraph j).subtypeL).codRestrict
    (potentialEnergyGraph j) (fun z => positionToPotential_mem z.property)

theorem physicalEnergyToPotential_potentialEnergyToPhysical (j : ℝ) (z : PotentialEnergySpace j) :
    physicalEnergyToPotential j (potentialEnergyToPhysical j z) = z :=
  Subtype.ext (positionToPotential_potentialToPosition z.property)

theorem potentialEnergyToPhysical_physicalEnergyToPotential (j : ℝ) (z : PhysicalEnergySpace j) :
    potentialEnergyToPhysical j (physicalEnergyToPotential j z) = z :=
  Subtype.ext (potentialToPosition_positionToPotential z.property)

/-- Actual compact smooth test functions in the potential-weighted graph.
The weighted third coordinate is not required to be a smooth function. -/
def potentialCompactSmoothCore (j : ℝ) : Set PhysicalEnergyTriple :=
  {z | ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    (z 0 : ℝ → ℝ) =ᵐ[volume] φ ∧
    (z 1 : ℝ → ℝ) =ᵐ[volume] deriv φ ∧
    (z 2 : ℝ → ℝ) =ᵐ[volume] (fun x => potentialEnergyWeight j x * φ x)}

theorem positionToPotential_compact_lift (j : ℝ) (φ : ℝ → ℝ)
    (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    positionToPotential j (physicalEnergyLift j (compactSmooth_energyDomain hs hc)).val ∈
      potentialCompactSmoothCore j := by
  let V := physicalEnergyLift j (compactSmooth_energyDomain hs hc)
  have hb : (V.val 0 : ℝ → ℝ) =ᵐ[volume] φ := by
    change (physicalEnergyBase j V : ℝ → ℝ) =ᵐ[volume] φ
    rw [physicalEnergyLift_base]
    exact MemLp.coeFn_toLp _
  have hd : (V.val 1 : ℝ → ℝ) =ᵐ[volume] deriv φ := by
    change (physicalEnergyDerivative j V : ℝ → ℝ) =ᵐ[volume] deriv φ
    rw [physicalEnergyLift_derivative]
    exact MemLp.coeFn_toLp _
  refine ⟨φ, hs, hc, hb, hd, ?_⟩
  have hw := (positionToPotential_mem V.property).2
  filter_upwards [hw, hb] with x hx hb
  change (positionToPotential j V.val 2) x = potentialEnergyWeight j x * φ x
  change (positionToPotential j V.val 2) x = potentialEnergyWeight j x * V.val 0 x at hx
  rw [hx, hb]

theorem potentialCompactSmoothCore_subset (j : ℝ) :
    potentialCompactSmoothCore j ⊆ (potentialEnergyGraph j : Set PhysicalEnergyTriple) := by
  rintro z ⟨φ, hs, hc, hz0, hz1, hz2⟩
  let V := physicalEnergyLift j (compactSmooth_energyDomain hs hc)
  have hb : (V.val 0 : ℝ → ℝ) =ᵐ[volume] φ := by
    change (physicalEnergyBase j V : ℝ → ℝ) =ᵐ[volume] φ
    rw [physicalEnergyLift_base]
    exact MemLp.coeFn_toLp _
  have hd : (V.val 1 : ℝ → ℝ) =ᵐ[volume] deriv φ := by
    change (physicalEnergyDerivative j V : ℝ → ℝ) =ᵐ[volume] deriv φ
    rw [physicalEnergyLift_derivative]
    exact MemLp.coeFn_toLp _
  have hw : (positionToPotential j V.val 2 : ℝ → ℝ) =ᵐ[volume]
      (fun x => potentialEnergyWeight j x * φ x) := by
    have hraw := (positionToPotential_mem V.property).2
    filter_upwards [hraw, hb] with x hx hbase
    change (positionToPotential j V.val 2) x = potentialEnergyWeight j x * V.val 0 x at hx
    rw [hx, hbase]
  have heq : z = positionToPotential j V.val := by
    apply PiLp.ext
    intro i
    fin_cases i
    · apply Lp.ext
      exact hz0.trans hb.symm
    · apply Lp.ext
      exact hz1.trans hd.symm
    · apply Lp.ext
      exact hz2.trans hw.symm
  rw [heq]
  exact positionToPotential_mem V.property

/-- Compact smooth tests are dense in the actual potential-weighted
domain. The transported core is identified with the genuine test core. -/
theorem potentialCompactSmoothCore_closure {j : ℝ} (hj : 0 < j) :
    closure (potentialCompactSmoothCore j) = (potentialEnergyGraph j : Set PhysicalEnergyTriple) := by
  apply le_antisymm
  · exact closure_minimal (potentialCompactSmoothCore_subset j) (potentialEnergyGraph_isClosed j)
  · intro z hz
    let V : PhysicalEnergySpace j := ⟨potentialToPosition j z, potentialToPosition_mem hz⟩
    let f : PhysicalEnergySpace j → PhysicalEnergyTriple := fun U => positionToPotential j U.val
    have hf : Continuous f :=
      (positionToPotential j).continuous.comp (physicalEnergyGraph j).subtypeL.continuous
    have hV : V ∈ closure (physicalCompactSmoothCore j : Set (PhysicalEnergySpace j)) := by
      change V ∈ (physicalCompactSmoothCore j).topologicalClosure
      rw [physicalCompactSmoothCore_dense hj]
      trivial
    have him : f '' (physicalCompactSmoothCore j : Set (PhysicalEnergySpace j)) ⊆
        potentialCompactSmoothCore j := by
      rintro _ ⟨U, hU, rfl⟩
      obtain ⟨φ, hs, hc, rfl⟩ := hU
      exact positionToPotential_compact_lift j φ hs hc
    have hsub : f '' closure (physicalCompactSmoothCore j : Set (PhysicalEnergySpace j)) ⊆
        closure (potentialCompactSmoothCore j) :=
      (image_closure_subset_closure_image hf).trans (closure_mono him)
    have hzcl := hsub ⟨V, hV, rfl⟩
    have heq : f V = z := positionToPotential_potentialToPosition hz
    rwa [heq] at hzcl

private theorem potential_l2_inner_integral (u v : HermiteL2) :
    ⟪u, v⟫_ℝ = ∫ x : ℝ, u x * v x := by
  rw [L2.inner_def]
  congr 1
  funext x
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem physical_potential_pairing_ae {j : ℝ} {z w : PhysicalEnergyTriple}
    (hz : z ∈ physicalEnergyGraph j) (hw : w ∈ physicalEnergyGraph j) :
    (fun x => centralPotentialValue j x * z 0 x * w 0 x) =ᵐ[volume]
      (fun x => z 2 x * w 2 x + centralPotentialConstant j * (z 0 x * w 0 x)) := by
  filter_upwards [hz.2, hw.2] with x hx hy
  change centralPotentialValue j x * z 0 x * w 0 x =
    z 2 x * w 2 x + centralPotentialConstant j * (z 0 x * w 0 x)
  rw [hx, hy]
  unfold centralPotentialValue
  ring

/-- The signed potential term is genuinely integrable on the physical
domain, as a sum of two products of actual L2 functions. -/
theorem physical_potential_integrable {j : ℝ} {z w : PhysicalEnergyTriple}
    (hz : z ∈ physicalEnergyGraph j) (hw : w ∈ physicalEnergyGraph j) :
    Integrable (fun x => centralPotentialValue j x * z 0 x * w 0 x) volume := by
  have hp : Integrable (fun x => z 2 x * w 2 x) volume :=
    (Lp.memLp (z 2)).integrable_mul (Lp.memLp (w 2))
  have hb : Integrable (fun x => z 0 x * w 0 x) volume :=
    (Lp.memLp (z 0)).integrable_mul (Lp.memLp (w 0))
  exact (hp.add (hb.const_mul (centralPotentialConstant j))).congr
    (physical_potential_pairing_ae hz hw).symm

theorem physical_potential_integral {j : ℝ} {z w : PhysicalEnergyTriple}
    (hz : z ∈ physicalEnergyGraph j) (hw : w ∈ physicalEnergyGraph j) :
    (∫ x, centralPotentialValue j x * z 0 x * w 0 x) =
      ⟪z 2, w 2⟫_ℝ + centralPotentialConstant j * ⟪z 0, w 0⟫_ℝ := by
  have hp : Integrable (fun x => z 2 x * w 2 x) volume :=
    (Lp.memLp (z 2)).integrable_mul (Lp.memLp (w 2))
  have hb : Integrable (fun x => z 0 x * w 0 x) volume :=
    (Lp.memLp (z 0)).integrable_mul (Lp.memLp (w 0))
  rw [integral_congr_ae (physical_potential_pairing_ae hz hw),
    integral_add (f := fun x => z 2 x * w 2 x)
      (g := fun x => centralPotentialConstant j * (z 0 x * w 0 x)) hp
      (hb.const_mul (centralPotentialConstant j)), integral_const_mul,
    ← potential_l2_inner_integral, ← potential_l2_inner_integral]

theorem potentialEnergy_integrable {j : ℝ} (z w : PotentialEnergySpace j) :
    Integrable (fun x => centralPotentialValue j x * z.val 0 x * w.val 0 x) volume :=
  physical_potential_integrable (z := potentialToPosition j z.val) (w := potentialToPosition j w.val)
    (potentialToPosition_mem z.property) (potentialToPosition_mem w.property)

theorem physicalEnergy_inner_potential (j : ℝ) (z w : PhysicalEnergySpace j) :
    ⟪z, w⟫_ℝ = ⟪z.val 1, w.val 1⟫_ℝ +
      (∫ x, centralPotentialValue j x * z.val 0 x * w.val 0 x) +
      centralEnergyShift j * ⟪z.val 0, w.val 0⟫_ℝ := by
  rw [physicalEnergy_inner_coordinates]
  change ⟪z.val 0, w.val 0⟫_ℝ + ⟪z.val 1, w.val 1⟫_ℝ + ⟪z.val 2, w.val 2⟫_ℝ = _
  rw [physical_potential_integral z.property w.property]
  unfold centralEnergyShift centralPotentialConstant
  ring

/-- Association with the actual signed differential form on the actual
absolute-potential domain, quantified over all physical energy vectors. -/
def PotentialClosedFormEquation (j : ℝ) (u v : HermiteL2) : Prop :=
  ∃ z : PotentialEnergySpace j, z.val 0 = u ∧
    ∀ w : PotentialEnergySpace j,
      Integrable (fun x => centralPotentialValue j x * z.val 0 x * w.val 0 x) volume ∧
        ⟪v, w.val 0⟫_ℝ = ⟪z.val 1, w.val 1⟫_ℝ +
          ∫ x, centralPotentialValue j x * z.val 0 x * w.val 0 x

theorem potentialClosedFormEquation_iff_physical (j : ℝ) (u v : HermiteL2) :
    PotentialClosedFormEquation j u v ↔ PhysicalClosedFormEquation j u v := by
  constructor
  · rintro ⟨z, hz, heq⟩
    let Z : PhysicalEnergySpace j := potentialEnergyToPhysical j z
    refine ⟨Z, hz, ?_⟩
    intro V
    have hE : ⟪v, V.val 0⟫_ℝ = ⟪z.val 1, V.val 1⟫_ℝ +
        ∫ x, centralPotentialValue j x * z.val 0 x * V.val 0 x :=
      (heq (physicalEnergyToPotential j V)).2
    have hP := physicalEnergy_inner_potential j Z V
    change ⟪Z, V⟫_ℝ = ⟪z.val 1, V.val 1⟫_ℝ +
      (∫ x, centralPotentialValue j x * z.val 0 x * V.val 0 x) +
      centralEnergyShift j * ⟪z.val 0, V.val 0⟫_ℝ at hP
    rw [inner_add_left, real_inner_smul_left]
    change ⟪Z, V⟫_ℝ = ⟪v, V.val 0⟫_ℝ + centralEnergyShift j * ⟪u, V.val 0⟫_ℝ
    rw [← hz]
    linarith only [hP, hE]
  · rintro ⟨Z, hZ, heq⟩
    let z : PotentialEnergySpace j := physicalEnergyToPotential j Z
    refine ⟨z, hZ, ?_⟩
    intro w
    refine ⟨potentialEnergy_integrable z w, ?_⟩
    let V : PhysicalEnergySpace j := potentialEnergyToPhysical j w
    have hE := heq V
    rw [inner_add_left, real_inner_smul_left] at hE
    change ⟪Z, V⟫_ℝ = ⟪v, w.val 0⟫_ℝ + centralEnergyShift j * ⟪u, w.val 0⟫_ℝ at hE
    have hP := physicalEnergy_inner_potential j Z V
    change ⟪Z, V⟫_ℝ = ⟪Z.val 1, w.val 1⟫_ℝ +
      (∫ x, centralPotentialValue j x * Z.val 0 x * w.val 0 x) +
      centralEnergyShift j * ⟪Z.val 0, w.val 0⟫_ℝ at hP
    have hb : Z.val 0 = u := hZ
    rw [← hb] at hE
    change ⟪v, w.val 0⟫_ℝ = ⟪Z.val 1, w.val 1⟫_ℝ +
      ∫ x, centralPotentialValue j x * Z.val 0 x * w.val 0 x
    linarith only [hP, hE]

theorem potentialClosedFormEquation_iff_centralClosedGraph {j : ℝ} (hj : 0 < j)
    (u v : HermiteL2) :
    PotentialClosedFormEquation j u v ↔ (u, v) ∈ centralClosedGraph hj :=
  (potentialClosedFormEquation_iff_physical j u v).trans
    (physicalClosedFormEquation_iff_centralClosedGraph hj u v)

theorem centralPotentialValue_lower (j x : ℝ) :
    -|centralPotentialConstant j| ≤ centralPotentialValue j x := by
  unfold centralPotentialValue
  nlinarith [mul_nonneg (sq_nonneg j) (sq_nonneg x), neg_le_abs (centralPotentialConstant j)]

end ContinuousFlexibility.Radial
