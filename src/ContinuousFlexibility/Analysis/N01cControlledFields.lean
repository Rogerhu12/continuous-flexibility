import ContinuousFlexibility.Analysis.N01cCoefficientPolarPowerInputs

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
  {U : Set X} {Ω : Set PolarPoint} {H E : PolarPoint → ℝ}

/-- A genuine scalar field together with its actual mixed towers and
their distributed-order bounds. -/
structure PowerControlledField (p : ℕ → Seminorm ℝ X) (center : X)
    (base loss : ℕ) (U : Set X) (Ω : Set PolarPoint) (H E : PolarPoint → ℝ) where
  value : X → PolarPoint → ℝ
  regular : MixedJetRegularity U Ω value
  bounds : MixedPowerBounds p center base loss U Ω H E value

namespace PowerControlledField

def add (F G : PowerControlledField p center base loss U Ω H E)
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hH : ∀ q ∈ Ω, 0 ≤ H q) (hE : ∀ q ∈ Ω, 1 ≤ E q) :
    PowerControlledField p center base loss U Ω H E :=
  ⟨fun x q => F.value x q + G.value x q, F.regular.add G.regular hU hΩ,
    F.bounds.add G.bounds F.regular G.regular hΩ hH hE⟩

def mul (F G : PowerControlledField p center base loss U Ω H E)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hE : ∀ q ∈ Ω, 1 ≤ E q)
    {RH : ℝ} (hH : ∀ q ∈ Ω, 0 ≤ H q ∧ H q ≤ RH) :
    PowerControlledField p center base loss U Ω H E :=
  ⟨fun x q => F.value x q * G.value x q, F.regular.mul G.regular hU hΩ,
    F.bounds.mul G.bounds F.regular G.regular hΩ hE hH⟩

def scalarComp (F : PowerControlledField p center base loss U Ω H E)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hE : ∀ q ∈ Ω, 1 ≤ E q)
    {RH : ℝ} (hH : ∀ q ∈ Ω, 0 ≤ H q ∧ H q ≤ RH)
    {V K : Set ℝ} (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    (g : ℝ → ℝ) (hg : ContDiffOn ℝ ∞ g V)
    (hmap : ∀ x ∈ U, MapsTo (F.value x) Ω K) :
    PowerControlledField p center base loss U Ω H E :=
  ⟨fun x q => g (F.value x q),
    F.regular.scalarComp hU hΩ hV hg (fun x hx q hq => hKV (hmap x hx hq)),
    F.bounds.scalarComp F.regular hU hΩ hE hH hV hK hKV hg hmap⟩

def const (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hH : ∀ q ∈ Ω, 0 ≤ H q) (hE : ∀ q ∈ Ω, 1 ≤ E q) (c : ℝ) :
    PowerControlledField p center base loss U Ω H E := by
  refine ⟨fun _ _ => c, MixedJetRegularity.const hU hΩ c, ?_⟩
  apply mixedPowerBounds_parameterIndependent hH hE
  intro s
  refine ⟨1 + ‖c‖, 0, le_add_of_nonneg_right (norm_nonneg c), le_rfl, fun a b hab q hq => ?_⟩
  have hc : ‖mixedDerivative a b (fun _ : PolarPoint => c) q‖ ≤ ‖c‖ := by
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
      simp [mixedDerivative, iteratedDeriv_const, ha, hb]
  simpa only [Real.rpow_zero, mul_one] using
    hc.trans (le_add_of_nonneg_left zero_le_one)

end PowerControlledField

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

/-- The fixed radial reciprocal has bounded genuine jets on the closed
reference radial interval, independently of the state and angular point. -/
def coefficientRadiusInverse_controlled
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hD : RadialProfileGeometry D)
    (C : NonlinearGeometryData S) (base loss : ℕ) (ε : ℝ)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    PowerControlledField (pairGrading (stateGrading S) realGrading) (C.referenceState, 0)
      base loss (stateNeighborhood S C base ε) (annularOpen D)
      (fun q => T.H q.1 ^ (3 / 4 : ℝ)) (fun q => T.E0 q.1) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  have hH (q : PolarPoint) (hq : q ∈ annularOpen D) :
      0 ≤ T.H q.1 ^ (3 / 4 : ℝ) := Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le _
  have hi (r : ℝ) (hr : r ∈ Icc D.a D.b) : ContDiffAt ℝ ∞ (fun t : ℝ => t⁻¹) r :=
    contDiffAt_id.inv (hD.1.trans_le hr.1).ne'
  have hs : ContDiffOn ℝ ∞ (fun q : PolarPoint => q.1⁻¹) (annularOpen D) :=
    fun q hq => (contDiffAt_fst.inv (hD.1.trans hq.1.1).ne').contDiffWithinAt
  refine ⟨fun _ q => q.1⁻¹,
    ⟨fun _ _ => hs, fun a b q _ =>
      smoothDirections_constant (isOpen_stateNeighborhood S C base ε) _⟩, ?_⟩
  apply mixedPowerBounds_parameterIndependent hH (fun q hq => hE q.1 hq.1)
  intro s
  obtain ⟨B, hB, hb⟩ := compact_iteratedFDeriv_bound isCompact_Icc hi s
  refine ⟨max 1 B, 0, le_max_left _ _, le_rfl, fun a b hab q hq => ?_⟩
  rw [mixedDerivative_radialFunction]
  by_cases hb0 : b = 0
  · rw [if_pos hb0]
    have hh := hb a (by omega) q.1 ⟨hq.1.1.le, hq.1.2.le⟩
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.rpow_zero, mul_one] using
      hh.trans (le_max_right 1 B)
  · simp only [if_neg hb0, norm_zero, Real.rpow_zero, mul_one]
    exact zero_le_one.trans (le_max_left _ _)

end ContinuousFlexibility.Statements
