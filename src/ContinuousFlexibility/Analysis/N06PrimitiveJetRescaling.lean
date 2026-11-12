import ContinuousFlexibility.Statements.N06PrimitiveGeometryBridge
import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient
import ContinuousFlexibility.Analysis.N05ReferenceResidual
import ContinuousFlexibility.Analysis.TameLocalCalculus
import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace
import ContinuousFlexibility.Analysis.SpacesCylinderIntegration

/-!
# Actual state differences on the original canonical intervals

The primitive current jets are already differences of the actual functions.
This module only translates the state parameter and undoes the radial affine
rescaling. Both length atoms share one reference bound. Their product is one,
so that common bound is at least one, without a lower bound `E0 ≥ 1`.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

private theorem n06_add_state_difference {E : Type*} [AddCommGroup E]
    (x y : E) : x + (y - x) = y :=
  (add_comm x (y - x)).trans (sub_add_cancel y x)

private theorem n06_submodule_parameter_grading
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (U : Submodule ℝ E)
    (n : ℕ) (x : U) (q : ℝ) :
    pairGrading (fun k => (p k).comp U.subtype) realGrading n (x, q) =
      p n x.val + |q| := by
  rw [pairGrading_apply]
  change p n x.val + ‖q‖ = p n x.val + |q|
  exact congrArg (fun r : ℝ => p n x.val + r) (Real.norm_eq_abs q)

def n06PrimitiveParameterOfState (href : referenceStateConditions D S C)
    (z : AnnularState S × ℝ) (hs : stateSector S z.1) : Parameter S :=
  (⟨z.1 - C.referenceState,
    (stateSectorSubmodule S).sub_mem hs (n05_referenceState_sector href)⟩, z.2)

theorem n06PrimitiveParameterOfState_lift (href : referenceStateConditions D S C)
    (z : AnnularState S × ℝ) (hs : stateSector S z.1) :
    liftSectorParameter S C (n06PrimitiveParameterOfState href z hs) = z := by
  apply Prod.ext
  · change C.referenceState + (z.1 - C.referenceState) = z.1
    exact n06_add_state_difference C.referenceState z.1
  · rfl

theorem n06PrimitiveParameterOfState_mem (href : referenceStateConditions D S C)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    n06PrimitiveParameterOfState href z hs ∈ sectorNeighborhood S base ε ε := hz

theorem n06PrimitiveParameterOfState_grading (href : referenceStateConditions D S C)
    (z : AnnularState S × ℝ) (hs : stateSector S z.1) (n : ℕ) :
    parameterGrading S n (n06PrimitiveParameterOfState href z hs) =
      stateGrading S n (z.1 - C.referenceState) + |z.2| := by
  exact n06_submodule_parameter_grading (stateGrading S) (stateSectorSubmodule S) n
    (n06PrimitiveParameterOfState href z hs).1
    (n06PrimitiveParameterOfState href z hs).2

private def N06PrimitiveCurrentJetOrderBound
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (base : ℕ) (ε : ℝ) (d s : ℕ) (B : ℝ) : Prop :=
  0 < B ∧ ∀ w ∈ sectorNeighborhood S base ε ε, ∀ m a (p : unitStrip),
    ∀ i j : ℕ, i + j ≤ s →
      |differenceJets D T S C L K w a m i j p| ≤
        B * T.E0 (T.sample (K.cell m)) ^ B *
          T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * parameterGrading S (s + d) w

private theorem n06_currentJets_zero_bounds
    (hcur : CurrentJets D T S C L K base ε) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ,
      N06PrimitiveCurrentJetOrderBound D T S C L K base ε d s B :=
  hcur.2.1

/-- The state loss is selected once, before every spatial order. -/
theorem n06_primitive_currentAtom_difference_jets
    (href : referenceStateConditions D S C)
    (hcur : CurrentJets D T S C L K base ε) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ stateNeighborhood S C base ε, ∀ hs : stateSector S z.1,
      ∀ m a p, p ∈ unitStrip → ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j
          (fun q => atom D T S C L K z m a q -
            atom D T S C L K (C.referenceState, 0) m a q) p| ≤
          B * T.E0 (T.sample (K.cell m)) ^ B *
            T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
              (stateGrading S (s + d) (z.1 - C.referenceState) + |z.2|) := by
  obtain ⟨d, hd⟩ := n06_currentJets_zero_bounds hcur
  refine ⟨d, fun s => ?_⟩
  obtain ⟨B, hb⟩ := hd s
  refine ⟨B, hb.1, ?_⟩
  intro z hz hs m a p hp i j hij
  have h := hb.2 (n06PrimitiveParameterOfState href z hs)
    (n06PrimitiveParameterOfState_mem href hz hs) m a ⟨p, hp⟩ i j hij
  simpa only [differenceJets, n06PrimitiveParameterOfState_lift,
    n06PrimitiveParameterOfState_grading] using h

private theorem n06_length_and_inverse_common_bound {ell U : ℝ}
    (hell : 0 < ell) (h : |ell| ≤ U) (hi : |ell⁻¹| ≤ U) : 1 ≤ U := by
  have hU : 0 ≤ U := (abs_nonneg ell).trans h
  have hprod : 1 ≤ U * U := by
    calc
      1 = |ell| * |ell⁻¹| := by rw [← abs_mul, mul_inv_cancel₀ hell.ne', abs_one]
      _ ≤ U * U := mul_le_mul h hi (abs_nonneg _) hU
  nlinarith only [hprod, hU]

/-- Both actual canonical length atoms have the same positive envelope.
This is the only normalization used when comparing its finite powers. -/
theorem n06_referenceCanonicalLength_envelope
    (href : ReferenceJets D T S C L K)
    (hlen : ∀ m, K.left m < K.right m) :
    ∃ B : ℝ, 0 < B ∧ ∀ m,
      1 ≤ B * T.E0 (T.sample (K.cell m)) ^ B ∧
      |K.right m - K.left m| ≤ B * T.E0 (T.sample (K.cell m)) ^ B ∧
      |(K.right m - K.left m)⁻¹| ≤ B * T.E0 (T.sample (K.cell m)) ^ B := by
  obtain ⟨B, hB, hb⟩ := href.2 0
  refine ⟨B, hB, fun m => ?_⟩
  have hp : ((1 / 2, 0) : PolarPoint) ∈ unitStrip := by
    constructor <;> norm_num
  have hl : |K.right m - K.left m| ≤ B * T.E0 (T.sample (K.cell m)) ^ B := by
    simpa only [spaces_mixedDerivative_zero, atom] using
      hb m .canonicalLength (1 / 2, 0) hp 0 0 (by omega)
  have hi : |(K.right m - K.left m)⁻¹| ≤ B * T.E0 (T.sample (K.cell m)) ^ B := by
    simpa only [spaces_mixedDerivative_zero, atom] using
      hb m .canonicalLengthInverse (1 / 2, 0) hp 0 0 (by omega)
  exact ⟨n06_length_and_inverse_common_bound (sub_pos.mpr (hlen m)) hl hi, hl, hi⟩

/-- A field equality only on the open unit strip transports every actual
mixed jet. No global smooth extension of either field is used. -/
theorem n06_mixedJet_of_unit_identity (m : ℕ) (hlen : K.left m < K.right m)
    {f g : PolarPoint → ℝ}
    (heq : EqOn (f ∘ canonicalUnitPoint K m) g unitStrip)
    (a j : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    mixedDerivative a j f p = (K.right m - K.left m)⁻¹ ^ a *
      mixedDerivative a j g (n07aCanonicalUnitInversePoint K m p) := by
  let q := n07aCanonicalUnitInversePoint K m p
  have hq : q ∈ unitStrip := n07aCanonicalUnitInversePoint_maps hlen hp
  have h := n07a_mixedDerivative_radialAffine f (K.left m)
    (K.right m - K.left m) a j q
  change mixedDerivative a j (f ∘ canonicalUnitPoint K m) q =
    (K.right m - K.left m) ^ a * mixedDerivative a j f (canonicalUnitPoint K m q) at h
  dsimp only [q] at h
  rw [n07aCanonicalUnitPoint_inverse hlen p] at h
  have hg := mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) heq a j hq
  have hne : K.right m - K.left m ≠ 0 := (sub_pos.mpr hlen).ne'
  calc
    mixedDerivative a j f p = (K.right m - K.left m)⁻¹ ^ a *
        ((K.right m - K.left m) ^ a * mixedDerivative a j f p) := by
      rw [← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero a hne), one_mul]
    _ = (K.right m - K.left m)⁻¹ ^ a *
        mixedDerivative a j (f ∘ canonicalUnitPoint K m) q := by rw [h]
    _ = _ := congrArg (fun v : ℝ => (K.right m - K.left m)⁻¹ ^ a * v) hg

/-- One fixed finite spatial order costs one fixed coefficient power,
with the full `H^(3/4)` attenuation retained. -/
theorem n06_inverseLength_weighted_jet_bound
    {ell E H B P rho v : ℝ} {a n : ℕ}
    (hell : 0 < ell) (hE : 0 < E) (hH : 0 ≤ H)
    (hB : 0 ≤ B) (hP : 0 ≤ P) (hrho : 0 ≤ rho) (han : a ≤ n)
    (hunit : 1 ≤ P * E ^ P) (hinv : |ell⁻¹| ≤ P * E ^ P)
    (hv : |v| ≤ B * E ^ B * H * rho) :
    |ell⁻¹ ^ a * v| ≤ (B * P ^ n * rho) * (H * E ^ (B + P * n)) := by
  have hpower : ell⁻¹ ^ a ≤ (P * E ^ P) ^ n :=
    (pow_le_pow_left₀ (inv_nonneg.mpr hell.le)
      ((le_abs_self _).trans hinv) a).trans (pow_le_pow_right₀ hunit han)
  rw [abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hell.le) a)]
  calc
    ell⁻¹ ^ a * |v| ≤ (P * E ^ P) ^ n * (B * E ^ B * H * rho) :=
      mul_le_mul hpower hv (abs_nonneg _) (pow_nonneg (zero_le_one.trans hunit) n)
    _ = (B * P ^ n * rho) * (H * E ^ (B + P * n)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hE.le P n, Real.rpow_add hE]
      ring

end ContinuousFlexibility.Statements
