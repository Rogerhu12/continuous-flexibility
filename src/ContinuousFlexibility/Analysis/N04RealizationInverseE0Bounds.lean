module

public import ContinuousFlexibility.Analysis.N04RealizationAtomFrechetBounds
public import ContinuousFlexibility.Analysis.N07aInverseChartBounds

/-!
# Actual inverse-coordinate jets with sampled E0 powers

The normalized radial atom and the angular defect determine the stored
inverse chart. The physical interval length is bounded by its own static
reference atom. Their Fréchet bounds therefore retain an E0 power and one
state loss. Only positive derivatives of the unwrapped angular coordinate
are estimated; its unbounded value is never put into the envelope.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem n04Realization_inverseCoordinate_numeric_bound
    {v ell E P B rho : ℝ} (hE : 1 ≤ E) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hrho : 1 ≤ rho) (hell : ell ≤ P * E ^ P)
    (hv : v ≤ ell * (B * E ^ B * rho) + 1 + B * E ^ B * rho) :
    v ≤ (P * B + 1 + B) * E ^ (P + B) * rho := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hρ : 0 ≤ rho := zero_le_one.trans hrho
  have hfactor : 0 ≤ B * E ^ B * rho :=
    mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hE0.le _)) hρ
  have hEB : E ^ B ≤ E ^ (P + B) :=
    Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_left hP)
  have hpower : 1 ≤ E ^ (P + B) := by
    calc
      1 = E ^ (0 : ℝ) := (Real.rpow_zero E).symm
      _ ≤ E ^ (P + B) :=
        Real.rpow_le_rpow_of_exponent_le hE (add_nonneg hP hB)
  have hone : 1 ≤ E ^ (P + B) * rho := by
    calc
      1 ≤ E ^ (P + B) := hpower
      _ ≤ E ^ (P + B) * rho := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hrho
          (Real.rpow_nonneg hE0.le _)
  calc
    v ≤ ell * (B * E ^ B * rho) + 1 + B * E ^ B * rho := hv
    _ ≤ (P * E ^ P) * (B * E ^ B * rho) + 1 + B * E ^ B * rho :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hell hfactor) le_rfl) le_rfl
    _ = P * B * E ^ (P + B) * rho + 1 + B * E ^ B * rho := by
      rw [Real.rpow_add hE0]
      ring
    _ ≤ P * B * E ^ (P + B) * rho + E ^ (P + B) * rho +
        B * E ^ (P + B) * rho :=
      add_le_add (add_le_add le_rfl hone)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEB hB) hρ)
    _ = (P * B + 1 + B) * E ^ (P + B) * rho := by ring

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
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}

private theorem n04Realization_physicalLength_coefficient_bound
    (href : ReferenceJets D T S C L K) :
    ∃ P : ℝ, 0 < P ∧ ∀ m,
      |K.physicalRight m - K.physicalLeft m| ≤
        P * T.E0 (T.sample (K.cell m)) ^ P := by
  obtain ⟨P, hP, hb⟩ := href.2 0
  have hp : ((1 / 2, 0) : PolarPoint) ∈ unitStrip := by
    constructor <;> norm_num
  refine ⟨P, hP, fun m => ?_⟩
  simpa only [spaces_mixedDerivative_zero, atom] using
    hb m .physicalLength (1 / 2, 0) hp 0 0 (by omega)

/-- The genuine stored inverse has uniform positive-order Fréchet bounds
with the original sampled E0 envelope. The same neighborhood and fixed
loss work at every spatial order. -/
theorem n04Realization_inverseChart_positive_E0_jets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hrefState : referenceStateConditions D S C)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hlen : ∀ m, K.left m < K.right m)
    (hphysical : ∀ m, K.physicalLeft m < K.physicalRight m)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m))) :
    ∃ d : ℕ, ∀ n : ℕ, 0 < n → ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ∀ m x, x ∈ canonicalOpen S K m →
          ‖iteratedFDeriv ℝ n (K.inverseChart z m) x‖ ≤
            B * T.E0 (T.sample (K.cell m)) ^ B *
              (1 + stateGrading S (n + d) (z.1 - C.referenceState) + |z.2|) := by
  obtain ⟨P, hP, hlength⟩ := n04Realization_physicalLength_coefficient_bound href
  obtain ⟨d, hscalar⟩ :=
    n04Realization_canonicalAtom_frechet_bounds hD hT hrefState href hcur hlen hfloor
  refine ⟨d, fun n hn => ?_⟩
  obtain ⟨A, hA, hnorm⟩ := hscalar n
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (P * A + 1 + A) (P + A)
  refine ⟨B, hB, fun z hz hs m x hx => ?_⟩
  let ζ : Parameter S := n06PrimitiveParameterOfState hrefState z hs
  have hζ : ζ ∈ sectorNeighborhood S base ε ε :=
    n06PrimitiveParameterOfState_mem hrefState hz hs
  have hlift : liftSectorParameter S C ζ = z :=
    n06PrimitiveParameterOfState_lift hrefState z hs
  let f : Atom → PolarPoint → ℝ := fun a => n07aCanonicalAtomField D T S C L K a ζ m
  have hfs (a : Atom) : ContDiffOn ℝ ∞ (f a) (canonicalOpen S K m) :=
    n07a_canonicalAtomField_smooth hcur hlen a ζ hζ m
  have hidentity (a : Atom) :
      EqOn (f a ∘ canonicalUnitPoint K m) (atom D T S C L K z m a) unitStrip := by
    simpa only [hlift] using
      n04Realization_canonicalAtom_unit_identity (D := D) (T := T) (S := S) (C := C) (L := L)
        ζ m a (hlen m)
  let E : ℝ := T.E0 (T.sample (K.cell m))
  let rho : ℝ := 1 + stateGrading S (n + d) (z.1 - C.referenceState) + |z.2|
  have hrho : 1 ≤ rho := by
    dsimp only [rho]
    linarith only [apply_nonneg (stateGrading S (n + d)) (z.1 - C.referenceState),
      abs_nonneg z.2]
  have hrad : ‖iteratedFDeriv ℝ n (f .inverseRadial) x‖ ≤ A * E ^ A * rho :=
    hnorm z hz hs m .inverseRadial (f .inverseRadial)
      (hfs .inverseRadial) (hidentity .inverseRadial) x hx
  have hang : ‖iteratedFDeriv ℝ n (f .inverseAngleDefect) x‖ ≤ A * E ^ A * rho :=
    hnorm z hz hs m .inverseAngleDefect (f .inverseAngleDefect)
      (hfs .inverseAngleDefect) (hidentity .inverseAngleDefect) x hx
  have heq : K.inverseChart z m = fun y =>
      (K.physicalLeft m + (K.physicalRight m - K.physicalLeft m) * f .inverseRadial y,
        y.2 + f .inverseAngleDefect y) := by
    simpa only [hlift] using
      n07a_inverseChart_eq_rawAtoms (D := D) (T := T) (C := C) (L := L)
        m (hlen m) (hphysical m) ζ
  have hcoord := n07a_coordinatePair_iteratedFDeriv_bound
    ((hfs .inverseRadial).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hx))
    ((hfs .inverseAngleDefect).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hx))
    (K.physicalLeft m) (K.physicalRight m - K.physicalLeft m) hn
  have hraw : ‖iteratedFDeriv ℝ n (K.inverseChart z m) x‖ ≤
      |K.physicalRight m - K.physicalLeft m| * (A * E ^ A * rho) + 1 +
        A * E ^ A * rho :=
    (congrArg (fun F : PolarPoint → PolarPoint => ‖iteratedFDeriv ℝ n F x‖) heq).le.trans
      (hcoord.trans (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hrad (abs_nonneg _)) le_rfl) hang))
  have hbound := n04Realization_inverseCoordinate_numeric_bound
    (hfloor m) hP.le hA.le hrho (hlength m) hraw
  exact hbound.trans (mul_le_mul_of_nonneg_right (hpack E (hfloor m))
    (zero_le_one.trans hrho))

end ContinuousFlexibility.Analysis
