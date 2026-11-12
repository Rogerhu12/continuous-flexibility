import ContinuousFlexibility.Analysis.JointTransportPowerBounds
import ContinuousFlexibility.Analysis.N01TransportCharacteristicInterpolation
import ContinuousFlexibility.Analysis.JointMixedRadialScalar

/-!
# The same actual cutoff velocity has fixed-loss mixed parameter bounds

The angular boundary estimates, original characteristic estimates and
cutoff bounds all come from the actual N01 construction on its buffered
strips. One common low order is selected before the spatial budget.
The true transport equations then propagate the estimates radially.
Both the independent residual and the supplied N02 residual use the
same cutoff and the same flow inverses.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private def radialCutoffScalarTower
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {V : Set PolarPoint} (hU : IsOpen U) (hV : IsOpen V)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    SmoothDirections (U ×ˢ V) (fun x : E × PolarPoint => deriv χ x.2.1) := by
  let L : E × PolarPoint →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  have hd : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  exact (smoothDirectionsOfContDiffOn isOpen_univ hd.contDiffOn).compLinear L
    (hU.prod hV) (fun _ _ => mem_univ _)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

local instance n01TransportVelocityMixedGrowthStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01TransportVelocityMixedGrowthParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S × ℝ) := Prod.instSMul

/-- Fixed-loss bounds for the actual independent and frozen-residual
velocities. All geometric assumptions are the witnesses produced by
the buffered, uniform N01 neighborhood construction. -/
theorem N01Properties.returnCorrectionVelocity_flatMixedGrowth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hR : N02Properties D T S C R base ε)
    (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
        deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (y : PolarPoint),
      y.1 ∈ Ioo (l m) (h m) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      d ≤ (originalCoefficients D S C z).a y ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b y ^ 2 -
        (originalCoefficients D S C z).a y * (originalCoefficients D S C z).c y)
    (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hcutoff : ∀ k : ℕ, ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ K * radialE (D.cellIndex (j m)) ^ Q)
    (JV : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2))
    (JE : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
          (R.residual (liftSectorParameter S C x.1.1))))
    (nmax : ℕ) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading
    let W := fun m => radialE (D.cellIndex (j m))
    ∃ B : ℕ,
      FlatMixedDiagonalGrowth p W (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)) JV
        nmax B (B + 1) ∧
      FlatMixedDiagonalGrowth p W (fun _ => 1) JE nmax B (B + 1) := by
  let E := (StateDirections S × ℝ) × CircleSpace S
  let U : Set E := sectorNeighborhood S base ε ε ×ˢ univ
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let p := pairGrading (pairGrading (sectorGrading S) realGrading)
    (S.circle (3 / 4 : ℝ)).grading
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  let H : ℕ → ℝ := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
  have hp : Monotone p := correctionParameterGrading_monotone S
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hW0 (m : ℕ) : 0 ≤ W m := zero_le_one.trans (hW m)
  have hH (m : ℕ) : 0 ≤ H m := Real.rpow_nonneg
    ((material_circle_sample_weights_pos hT hN.1.1).2 m).le _
  have hU : IsOpen U := (sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ
  have hU₀ := sectorNeighborhood_isOpen S base ε ε
  have hV (m : ℕ) : IsOpen (V m) := isOpen_Ioo.prod isOpen_univ
  have hc (m : ℕ) : Convex ℝ (U ×ˢ V m) :=
    ((sectorNeighborhood_convex S base ε ε).prod (convex_univ : Convex ℝ (univ : Set (CircleSpace S)))).prod
      ((convex_Ioo (l m) (h m)).prod (convex_univ : Convex ℝ (univ : Set ℝ)))
  have hdisc (m : ℕ) (z : StateDirections S × ℝ)
      (hz : z ∈ sectorNeighborhood S base ε ε) (y : PolarPoint)
      (hy : y.1 ∈ Ioo (l m) (h m)) :
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b y ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a y *
          (originalCoefficients D S C (liftSectorParameter S C z)).c y := by
    have hd : 0 < lam * W m ^ (-P) / 2 :=
      half_pos (mul_pos hlam (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hW m)) _))
    exact (pow_pos hd 2).trans_le (hpositive (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl) m y hy).2
  let characteristicData := hN.exists_minusCharacteristicSpeed_strip_joint_growth
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hS hT j hcell l h hl hh hlam hP hpositive
  let JL₀ := characteristicData.choose
  let JL := fun m => (JL₀ m).fstParameter (F := CircleSpace S) hU₀ (hV m)
  let JA := fun m =>
    (hN.returnFlowInverseSlope_parameterSpatialTower hS hT m (l m) (h m) (hl m) (hh m)
      (hdisc m)).fstParameter (F := CircleSpace S) hU₀ (hV m)
  let J₀ := fun m =>
    (hN.returnCorrectionPulledResidual_parameterSpatialTower hS hT m (l m) (h m) (hl m) (hh m)
      (hdisc m) χ hχ hχrange hR).fstParameter (F := CircleSpace S) hU₀ (hV m)
  let J₁ := fun m =>
    hN.returnCorrectionPulledDisplacement_parameterSpatialTower hS hT m (l m) (h m) (hl m) (hh m)
      (hdisc m) χ hχ hχrange
  let fZ : Fin 2 → ℕ → E × PolarPoint → ℝ := Fin.cases
    (fun m x => returnCorrectionPulledDisplacementLinear S C χ
      (liftSectorParameter S C x.1.1) m x.2 (R.residual (liftSectorParameter S C x.1.1)))
    (Fin.cases (fun m x => returnCorrectionPulledDisplacementLinear S C χ
      (liftSectorParameter S C x.1.1) m x.2 x.1.2) Fin.elim0)
  let JZ : ∀ c m, SmoothDirections (U ×ˢ V m) (fZ c m) :=
    Fin.cases J₀ (Fin.cases J₁ (fun i => Fin.elim0 i))
  let JC := fun m => radialCutoffScalarTower hU (hV m) (hχ m)
  let characteristicBounds := hN.minusCharacteristicSpeed_correction_mixed_interpolation
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hS hT j hcell l h hl hh hlam hP hpositive JL nmax
  let BL : ℕ := characteristicBounds.choose
  have hBL := characteristicBounds.choose_spec
  let slopeBounds := hN.returnFlowInverseSlope_angular_diagonal_interpolation
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hS hT hflow l h hl hh JA nmax
  let BA : ℕ := slopeBounds.choose
  have hBA := slopeBounds.choose_spec
  let residualBounds := hN.returnCorrectionPulledResidual_angular_diagonal_interpolation
    (D := D) (T := T) (S := S) (C := C) (R := R)
    (base := base) (loss := loss) (ε := ε)
    hS hT hflow l h hl hh χ hχrange hR J₀ nmax
  let B₀ : ℕ := residualBounds.choose
  have hB₀ := residualBounds.choose_spec
  let displacementBounds := hN.returnCorrectionPulledDisplacement_angular_diagonal_interpolation
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hS hT hflow l h hl hh χ hχrange J₁ nmax
  let B₁ : ℕ := displacementBounds.choose
  have hB₁ := displacementBounds.choose_spec
  let B : ℕ := BL + BA + B₀ + B₁
  have hbL : BL ≤ B := by dsimp only [B]; omega
  have hbA : BA ≤ B := by dsimp only [B]; omega
  have hb0 : B₀ ≤ B := by dsimp only [B]; omega
  have hb1 : B₁ ≤ B := by dsimp only [B]; omega
  have hgL₀ : MixedDiagonalPowerGrowth p W (fun _ => 1) JL nmax BL := by
    intro A hA N n hn a b hab
    obtain ⟨K, Q, hK, hQ, hbnd⟩ := hBL A hA N n hn a b hab
    refine ⟨K, Q, hK, hQ, fun m x hx hxB w hw y hy => ?_⟩
    simpa only [mul_one] using hbnd m x hx w hxB hw y hy.1
  have hgL := hgL₀.mono_base hp hW0 (fun _ => zero_le_one) hbL
  have hgA₀ : AngularDiagonalPowerGrowth p (fun _ => 1) JA nmax BA := by
    intro A hA N n hn b hb
    obtain ⟨K, hK, hbnd⟩ := hBA A hA N n hn b hb
    refine ⟨K, hK, fun m x hx hxB w hw y hy => ?_⟩
    simpa only [mul_one] using hbnd m x hx w hxB hw y hy.1
  have hgA := hgA₀.mono_base hp (fun _ => zero_le_one) hbA
  have hg0 : AngularDiagonalPowerGrowth p (fun _ => 1) J₀ nmax B := by
    apply AngularDiagonalPowerGrowth.mono_base hp (fun _ => zero_le_one) (B := B₀) _ hb0
    intro A hA N n hn b hb
    obtain ⟨K, hK, hbnd⟩ := hB₀ A hA N n hn b hb
    refine ⟨K, hK, fun m x hx hxB w hw y hy => ?_⟩
    simpa only [mul_one] using hbnd m x hx w hxB hw y hy.1
  have hg1 : AngularDiagonalPowerGrowth p H J₁ nmax B := by
    apply AngularDiagonalPowerGrowth.mono_base hp hH (B := B₁) _ hb1
    intro A hA N n hn b hb
    obtain ⟨K, hK, hbnd⟩ := hB₁ A hA N n hn b hb
    exact ⟨K, hK, fun m x hx hxB w hw y hy => hbnd m x hx w hxB hw y hy.1⟩
  have hgZ (c : Fin 2) : AngularDiagonalPowerGrowth p (fun m => H m ^ c.val) (JZ c) nmax B := by
    fin_cases c
    · change AngularDiagonalPowerGrowth p (fun m => H m ^ 0) J₀ nmax B
      simpa only [pow_zero] using hg0
    · change AngularDiagonalPowerGrowth p (fun m => H m ^ 1) J₁ nmax B
      simpa only [pow_one] using hg1
  have hgC (n a b : ℕ) : ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧
      ∀ m x, x ∈ U → ∀ w, ∀ y ∈ V m,
        |jointMixedDiagonal (JC m) n a b x w y| ≤ K * W m ^ Q := by
    obtain ⟨K, Q, hK, hQ, hbnd⟩ := hcutoff (a + 1)
    exact ⟨K, Q, hK, hQ, fun m x hx w y hy =>
      jointMixedDiagonal_radial_deriv_abs_le (JC m) hU (hV m) (hc m)
        n a b x w hx hy hK (hW0 m) (hbnd m y.1)⟩
  have hAr (m : ℕ) (x : E) (hx : x ∈ U) (y : PolarPoint) (hy : y ∈ V m) :
      radialPartial (returnFlowInverseSlope S C (liftSectorParameter S C x.1) m) y =
        angularPartial (minusCharacteristicSpeed (originalCoefficients D S C
          (liftSectorParameter S C x.1))) y *
            returnFlowInverseSlope S C (liftSectorParameter S C x.1) m y -
        minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) y *
          angularPartial (returnFlowInverseSlope S C (liftSectorParameter S C x.1) m) y :=
    hN.returnFlowInverseSlope_transport_of_discriminant hS hT
      (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
      (hN.2.2.1.liftSectorParameter_sector x.1) m y
      ⟨(hl m).trans hy.1.1, hy.1.2.trans (hh m)⟩ (hdisc m x.1 hx.1 y hy.1)
  have hZr (c : Fin 2) (m : ℕ) (x : E) (hx : x ∈ U) (y : PolarPoint) (hy : y ∈ V m) :
      radialPartial (fun q => fZ c m (x, q)) y =
        -((minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) y +
            deriv (χ m) y.1 * returnFlowInverseSlope S C (liftSectorParameter S C x.1) m y *
              fZ 0 m (x, y)) * angularPartial (fun q => fZ c m (x, q)) y) := by
    have hrec (ρ : CircleSpace S) :=
      hN.returnCorrectionPulledDisplacementLinear_transport_actual hS hT
        (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
        (hN.2.2.1.liftSectorParameter_sector x.1) hR χ m (hχ m) (hχrange m)
        ρ y ⟨(hl m).trans hy.1.1, hy.1.2.trans (hh m)⟩
    fin_cases c
    · simpa only [fZ, Fin.cases_zero, neg_mul] using
        hrec (R.residual (liftSectorParameter S C x.1))
    · simpa only [fZ, Fin.cases_succ, Fin.cases_zero, neg_mul] using hrec x.2
  have hvel := jointTransport_velocity_mixedPowerGrowth p W H hW hH hU hV hc
    JL JC JA JZ nmax B hgL hgC hgA hgZ hAr hZr
  have hflat1 := (hvel 1).flat hW (fun m => pow_nonneg (hH m) (1 : Fin 2).val)
  have hflat0 := (hvel 0).flat hW (fun m => pow_nonneg (hH m) (0 : Fin 2).val)
  refine ⟨B, ?_, ?_⟩
  · have hsame := hflat1.congr JV hV (fun m x hx =>
      (returnCorrectionVelocityLinear_eq_transportProduct D S C χ
        (liftSectorParameter S C x.1.1) m x.2 x.1.2).symm)
    simpa only [pow_one] using hsame
  · have hsame := hflat0.congr JE hV (fun m x hx =>
      (returnCorrectionVelocityLinear_eq_transportProduct D S C χ
        (liftSectorParameter S C x.1.1) m x.2
          (R.residual (liftSectorParameter S C x.1.1))).symm)
    simpa only [pow_zero] using hsame

end ContinuousFlexibility.Statements
