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


private theorem transportVelocity_finTwo_transport
    {I E : Type*} (f₀ f₁ : I → E × PolarPoint → ℝ)
    (i : I) (x : E) (y : PolarPoint) (v : ℝ)
    (h₀ : radialPartial (fun q => f₀ i (x, q)) y =
      -v * angularPartial (fun q => f₀ i (x, q)) y)
    (h₁ : radialPartial (fun q => f₁ i (x, q)) y =
      -v * angularPartial (fun q => f₁ i (x, q)) y)
    (c : Fin 2) :
    let fZ : Fin 2 → I → E × PolarPoint → ℝ :=
      Fin.cases f₀ (Fin.cases f₁ Fin.elim0)
    radialPartial (fun q => fZ c i (x, q)) y =
      -(v * angularPartial (fun q => fZ c i (x, q)) y) := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun j : Fin 0 => Fin.elim0 j)) c
  · simpa only [Fin.cases_zero, neg_mul] using h₀
  · simpa only [Fin.cases_succ, Fin.cases_zero, neg_mul] using h₁


private theorem transportVelocity_flat_from_certificates
    {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {l h : I → ℝ}
    (p : ℕ → Seminorm ℝ E) (W H : I → ℝ) (χ : I → ℝ → ℝ)
    (hp : Monotone p) (hW : ∀ i, 1 ≤ W i) (hH : ∀ i, 0 ≤ H i)
    (hU : IsOpen U)
    (hc : ∀ i, Convex ℝ (U ×ˢ (Ioo (l i) (h i) ×ˢ (univ : Set ℝ))))
    {fL fA fV fE : I → E × PolarPoint → ℝ}
    {fZ : Fin 2 → I → E × PolarPoint → ℝ}
    (JL : ∀ i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fL i))
    (JC : ∀ i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ))
      (fun z : E × PolarPoint => deriv (χ i) z.2.1))
    (JA : ∀ i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fA i))
    (JZ : ∀ c i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fZ c i))
    (JV : ∀ i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fV i))
    (JE : ∀ i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fE i))
    (nmax : ℕ)
    (characteristicBounds : ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A →
      ∀ N n : ℕ, n ≤ nmax → ∀ a b : ℕ, a + b ≤ N →
      ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧ ∀ i x, x ∈ U → ∀ w,
        p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
        |jointMixedDiagonal (JL i) n a b x w y| ≤ K * W i ^ Q *
          (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            (((a + b : ℕ) : ℝ) / ((N : ℝ) + 1)))
    (slopeBounds : ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A →
      ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i x, x ∈ U → ∀ w,
        p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
        |jointMixedDiagonal (JA i) n 0 b x w y| ≤ K *
          (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            ((b : ℝ) / ((N : ℝ) + 1)))
    (residualBounds : ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A →
      ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i x, x ∈ U → ∀ w,
        p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
        |jointMixedDiagonal (JZ 0 i) n 0 b x w y| ≤ K *
          (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            ((b : ℝ) / ((N : ℝ) + 1)))
    (displacementBounds : ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A →
      ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i x, x ∈ U → ∀ w,
        p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
        |jointMixedDiagonal (JZ 1 i) n 0 b x w y| ≤ K * H i *
          (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            ((b : ℝ) / ((N : ℝ) + 1)))
    (hcutoff : ∀ k : ℕ, ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧ ∀ i r,
      |iteratedDeriv k (χ i) r| ≤ K * W i ^ Q)
    (hAr : ∀ i x, x ∈ U → ∀ y ∈ Ioo (l i) (h i) ×ˢ (univ : Set ℝ),
      radialPartial (fun q => fA i (x, q)) y =
        angularPartial (fun q => fL i (x, q)) y * fA i (x, y) -
          fL i (x, y) * angularPartial (fun q => fA i (x, q)) y)
    (hZr : ∀ c i x, x ∈ U → ∀ y ∈ Ioo (l i) (h i) ×ˢ (univ : Set ℝ),
      radialPartial (fun q => fZ c i (x, q)) y =
        -((fL i (x, y) + deriv (χ i) y.1 * fA i (x, y) * fZ 0 i (x, y)) *
          angularPartial (fun q => fZ c i (x, q)) y))
    (hVeq : ∀ i z, z ∈ U ×ˢ (Ioo (l i) (h i) ×ˢ (univ : Set ℝ)) →
      deriv (χ i) z.2.1 * fA i z * fZ 1 i z = fV i z)
    (hEeq : ∀ i z, z ∈ U ×ˢ (Ioo (l i) (h i) ×ˢ (univ : Set ℝ)) →
      deriv (χ i) z.2.1 * fA i z * fZ 0 i z = fE i z) :
    ∃ B : ℕ, FlatMixedDiagonalGrowth p W H JV nmax B (B + 1) ∧
      FlatMixedDiagonalGrowth p W (fun _ => 1) JE nmax B (B + 1) := by
  let V : I → Set PolarPoint := fun i => Ioo (l i) (h i) ×ˢ univ
  have hV (i : I) : IsOpen (V i) := isOpen_Ioo.prod isOpen_univ
  have hW0 (i : I) : 0 ≤ W i := zero_le_one.trans (hW i)
  let J₀ := JZ 0
  let J₁ := JZ 1
  obtain ⟨BL, hBL⟩ := characteristicBounds
  obtain ⟨BA, hBA⟩ := slopeBounds
  obtain ⟨B₀, hB₀⟩ := residualBounds
  obtain ⟨B₁, hB₁⟩ := displacementBounds
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
    refine Fin.cases ?_ (Fin.cases ?_ (fun i : Fin 0 => Fin.elim0 i)) c
    · simpa only [J₀, Fin.val_zero, pow_zero] using hg0
    · simpa only [J₁, Fin.succ_zero_eq_one, Fin.val_one, pow_one] using hg1
  have hgC (n a b : ℕ) : ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧
      ∀ m x, x ∈ U → ∀ w, ∀ y ∈ V m,
        |jointMixedDiagonal (JC m) n a b x w y| ≤ K * W m ^ Q := by
    obtain ⟨K, Q, hK, hQ, hbnd⟩ := hcutoff (a + 1)
    exact ⟨K, Q, hK, hQ, fun m x hx w y hy =>
      jointMixedDiagonal_radial_deriv_abs_le (JC m) hU (hV m) (hc m)
        n a b x w hx hy hK (hW0 m) (hbnd m y.1)⟩
  have hvel := jointTransport_velocity_mixedPowerGrowth
    (I := I) (E := E) (U := U) (V := V)
    (fL := fL) (fC := fun i (z : E × PolarPoint) => deriv (χ i) z.2.1)
    (fA := fA) (fZ := fZ) p W H hW hH hU hV hc
    JL JC JA JZ nmax B hgL hgC hgA hgZ hAr hZr
  have hflat1 := (hvel 1).flat hW (fun i => pow_nonneg (hH i) (1 : Fin 2).val)
  have hflat0 := (hvel 0).flat hW (fun i => pow_nonneg (hH i) (0 : Fin 2).val)
  refine ⟨B, ?_, ?_⟩
  · have hsame := hflat1.congr JV hV hVeq
    simpa only [Fin.val_one, pow_one] using hsame
  · have hsame := hflat0.congr JE hV hEeq
    simpa only [Fin.val_zero, pow_zero] using hsame

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

local instance n01TransportVelocityMixedGrowthStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

local instance n01TransportVelocityMixedGrowthDirectionsSMul (S : PhysicalSpacesData) :
    SMul ℝ (StateDirections S) :=
  Submodule.smul (R := ℝ) (M := AnnularState S) (S := ℝ) (StateDirections S)

local instance n01TransportVelocityMixedGrowthSectorSMul (S : PhysicalSpacesData) :
    SMul ℝ (StateDirections S × ℝ) := Prod.instSMul

local instance n01TransportVelocityMixedGrowthCorrectionSMul (S : PhysicalSpacesData) :
    SMul ℝ ((StateDirections S × ℝ) × CircleSpace S) := Prod.instSMul

local instance n01TransportVelocityMixedGrowthParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S × ℝ) := Prod.instSMul

private def transportVelocity_parameterGrading (S : PhysicalSpacesData) :
    ℕ → Seminorm ℝ ((StateDirections S × ℝ) × CircleSpace S) :=
  pairGrading (pairGrading (sectorGrading S) realGrading)
    (S.circle (3 / 4 : ℝ)).grading

private theorem transportVelocity_parameterGrading_monotone (S : PhysicalSpacesData) :
    Monotone (transportVelocity_parameterGrading S) :=
  correctionParameterGrading_monotone S

private theorem transportVelocity_parameterDomain_isOpen
    (S : PhysicalSpacesData) (base : ℕ) (ε : ℝ) :
    IsOpen (sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) :=
  (sectorNeighborhood_isOpen S base ε ε).prod
    (isOpen_univ : IsOpen (univ : Set (CircleSpace S)))

private theorem transportVelocity_domain_convex
    (S : PhysicalSpacesData) (base : ℕ) (ε l h : ℝ) :
    Convex ℝ ((sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) ×ˢ
      (Ioo l h ×ˢ (univ : Set ℝ))) :=
  ((sectorNeighborhood_convex S base ε ε).prod
    (convex_univ : Convex ℝ (univ : Set (CircleSpace S)))).prod
      ((convex_Ioo l h).prod (convex_univ : Convex ℝ (univ : Set ℝ)))

private def transportVelocity_characteristicDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    (hapos : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ (m : ℕ) (y : PolarPoint),
      y.1 ∈ Ioo (l m) (h m) →
        0 < (originalCoefficients D S C (liftSectorParameter S C z)).a y)
    (hdisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ (m : ℕ) (y : PolarPoint),
      y.1 ∈ Ioo (l m) (h m) →
        0 < (originalCoefficients D S C (liftSectorParameter S C z)).b y ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C z)).a y *
            (originalCoefficients D S C (liftSectorParameter S C z)).c y)
    (m : ℕ) :
    SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) ×ˢ
        (Ioo (l m) (h m) ×ˢ (univ : Set ℝ)))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        minusCharacteristicSpeed
          (originalCoefficients D S C (liftSectorParameter S C x.1.1)) x.2) :=
  (N01Properties.minusCharacteristicSpeed_stripTower
    (D := D) (T := T) (S := S) (C := C)
    (base := base) (loss := loss) (ε := ε)
    hN hS hT j hcell l h hl hh hapos hdisc m).fstParameter
      (F := CircleSpace S) (sectorNeighborhood_isOpen S base ε ε)
      ((isOpen_Ioo : IsOpen (Ioo (l m) (h m))).prod
        (isOpen_univ : IsOpen (univ : Set ℝ)))

private def transportVelocity_slopeDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m)
    (hdisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ y : PolarPoint,
      y.1 ∈ Ioo l h →
        0 < (originalCoefficients D S C (liftSectorParameter S C z)).b y ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C z)).a y *
            (originalCoefficients D S C (liftSectorParameter S C z)).c y) :
    SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) ×ˢ
        (Ioo l h ×ˢ (univ : Set ℝ)))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnFlowInverseSlope S C (liftSectorParameter S C x.1.1) m x.2) :=
  (N01Properties.returnFlowInverseSlope_parameterSpatialTower
    (D := D) (T := T) (S := S) (C := C)
    (base := base) (loss := loss) (ε := ε)
    hN hS hT m l h hl hh hdisc).fstParameter
      (F := CircleSpace S) (sectorNeighborhood_isOpen S base ε ε)
      ((isOpen_Ioo : IsOpen (Ioo l h)).prod
        (isOpen_univ : IsOpen (univ : Set ℝ)))

private def transportVelocity_residualDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m)
    (hdisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ y : PolarPoint,
      y.1 ∈ Ioo l h →
        0 < (originalCoefficients D S C (liftSectorParameter S C z)).b y ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C z)).a y *
            (originalCoefficients D S C (liftSectorParameter S C z)).c y)
    (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hR : N02Properties D T S C R base ε) :
    SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) ×ˢ
        (Ioo l h ×ˢ (univ : Set ℝ)))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionPulledDisplacementLinear S C χ
          (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1))) :=
  (N01Properties.returnCorrectionPulledResidual_parameterSpatialTower
    (D := D) (T := T) (S := S) (C := C) (R := R)
    (base := base) (loss := loss) (ε := ε)
    hN hS hT m l h hl hh hdisc χ hχ hχrange hR).fstParameter
      (F := CircleSpace S) (sectorNeighborhood_isOpen S base ε ε)
      ((isOpen_Ioo : IsOpen (Ioo l h)).prod
        (isOpen_univ : IsOpen (univ : Set ℝ)))

private def transportVelocity_displacementDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m)
    (hdisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ y : PolarPoint,
      y.1 ∈ Ioo l h →
        0 < (originalCoefficients D S C (liftSectorParameter S C z)).b y ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C z)).a y *
            (originalCoefficients D S C (liftSectorParameter S C z)).c y)
    (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1) :
    SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) ×ˢ
        (Ioo l h ×ˢ (univ : Set ℝ)))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionPulledDisplacementLinear S C χ
          (liftSectorParameter S C x.1.1) m x.2 x.1.2) :=
  N01Properties.returnCorrectionPulledDisplacement_parameterSpatialTower
    (D := D) (T := T) (S := S) (C := C)
    (base := base) (loss := loss) (ε := ε)
    hN hS hT m l h hl hh hdisc χ hχ hχrange

private def transportVelocity_cutoffDirections
    (S : PhysicalSpacesData) (base : ℕ) (ε l h : ℝ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) ×ˢ
        (Ioo l h ×ˢ (univ : Set ℝ)))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        deriv χ x.2.1) :=
  radialCutoffScalarTower
    (E := (StateDirections S × ℝ) × CircleSpace S)
    (U := sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)))
    (V := Ioo l h ×ˢ (univ : Set ℝ)) (χ := χ)
    (transportVelocity_parameterDomain_isOpen S base ε)
    ((isOpen_Ioo : IsOpen (Ioo l h)).prod
      (isOpen_univ : IsOpen (univ : Set ℝ))) hχ

private theorem transportVelocity_parameterFlat_from_certificates
    (S : PhysicalSpacesData)
    {U : Set ((StateDirections S × ℝ) × CircleSpace S)} {l h : ℕ → ℝ}
    (p : ℕ → Seminorm ℝ ((StateDirections S × ℝ) × CircleSpace S)) (W H : ℕ → ℝ) (χ : ℕ → ℝ → ℝ)
    (hp : Monotone p) (hW : ∀ i, 1 ≤ W i) (hH : ∀ i, 0 ≤ H i)
    (hU : IsOpen U)
    (hc : ∀ i, Convex ℝ (U ×ˢ (Ioo (l i) (h i) ×ˢ (univ : Set ℝ))))
    {fL fA fV fE : ℕ → ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint → ℝ}
    {fZ : Fin 2 → ℕ → ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint → ℝ}
    (JL : ∀ i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fL i))
    (JC : ∀ i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ))
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint => deriv (χ i) z.2.1))
    (JA : ∀ i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fA i))
    (JZ : ∀ c i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fZ c i))
    (JV : ∀ i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fV i))
    (JE : ∀ i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fE i))
    (nmax : ℕ)
    (characteristicBounds : ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A →
      ∀ N n : ℕ, n ≤ nmax → ∀ a b : ℕ, a + b ≤ N →
      ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧ ∀ i x, x ∈ U → ∀ w,
        p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
        |jointMixedDiagonal (JL i) n a b x w y| ≤ K * W i ^ Q *
          (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            (((a + b : ℕ) : ℝ) / ((N : ℝ) + 1)))
    (slopeBounds : ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A →
      ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i x, x ∈ U → ∀ w,
        p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
        |jointMixedDiagonal (JA i) n 0 b x w y| ≤ K *
          (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            ((b : ℝ) / ((N : ℝ) + 1)))
    (residualBounds : ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A →
      ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i x, x ∈ U → ∀ w,
        p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
        |jointMixedDiagonal (JZ 0 i) n 0 b x w y| ≤ K *
          (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            ((b : ℝ) / ((N : ℝ) + 1)))
    (displacementBounds : ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A →
      ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i x, x ∈ U → ∀ w,
        p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
        |jointMixedDiagonal (JZ 1 i) n 0 b x w y| ≤ K * H i *
          (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            ((b : ℝ) / ((N : ℝ) + 1)))
    (hcutoff : ∀ k : ℕ, ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧ ∀ i r,
      |iteratedDeriv k (χ i) r| ≤ K * W i ^ Q)
    (hAr : ∀ i x, x ∈ U → ∀ y ∈ Ioo (l i) (h i) ×ˢ (univ : Set ℝ),
      radialPartial (fun q => fA i (x, q)) y =
        angularPartial (fun q => fL i (x, q)) y * fA i (x, y) -
          fL i (x, y) * angularPartial (fun q => fA i (x, q)) y)
    (hZr : ∀ c i x, x ∈ U → ∀ y ∈ Ioo (l i) (h i) ×ˢ (univ : Set ℝ),
      radialPartial (fun q => fZ c i (x, q)) y =
        -((fL i (x, y) + deriv (χ i) y.1 * fA i (x, y) * fZ 0 i (x, y)) *
          angularPartial (fun q => fZ c i (x, q)) y))
    (hVeq : ∀ i z, z ∈ U ×ˢ (Ioo (l i) (h i) ×ˢ (univ : Set ℝ)) →
      deriv (χ i) z.2.1 * fA i z * fZ 1 i z = fV i z)
    (hEeq : ∀ i z, z ∈ U ×ˢ (Ioo (l i) (h i) ×ˢ (univ : Set ℝ)) →
      deriv (χ i) z.2.1 * fA i z * fZ 0 i z = fE i z) :
    ∃ B : ℕ, FlatMixedDiagonalGrowth p W H JV nmax B (B + 1) ∧
      FlatMixedDiagonalGrowth p W (fun _ => 1) JE nmax B (B + 1) := by
  exact transportVelocity_flat_from_certificates
    (I := ℕ) (E := (StateDirections S × ℝ) × CircleSpace S)
    (U := U) (l := l) (h := h)
    (fL := fL) (fA := fA) (fZ := fZ) (fV := fV) (fE := fE)
    p W H χ hp hW hH hU hc JL JC JA JZ JV JE nmax
    characteristicBounds slopeBounds residualBounds displacementBounds
    hcutoff hAr hZr hVeq hEeq

private theorem transportVelocity_actualGrowth
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
    let p := transportVelocity_parameterGrading S
    let W := fun m => radialE (D.cellIndex (j m))
    ∃ B : ℕ,
      FlatMixedDiagonalGrowth p W (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)) JV
        nmax B (B + 1) ∧
      FlatMixedDiagonalGrowth p W (fun _ => 1) JE nmax B (B + 1) := by
  let E : Type := (StateDirections S × ℝ) × CircleSpace S
  let U : Set E := sectorNeighborhood S base ε ε ×ˢ univ
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let p := transportVelocity_parameterGrading S
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  let H : ℕ → ℝ := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
  have hp := transportVelocity_parameterGrading_monotone S
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hW0 (m : ℕ) : 0 ≤ W m := zero_le_one.trans (hW m)
  have hH (m : ℕ) : 0 ≤ H m := Real.rpow_nonneg
    ((material_circle_sample_weights_pos hT hN.1.1).2 m).le _
  have hU := transportVelocity_parameterDomain_isOpen S base ε
  have hc := fun m : ℕ => transportVelocity_domain_convex S base ε (l m) (h m)
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
  have hapos (z : StateDirections S × ℝ)
      (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) (y : PolarPoint)
      (hy : y.1 ∈ Ioo (l m) (h m)) :
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).a y := by
    have hd : 0 < lam * W m ^ (-P) / 2 :=
      half_pos (mul_pos hlam (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hW m)) _))
    exact hd.trans_le (hpositive (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl) m y hy).1
  let fL : ℕ → E × PolarPoint → ℝ := fun _ x =>
    minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1.1)) x.2
  let fA : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnFlowInverseSlope S C (liftSectorParameter S C x.1.1) m x.2
  let f₀ : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnCorrectionPulledDisplacementLinear S C χ
      (liftSectorParameter S C x.1.1) m x.2 (R.residual (liftSectorParameter S C x.1.1))
  let f₁ : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnCorrectionPulledDisplacementLinear S C χ
      (liftSectorParameter S C x.1.1) m x.2 x.1.2
  let JL := transportVelocity_characteristicDirections
    (D := D) (T := T) (S := S) (C := C)
    (base := base) (loss := loss) (ε := ε)
    hN hS hT j hcell l h hl hh hapos (fun z hz i y hy => hdisc i z hz y hy)
  let JA := fun m : ℕ => transportVelocity_slopeDirections
    (D := D) (T := T) (S := S) (C := C)
    (base := base) (loss := loss) (ε := ε)
    hN hS hT m (l m) (h m) (hl m) (hh m) (hdisc m)
  let J₀ := fun m : ℕ => transportVelocity_residualDirections
    (D := D) (T := T) (S := S) (C := C) (R := R)
    (base := base) (loss := loss) (ε := ε)
    hN hS hT m (l m) (h m) (hl m) (hh m) (hdisc m) χ hχ hχrange hR
  let J₁ := fun m : ℕ => transportVelocity_displacementDirections
    (D := D) (T := T) (S := S) (C := C)
    (base := base) (loss := loss) (ε := ε)
    hN hS hT m (l m) (h m) (hl m) (hh m) (hdisc m) χ hχ hχrange
  let fZ : Fin 2 → ℕ → E × PolarPoint → ℝ :=
    Fin.cases f₀ (Fin.cases f₁ Fin.elim0)
  let JZ : ∀ c m, SmoothDirections (U ×ˢ V m) (fZ c m) :=
    Fin.cases J₀ (Fin.cases J₁ (fun i : Fin 0 => Fin.elim0 i))
  let JC := fun m : ℕ =>
    transportVelocity_cutoffDirections S base ε (l m) (h m) (χ m) (hχ m)
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
    exact transportVelocity_finTwo_transport (I := ℕ) (E := E) f₀ f₁ m x y
      (minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) y +
        deriv (χ m) y.1 * returnFlowInverseSlope S C (liftSectorParameter S C x.1) m y *
          fZ 0 m (x, y))
      (hrec (R.residual (liftSectorParameter S C x.1))) (hrec x.2) c
  exact transportVelocity_parameterFlat_from_certificates S
    (U := U) (l := l) (h := h)
    (fL := fL) (fA := fA) (fZ := fZ)
    (fV := fun m (x : E × PolarPoint) =>
      returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2)
    (fE := fun m (x : E × PolarPoint) =>
      returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
        (R.residual (liftSectorParameter S C x.1.1)))
    p W H χ hp hW hH hU hc JL JC JA JZ JV JE nmax
    (N01Properties.minusCharacteristicSpeed_correction_mixed_interpolation
      (D := D) (T := T) (S := S) (C := C)
      (base := base) (loss := loss) (ε := ε) (lam := lam) (P := P)
      hN hS hT j hcell l h hl hh hlam hP hpositive JL nmax)
    (N01Properties.returnFlowInverseSlope_angular_diagonal_interpolation
      (D := D) (T := T) (S := S) (C := C)
      (base := base) (loss := loss) (ε := ε)
      hN hS hT hflow l h hl hh JA nmax)
    (N01Properties.returnCorrectionPulledResidual_angular_diagonal_interpolation
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε)
      hN hS hT hflow l h hl hh χ hχrange hR J₀ nmax)
    (N01Properties.returnCorrectionPulledDisplacement_angular_diagonal_interpolation
      (D := D) (T := T) (S := S) (C := C)
      (base := base) (loss := loss) (ε := ε)
      hN hS hT hflow l h hl hh χ hχrange J₁ nmax)
    hcutoff hAr hZr
    (fun m x _ => by
      simpa only [fA, fZ, f₀, f₁, ← Fin.succ_zero_eq_one,
        Fin.cases_succ, Fin.cases_zero] using
        (returnCorrectionVelocityLinear_eq_transportProduct D S C χ
          (liftSectorParameter S C x.1.1) m x.2 x.1.2).symm)
    (fun m x _ => by
      simpa only [fA, fZ, f₀, f₁, Fin.cases_zero] using
        (returnCorrectionVelocityLinear_eq_transportProduct D S C χ
          (liftSectorParameter S C x.1.1) m x.2
            (R.residual (liftSectorParameter S C x.1.1))).symm)

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
  exact transportVelocity_actualGrowth
    (D := D) (T := T) (S := S) (C := C) (R := R)
    (base := base) (loss := loss) (ε := ε) (lam := lam) (P := P)
    hN hS hT hR hflow j hcell l h hl hh hlam hP hpositive
    χ hχ hχrange hcutoff JV JE nmax


end ContinuousFlexibility.Statements
