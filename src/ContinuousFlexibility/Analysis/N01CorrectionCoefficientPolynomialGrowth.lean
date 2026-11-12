import ContinuousFlexibility.Analysis.N01CorrectionOriginalFactorGrowth
import ContinuousFlexibility.Analysis.N01CorrectionCoefficientTameTransfer
import ContinuousFlexibility.Analysis.FlatMixedPolynomialCoefficients

/-!
# Actual coefficient growth from the same-cutoff velocity estimates

The original coefficients and square-root factor have proved N01
growth. The two genuine velocity families provide the remaining input.
Reflection gives the actual drift and speed, the division-free identity
gives the original coefficient error, and uniqueness applies all bounds
to its previously selected joint towers.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01CorrectionCoefficientPolynomialGrowthStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)
  (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
  (hstripDisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m (p : PolarPoint),
    p.1 ∈ Ioo (l m) (h m) →
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p)
  {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
  (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (p : PolarPoint),
    p.1 ∈ Ioo (l m) (h m) →
    let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
    d ≤ (originalCoefficients D S C z).a p ∧
    d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

include hlam hP hpositive

theorem N01Properties.returnCorrectionCoefficient_joint_growth_of_velocity
    (Jρ : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2))
    (Je : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
          (R.residual (liftSectorParameter S C x.1.1))))
    (hJρ : HasFlatMixedTameGrowth
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (fun m => radialE (D.cellIndex (j m)))
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)) Jρ)
    (hJe : HasFlatMixedTameGrowth
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (fun m => radialE (D.cellIndex (j m))) (fun _ => 1) Je) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading
    let W := fun m => radialE (D.cellIndex (j m))
    let F := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
    HasFlatMixedTameGrowth p W F
      (fun m => solveSmoothDirectionsPostcomp
        (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
          m (j m) (hcell m) (l m) (h m) (hl m) (hh m)
          (fun z hz q hq => hstripDisc z hz m q hq)) (ContinuousLinearMap.fst ℝ ℝ ℝ)) ∧
    HasFlatMixedTameGrowth p W F
      (fun m => solveSmoothDirectionsPostcomp
        (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
          m (j m) (hcell m) (l m) (h m) (hl m) (hh m)
          (fun z hz q hq => hstripDisc z hz m q hq)) (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  let p := pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  let F : ℕ → ℝ := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
  have hp : Monotone p := correctionParameterGrading_monotone S
  have hIp : HasInterpolation p := correctionParameterGrading_hasInterpolation hS
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hF (m : ℕ) : 0 ≤ F m :=
    (Real.rpow_pos_of_pos ((material_circle_sample_weights_pos hT hN.1.1).2 m) _).le
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod
    (isOpen_univ : IsOpen (univ : Set (CircleSpace S)))
  have hV (m : ℕ) : IsOpen (Ioo (l m) (h m) ×ˢ (univ : Set ℝ)) :=
    isOpen_Ioo.prod isOpen_univ
  have hc (m : ℕ) : Convex ℝ
      ((sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) ×ˢ
        (Ioo (l m) (h m) ×ˢ (univ : Set ℝ))) :=
    ((sectorNeighborhood_convex S base ε ε).prod convex_univ).prod
      ((convex_Ioo (l m) (h m)).prod convex_univ)
  let refl := parameterAngularReflection ((StateDirections S × ℝ) × CircleSpace S)
  have hrefl (m : ℕ) : MapsTo refl
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ)) :=
    fun x hx => ⟨hx.1, hx.2.1, mem_univ _⟩
  let Jρr := fun m => (Jρ m).compLinear refl (hU.prod (hV m)) (hrefl m)
  let Jer := fun m => (Je m).compLinear refl (hU.prod (hV m)) (hrefl m)
  have hJρr : HasFlatMixedTameGrowth p W F Jρr :=
    hJρ.reflect_angle Jρr hU hV (fun _ y hy => ⟨hy.1, mem_univ _⟩)
      (fun _ _ _ _ _ => rfl)
  have hJer : HasFlatMixedTameGrowth p W (fun _ => 1) Jer :=
    hJe.reflect_angle Jer hU hV (fun _ y hy => ⟨hy.1, mem_univ _⟩)
      (fun _ _ _ _ _ => rfl)
  let JD := fun m => (reflectedVelocityDirections (Jρ m) (Jρr m)).congrOn
    (g := fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
      (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2,
        returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2))
    (by intro x hx; simp only [returnCorrectionDriftLinear_apply, returnCorrectionSpeedLinear_apply])
  let JE := fun m => (reflectedVelocityDirections (Je m) (Jer m)).congrOn
    (g := fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
      (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
          (R.residual (liftSectorParameter S C x.1.1)),
        returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
          (R.residual (liftSectorParameter S C x.1.1))))
    (by intro x hx; simp only [returnCorrectionDriftLinear_apply, returnCorrectionSpeedLinear_apply])
  let Jrd := fun m => solveSmoothDirectionsPostcomp (JD m) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let Jrv := fun m => solveSmoothDirectionsPostcomp (JD m) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let Jed := fun m => solveSmoothDirectionsPostcomp (JE m) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let Jev := fun m => solveSmoothDirectionsPostcomp (JE m) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hrd : HasFlatMixedTameGrowth p W F Jrd := by
    apply HasFlatMixedTameGrowth.linear_combination hp hW hF Jrd hV
      (1 / 2) (-1 / 2) (hJ := hJρ) (hK := hJρr)
    intro m x hx y hy
    rw [returnCorrectionDriftLinear_apply]
    ring
  have hrv : HasFlatMixedTameGrowth p W F Jrv := by
    apply HasFlatMixedTameGrowth.linear_combination hp hW hF Jrv hV
      (-1 / 2) (-1 / 2) (hJ := hJρ) (hK := hJρr)
    intro m x hx y hy
    rw [returnCorrectionSpeedLinear_apply]
    ring
  have hed : HasFlatMixedTameGrowth p W (fun _ => 1) Jed := by
    apply HasFlatMixedTameGrowth.linear_combination hp hW (fun _ => zero_le_one) Jed hV
      (1 / 2) (-1 / 2) (hJ := hJe) (hK := hJer)
    intro m x hx y hy
    rw [returnCorrectionDriftLinear_apply]
    ring
  have hev : HasFlatMixedTameGrowth p W (fun _ => 1) Jev := by
    apply HasFlatMixedTameGrowth.linear_combination hp hW (fun _ => zero_le_one) Jev hV
      (-1 / 2) (-1 / 2) (hJ := hJe) (hK := hJer)
    intro m x hx y hy
    rw [returnCorrectionSpeedLinear_apply]
    ring
  let Jentry := fun i m =>
    (hN.originalCoefficient_stripTower hS hT j hcell l h hl hh i m).fstParameter
      (F := CircleSpace S) (sectorNeighborhood_isOpen S base ε ε) (hV m)
  let Ja := fun m => (Jentry 0 m).congrOn
    (g := fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
      (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2)
    (by intro x hx; simp only [originalCoefficientEntry, eq_self_iff_true, ite_true])
  let Jb := fun m => (Jentry 1 m).congrOn
    (g := fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
      (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2)
    (by intro x hx; norm_num [originalCoefficientEntry])
  let Jc := fun m => (Jentry 2 m).congrOn
    (g := fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
      (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2)
    (by intro x hx; norm_num [originalCoefficientEntry])
  let subL : (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ
  let Jdisc := fun m => (smoothDirectionsPostContinuousLinear
    (smoothDirectionsProd ((Jb m).mul (Jb m)) ((Ja m).mul (Jc m))) subL).congrOn
    (g := fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
      (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2 ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
          (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2)
    (by intro x hx; simp only [pow_two])
  let Jq := fun m => (Jdisc m).comp_contDiff isOpen_Ioi
    (contDiffOn_id.sqrt (fun q (hq : q ∈ Ioi (0 : ℝ)) => hq.ne'))
    (fun x hx => hstripDisc x.1.1 hx.1.1 m x.2 hx.2.1)
  have hfactor := hN.originalCorrectionFactors_flat_mixed_growth hS hT j hcell l h hl hh
    hlam hP hpositive Ja Jb Jq
  let Jout := fun m => hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
    m (j m) (hcell m) (l m) (h m) (hl m) (hh m)
    (fun z hz q hq => hstripDisc z hz m q hq)
  let JB := fun m => solveSmoothDirectionsPostcomp (Jout m) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let JC := fun m => solveSmoothDirectionsPostcomp (Jout m) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hpoly (m : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
      (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ) (y : PolarPoint)
      (hy : y ∈ Ioo (l m) (h m) ×ˢ (univ : Set ℝ)) := by
    have hy' : y.1 ∈ Ioo (C.left m) (C.right m) :=
      ⟨(hl m).trans hy.1.1, hy.1.2.trans (hh m)⟩
    have hpoint := hN.negativeComponent_subset_annularOpen m ⟨hy', hy.2⟩
    have hapos := hN.originalRadialCoefficient_pos
      (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
      (hN.2.2.1.liftSectorParameter_sector x.1) hpoint
    have hlocal := returnCorrectionLocalCoefficientError_cancel_denominators D S C R χ
      (liftSectorParameter S C x.1) m y x.2 hapos.ne'
    have heq := congrArg (fun A : CircleSpace S →ₗ[ℝ] (ℝ × ℝ) => A x.2)
      (returnCorrectionCoefficientError_eq_local hN.2.2.2.1.2.2.1 R χ
        (liftSectorParameter S C x.1) m y hy')
    exact heq.trans hlocal
  exact flatMixed_polynomial_coefficient_growth p hp hIp W F hW hF hU hV hc
    Ja Jb Jq Jed Jev Jrd Jrv JB JC
    (fun m x hx y hy => congrArg Prod.fst (hpoly m x hx y hy))
    (fun m x hx y hy => congrArg Prod.snd (hpoly m x hx y hy))
    hfactor.1 hfactor.2.1 hfactor.2.2 hed hev hrd hrv

end ContinuousFlexibility.Statements
