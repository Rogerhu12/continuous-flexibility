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

set_option diagnostics true in
private def correctionPolynomial_reflectedData
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {V : ℕ → Set PolarPoint}
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (W F : ℕ → ℝ) (hW : ∀ m, 1 ≤ W m) (hF : ∀ m, 0 ≤ F m)
    (hU : IsOpen U) (hV : ∀ m, IsOpen (V m))
    (hmap : ∀ m y, y ∈ V m → (y.1, -y.2) ∈ V m)
    {f : ℕ → E × PolarPoint → ℝ} {g : ℕ → E × PolarPoint → ℝ × ℝ}
    (J : ∀ m, SmoothDirections (U ×ˢ V m) (f m))
    (hJ : HasFlatMixedTameGrowth p W F J)
    (hvalue : ∀ m x, x ∈ U → ∀ y ∈ V m,
      g m (x, y) =
        ((f m (x, y) - f m (x, (y.1, -y.2))) / 2,
          (-f m (x, (y.1, -y.2)) - f m (x, y)) / 2)) :
    { K : ∀ m, SmoothDirections (U ×ˢ V m) (g m) //
      HasFlatMixedTameGrowth p W F
        (fun m => solveSmoothDirectionsPostcomp (K m) (ContinuousLinearMap.fst ℝ ℝ ℝ)) ∧
      HasFlatMixedTameGrowth p W F
        (fun m => solveSmoothDirectionsPostcomp (K m) (ContinuousLinearMap.snd ℝ ℝ ℝ)) } := by
  run_tac Lean.logInfo "N02N03 PolynomialGrowth: reflection-entry"
  let refl : (E × PolarPoint) →L[ℝ] E × PolarPoint := parameterAngularReflection E
  have hrefl (z : E × PolarPoint) : refl z = (z.1, (z.2.1, -z.2.2)) := rfl
  have hmaps (m : ℕ) : MapsTo refl (U ×ˢ V m) (U ×ˢ V m) := by
    intro z hz
    rw [hrefl]
    exact ⟨hz.1, hmap m z.2 hz.2⟩
  let Jr : ∀ m, SmoothDirections (U ×ˢ V m) (fun z => f m (refl z)) := fun m =>
    (J m).compLinear (E := E × PolarPoint) (F := E × PolarPoint) (G := ℝ)
      (U := U ×ˢ V m) (V := U ×ˢ V m) (f := f m)
      refl (hU.prod (hV m)) (hmaps m)
  have hJr : HasFlatMixedTameGrowth p W F Jr :=
    hJ.reflect_angle Jr hU hV hmap
      (fun m x _ y _ => congrArg (f m) (hrefl (x, y)))
  let K : ∀ m, SmoothDirections (U ×ˢ V m) (g m) := fun m =>
    (reflectedVelocityDirections (E := E × PolarPoint) (U := U ×ˢ V m)
      (f := f m) (g := fun z => f m (refl z)) (J m) (Jr m)).congrOn
        (F := E × PolarPoint) (G := ℝ × ℝ) (U := U ×ˢ V m) (g := g m) (by
          intro z hz
          change ((f m z - f m (refl z)) / 2, (-f m (refl z) - f m z) / 2) = g m z
          rw [hrefl]
          simpa only [Prod.mk.eta] using (hvalue m z.1 hz.1 z.2 hz.2).symm)
  let Kd := fun m => solveSmoothDirectionsPostcomp (K m) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let Kv := fun m => solveSmoothDirectionsPostcomp (K m) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hd : HasFlatMixedTameGrowth p W F Kd := by
    apply HasFlatMixedTameGrowth.linear_combination hp hW hF Kd hV
      (1 / 2) (-1 / 2) (hJ := hJ) (hK := hJr)
    intro m x hx y hy
    change (g m (x, y)).1 = (1 / 2 : ℝ) * f m (x, y) + (-1 / 2 : ℝ) * f m (refl (x, y))
    rw [hvalue m x hx y hy, hrefl]
    ring
  have hv : HasFlatMixedTameGrowth p W F Kv := by
    apply HasFlatMixedTameGrowth.linear_combination hp hW hF Kv hV
      (-1 / 2) (-1 / 2) (hJ := hJ) (hK := hJr)
    intro m x hx y hy
    change (g m (x, y)).2 = (-1 / 2 : ℝ) * f m (x, y) + (-1 / 2 : ℝ) * f m (refl (x, y))
    rw [hvalue m x hx y hy, hrefl]
    ring
  exact ⟨K, hd, hv⟩

private def correctionPolynomial_sqrtTower
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {a b c : E → ℝ}
    (Ja : SmoothDirections U a) (Jb : SmoothDirections U b) (Jc : SmoothDirections U c)
    (hpos : ∀ x ∈ U, 0 < b x ^ 2 - a x * c x) :
    SmoothDirections U (fun x => Real.sqrt (b x ^ 2 - a x * c x)) := by
  let subL : (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ
  let Jdisc : SmoothDirections U (fun x => b x ^ 2 - a x * c x) :=
    (smoothDirectionsPostContinuousLinear
      (smoothDirectionsProd (Jb.mul Jb) (Ja.mul Jc)) subL).congrOn
      (by intro x hx; simp only [pow_two])
  exact Jdisc.comp_contDiff isOpen_Ioi
    (contDiffOn_id.sqrt (fun q (hq : q ∈ Ioi (0 : ℝ)) => hq.ne')) hpos

private structure CorrectionPolynomialFactorData
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {V : ℕ → Set PolarPoint}
    (p : ℕ → Seminorm ℝ E) (W : ℕ → ℝ)
    (a b q : ℕ → E × PolarPoint → ℝ) where
  Ja : ∀ m, SmoothDirections (U ×ˢ V m) (a m)
  Jb : ∀ m, SmoothDirections (U ×ˢ V m) (b m)
  Jq : ∀ m, SmoothDirections (U ×ˢ V m) (q m)
  growth : HasFlatMixedTameGrowth p W (fun _ => 1) Ja ∧
    HasFlatMixedTameGrowth p W (fun _ => 1) Jb ∧
    HasFlatMixedTameGrowth p W (fun _ => 1) Jq

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

set_option diagnostics true in
include hN hS hT j hcell hl hh hstripDisc hlam hP hpositive in
private def correctionPolynomial_originalFactors :
    CorrectionPolynomialFactorData
      (U := sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)))
      (V := fun m => Ioo (l m) (h m) ×ˢ (univ : Set ℝ))
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (fun m => radialE (D.cellIndex (j m)))
      (fun _ (x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2)
      (fun _ (x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2)
      (fun _ (x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) =>
        Real.sqrt ((originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2 ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
            (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2)) := by
  run_tac Lean.logInfo "N02N03 PolynomialGrowth: factors-entry"
  have hV (m : ℕ) : IsOpen (Ioo (l m) (h m) ×ˢ (univ : Set ℝ)) :=
    isOpen_Ioo.prod isOpen_univ
  let Jentry := fun (i : Fin 3) (m : ℕ) =>
    (hN.originalCoefficient_stripTower
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      hS hT j hcell l h hl hh i m).fstParameter
      (E := StateDirections S × ℝ) (F := CircleSpace S) (P := PolarPoint) (G := ℝ)
      (U := sectorNeighborhood S base ε ε) (V := Ioo (l m) (h m) ×ˢ univ)
      (sectorNeighborhood_isOpen S base ε ε) (hV m)
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
  let Jq := fun m => correctionPolynomial_sqrtTower
    (E := ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint)
    (U := (sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
    (Ja m) (Jb m) (Jc m) (fun x hx => hstripDisc x.1.1 hx.1.1 m x.2 hx.2.1)
  have hfactor := hN.originalCorrectionFactors_flat_mixed_growth
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    (lam := lam) (P := P) hS hT j hcell l h hl hh hlam hP hpositive Ja Jb Jq
  run_tac Lean.logInfo "N02N03 PolynomialGrowth: factors-ready"
  exact ⟨Ja, Jb, Jq, hfactor⟩

include hlam hP hpositive

set_option diagnostics true in
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
  run_tac Lean.logInfo "N02N03 PolynomialGrowth: physical-entry"
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
  let E : Type := (StateDirections S × ℝ) × CircleSpace S
  let U : Set E := sectorNeighborhood S base ε ε ×ˢ univ
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let fρ : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2
  let fe : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
      (R.residual (liftSectorParameter S C x.1.1))
  let gρ : ℕ → E × PolarPoint → ℝ × ℝ := fun m x =>
    (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2,
      returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2)
  let ge : ℕ → E × PolarPoint → ℝ × ℝ := fun m x =>
    (returnCorrectionDriftLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
        (R.residual (liftSectorParameter S C x.1.1)),
      returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
        (R.residual (liftSectorParameter S C x.1.1)))
  let independent := correctionPolynomial_reflectedData
    (E := E) (U := U) (V := V) (f := fρ) (g := gρ)
    p hp W F hW hF hU hV (fun _ y hy => ⟨hy.1, mem_univ _⟩) Jρ hJρ
    (by
      intro m x hx y hy
      simp only [gρ, fρ, returnCorrectionDriftLinear_apply, returnCorrectionSpeedLinear_apply])
  let actual := correctionPolynomial_reflectedData
    (E := E) (U := U) (V := V) (f := fe) (g := ge)
    p hp W (fun _ => 1) hW (fun _ => zero_le_one) hU hV
    (fun _ y hy => ⟨hy.1, mem_univ _⟩) Je hJe
    (by
      intro m x hx y hy
      simp only [ge, fe, returnCorrectionDriftLinear_apply, returnCorrectionSpeedLinear_apply])
  let JD := independent.val
  let JE := actual.val
  let Jrd := fun m => solveSmoothDirectionsPostcomp (JD m) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let Jrv := fun m => solveSmoothDirectionsPostcomp (JD m) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let Jed := fun m => solveSmoothDirectionsPostcomp (JE m) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let Jev := fun m => solveSmoothDirectionsPostcomp (JE m) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hrd : HasFlatMixedTameGrowth p W F Jrd := independent.property.1
  have hrv : HasFlatMixedTameGrowth p W F Jrv := independent.property.2
  have hed : HasFlatMixedTameGrowth p W (fun _ => 1) Jed := actual.property.1
  have hev : HasFlatMixedTameGrowth p W (fun _ => 1) Jev := actual.property.2
  run_tac Lean.logInfo "N02N03 PolynomialGrowth: reflections-ready"
  let factors := correctionPolynomial_originalFactors
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    (hN := hN) (hS := hS) (hT := hT) (j := j) (hcell := hcell)
    (l := l) (h := h) (hl := hl) (hh := hh) (hstripDisc := hstripDisc)
    (lam := lam) (P := P) (hlam := hlam) (hP := hP) (hpositive := hpositive)
  let Ja := factors.Ja
  let Jb := factors.Jb
  let Jq := factors.Jq
  have hfactor : HasFlatMixedTameGrowth p W (fun _ => 1) Ja ∧
      HasFlatMixedTameGrowth p W (fun _ => 1) Jb ∧
      HasFlatMixedTameGrowth p W (fun _ => 1) Jq := factors.growth
  run_tac Lean.logInfo "N02N03 PolynomialGrowth: assembly"
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
