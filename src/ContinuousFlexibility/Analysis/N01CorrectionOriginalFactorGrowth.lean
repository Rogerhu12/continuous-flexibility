import ContinuousFlexibility.Analysis.N01TransportCharacteristicInterpolation
import ContinuousFlexibility.Analysis.FlatMixedDiagonalRealization

/-!
# The actual original factors in the correction polynomial

The radial and mixed coefficients have the original unweighted N01
growth. On the same quantitative strip, the already constructed minus
characteristic speed gives the square-root factor by the exact identity
`sqrt(discriminant) = b - a * minusSpeed`. Thus all three actual factors
have fixed-loss mixed growth on the full correction parameter space.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01CorrectionOriginalFactorGrowthStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

private theorem sqrt_discriminant_from_minus_speed {a b c : ℝ} (ha : a ≠ 0) :
    b - a * (b / a - Real.sqrt (b ^ 2 - a * c) / a) = Real.sqrt (b ^ 2 - a * c) := by
  field_simp [ha]
  ring

theorem N01Properties.originalCorrectionFactors_flat_mixed_growth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (p : PolarPoint),
      p.1 ∈ Ioo (l m) (h m) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      d ≤ (originalCoefficients D S C z).a p ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (Ja : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2))
    (Jb : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        (originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2))
    (Jq : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        Real.sqrt ((originalCoefficients D S C (liftSectorParameter S C x.1.1)).b x.2 ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C x.1.1)).a x.2 *
            (originalCoefficients D S C (liftSectorParameter S C x.1.1)).c x.2))) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading
    let W := fun m => radialE (D.cellIndex (j m))
    HasFlatMixedTameGrowth p W (fun _ => 1) Ja ∧
      HasFlatMixedTameGrowth p W (fun _ => 1) Jb ∧
        HasFlatMixedTameGrowth p W (fun _ => 1) Jq := by
  let p := pairGrading (pairGrading (sectorGrading S) realGrading)
    (S.circle (3 / 4 : ℝ)).grading
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  have hp : Monotone p := correctionParameterGrading_monotone S
  have hIp : HasInterpolation p := correctionParameterGrading_hasInterpolation hS
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hW₀ (m : ℕ) : 0 ≤ W m := zero_le_one.trans (hW m)
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod
    (isOpen_univ : IsOpen (univ : Set (CircleSpace S)))
  have hV (m : ℕ) : IsOpen (Ioo (l m) (h m) ×ˢ (univ : Set ℝ)) :=
    isOpen_Ioo.prod isOpen_univ
  have hc (m : ℕ) : Convex ℝ
      ((sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) ×ˢ
        (Ioo (l m) (h m) ×ˢ (univ : Set ℝ))) :=
    ((sectorNeighborhood_convex S base ε ε).prod convex_univ).prod
      ((convex_Ioo (l m) (h m)).prod convex_univ)
  have ha₀ : UniformWeightedJointGrowth p (fun _ => 1) Ja base loss := by
    have hb := (hN.originalCoefficient_strip_joint_growth hS hT j hcell l h hl hh 0).fstParameter
      (S.circle (3 / 4 : ℝ)).grading (fun _ => zero_le_one)
      (sectorNeighborhood_isOpen S base ε ε) hV
    apply hb.congr Ja
    intro m x hx
    simp only [originalCoefficientEntry, if_pos rfl]
  have hb₀ : UniformWeightedJointGrowth p (fun _ => 1) Jb base loss := by
    have hb := (hN.originalCoefficient_strip_joint_growth hS hT j hcell l h hl hh 1).fstParameter
      (S.circle (3 / 4 : ℝ)).grading (fun _ => zero_le_one)
      (sectorNeighborhood_isOpen S base ε ε) hV
    apply hb.congr Jb
    intro m x hx
    norm_num [originalCoefficientEntry]
  have ha : UniformWeightedJointGrowth p W Ja base loss := ha₀.withWeight W
  have hb : UniformWeightedJointGrowth p W Jb base loss := hb₀.withWeight W
  let data := hN.exists_minusCharacteristicSpeed_strip_joint_growth hS hT
    j hcell l h hl hh hlam hP hpositive
  let Jv := fun m => (data.choose m).fstParameter
    (F := CircleSpace S) (sectorNeighborhood_isOpen S base ε ε) (hV m)
  let B := data.choose_spec.choose
  let L := data.choose_spec.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.choose_spec.1
  have hv : UniformWeightedJointGrowth p W Jv B L :=
    data.choose_spec.choose_spec.choose_spec.2.2.fstParameter
      (S.circle (3 / 4 : ℝ)).grading hW₀ (sectorNeighborhood_isOpen S base ε ε) hV
  let M := max loss L
  let Jprod := fun m => (Ja m).mul (Jv m)
  obtain ⟨B', L', hB', _, hprod⟩ :=
    (ha.mono hp hW₀ hB (le_max_left loss L)).mul hp hIp hW
      (hv.mono hp hW₀ le_rfl (le_max_right loss L)) Jprod
  let M' := max loss L'
  let subL : (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ
  let Jtemp := fun m => smoothDirectionsPostContinuousLinear
    (smoothDirectionsProd (Jb m) (Jprod m)) subL
  have htemp : UniformWeightedJointGrowth p W Jtemp B' M' :=
    (hb.mono hp hW₀ (hB.trans hB') (le_max_left _ _)).sub hp hW
      (hprod.mono hp hW₀ le_rfl (le_max_right _ _)) Jtemp
  have hq : UniformWeightedJointGrowth p W Jq B' M' := by
    apply htemp.congr Jq
    intro m x hx
    have hpoint : x.2 ∈ annularOpen D := hN.negativeComponent_subset_annularOpen m
      ⟨⟨(hl m).trans hx.2.1.1, hx.2.1.2.trans (hh m)⟩, hx.2.2⟩
    have hapos := hN.originalRadialCoefficient_pos
      (liftSectorParameter_mem_stateNeighborhood hx.1.1 le_rfl)
      (hN.2.2.1.liftSectorParameter_sector x.1.1) hpoint
    exact sqrt_discriminant_from_minus_speed hapos.ne'
  exact ⟨ha.hasFlatMixedTameGrowth hp hW hV hc,
    hb.hasFlatMixedTameGrowth hp hW hV hc,
    hq.hasFlatMixedTameGrowth hp hW hV hc⟩

end ContinuousFlexibility.Statements
