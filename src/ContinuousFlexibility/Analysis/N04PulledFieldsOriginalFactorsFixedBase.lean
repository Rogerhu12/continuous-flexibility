module

public import ContinuousFlexibility.Analysis.N01CorrectionOriginalFactorGrowth
public import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBaseMixedGrowth

/-!
# The actual original polynomial factors on one parameter neighborhood

The original coefficient and minus-characteristic towers already have
uniform joint growth with one fixed base. The exact identity
`sqrt(discriminant) = b - a * minusSpeed` gives the third factor. The
genuine original towers are retained, on the original sector parameter
space, before any parameter order or spatial loss is selected.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

private theorem n04PulledFields_originalFactors_from_jointGrowth
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    {W : ℕ → ℝ} (hW : ∀ m, 1 ≤ W m)
    {U : Set E} {V : ℕ → Set PolarPoint}
    (hV : ∀ m, IsOpen (V m)) (hc : ∀ m, Convex ℝ (U ×ˢ V m))
    {fa fb fv fq : ℕ → E × PolarPoint → ℝ}
    (Ja : ∀ m, SmoothDirections (U ×ˢ V m) (fa m))
    (Jb : ∀ m, SmoothDirections (U ×ˢ V m) (fb m))
    (Jv : ∀ m, SmoothDirections (U ×ˢ V m) (fv m))
    (Jq : ∀ m, SmoothDirections (U ×ˢ V m) (fq m))
    {base loss B L : ℕ} (hB : base ≤ B)
    (ha : UniformWeightedJointGrowth p W Ja base loss)
    (hb : UniformWeightedJointGrowth p W Jb base loss)
    (hv : UniformWeightedJointGrowth p W Jv B L)
    (heq : ∀ m x, x ∈ U ×ˢ V m → fb m x - fa m x * fv m x = fq m x) :
    N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Ja ∧
      N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Jb ∧
        N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Jq := by
  obtain ⟨B', L', _, _, hq⟩ :=
    scalar_sub_mul_jointGrowth hp hI hW Ja Jb Jv Jq hB ha hb hv heq
  exact ⟨ha.n04PulledFields_fixedBaseMixedGrowth hp hW hV hc,
    hb.n04PulledFields_fixedBaseMixedGrowth hp hW hV hc,
    hq.n04PulledFields_fixedBaseMixedGrowth hp hW hV hc⟩

local instance n04PulledFieldsOriginalFactorsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

/-- Genuine `a`, `b`, and square-root discriminant factors on the
original sector. The low base of each factor precedes all parameter
orders; the quantitative strip remains unchanged. -/
theorem N01Properties.n04PulledFields_originalCorrectionFactors_fixedBase
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
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        (originalCoefficients D S C (liftSectorParameter S C x.1)).a x.2))
    (Jb : ∀ m, SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        (originalCoefficients D S C (liftSectorParameter S C x.1)).b x.2))
    (Jq : ∀ m, SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        Real.sqrt ((originalCoefficients D S C (liftSectorParameter S C x.1)).b x.2 ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C x.1)).a x.2 *
            (originalCoefficients D S C (liftSectorParameter S C x.1)).c x.2))) :
    let p := pairGrading (sectorGrading S) realGrading
    let W := fun m => radialE (D.cellIndex (j m))
    N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Ja ∧
      N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Jb ∧
        N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Jq := by
  let E := StateDirections S × ℝ
  let p : ℕ → Seminorm ℝ E := pairGrading (sectorGrading S) realGrading
  let U : Set E := sectorNeighborhood S base ε ε
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  have hp : Monotone p := sectorPairGrading_monotone S
  have hI : HasInterpolation p := hasInterpolation_of_hasSmoothing hp
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat (D.cellIndex (j m))
  have hV (m : ℕ) : IsOpen (V m) := isOpen_Ioo.prod isOpen_univ
  have hc (m : ℕ) : Convex ℝ (U ×ˢ V m) :=
    (sectorNeighborhood_convex S base ε ε).prod ((convex_Ioo (l m) (h m)).prod convex_univ)
  let entry : Fin 3 → ℕ → E × PolarPoint → ℝ := fun i _ x =>
    originalCoefficientEntry D S C i (liftSectorParameter S C x.1) x.2
  let K : ∀ (i : Fin 3) (m : ℕ), SmoothDirections (U ×ˢ V m) (entry i m) :=
    fun i m => hN.originalCoefficient_stripTower hS hT j hcell l h hl hh i m
  have hK (i : Fin 3) : UniformWeightedJointGrowth p (fun _ => 1) (K i) base loss :=
    hN.originalCoefficient_strip_joint_growth hS hT j hcell l h hl hh i
  have ha : UniformWeightedJointGrowth p W Ja base loss :=
    ((hK 0).congr Ja (fun _ _ _ => by
      simp only [entry, originalCoefficientEntry, eq_self_iff_true, ite_true])).withWeight W
  have hb : UniformWeightedJointGrowth p W Jb base loss :=
    ((hK 1).congr Jb (fun _ _ _ => by
      have h10 : (1 : Fin 3) ≠ 0 := by decide
      simp only [entry, originalCoefficientEntry, h10, eq_self_iff_true, ite_false, ite_true])).withWeight W
  let fv : ℕ → E × PolarPoint → ℝ := fun _ x =>
    minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) x.2
  let data : ∃ J : ∀ m, SmoothDirections (U ×ˢ V m) (fv m),
      ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p W J B L :=
    hN.exists_minusCharacteristicSpeed_strip_joint_growth
      hS hT j hcell l h hl hh hlam hP hpositive
  let Jv : ∀ m, SmoothDirections (U ×ˢ V m) (fv m) := data.choose
  let B : ℕ := data.choose_spec.choose
  let L : ℕ := data.choose_spec.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.choose_spec.1
  have hv : UniformWeightedJointGrowth p W Jv B L := data.choose_spec.choose_spec.choose_spec.2.2
  apply n04PulledFields_originalFactors_from_jointGrowth hp hI hW hV hc Ja Jb Jv Jq hB ha hb hv
  intro m x hx
  have hpoint : x.2 ∈ annularOpen D := hN.negativeComponent_subset_annularOpen m
    ⟨⟨(hl m).trans hx.2.1.1, hx.2.1.2.trans (hh m)⟩, hx.2.2⟩
  have hapos : 0 < (originalCoefficients D S C (liftSectorParameter S C x.1)).a x.2 :=
    hN.originalRadialCoefficient_pos
      (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
      (hN.2.2.1.liftSectorParameter_sector x.1) hpoint
  have heq := sqrt_discriminant_from_minus_speed
    (a := (originalCoefficients D S C (liftSectorParameter S C x.1)).a x.2)
    (b := (originalCoefficients D S C (liftSectorParameter S C x.1)).b x.2)
    (c := (originalCoefficients D S C (liftSectorParameter S C x.1)).c x.2) hapos.ne'
  simp only [fv, minusCharacteristicSpeed]
  exact heq

end ContinuousFlexibility.Statements
