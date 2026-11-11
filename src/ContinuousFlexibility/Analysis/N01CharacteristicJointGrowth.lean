import ContinuousFlexibility.Analysis.N01OriginalCoefficientTameBounds
import ContinuousFlexibility.Analysis.N01NeighborhoodRestriction
import ContinuousFlexibility.Analysis.MixedJointTameBounds
import ContinuousFlexibility.Analysis.JointMixedTameBounds
import ContinuousFlexibility.Analysis.WeightedJointProducts
import ContinuousFlexibility.Analysis.WeightedJointPowers
import ContinuousFlexibility.Analysis.TameSmoothingCalculus
import ContinuousFlexibility.Analysis.ActualRadialCellComparison

/-!
# Actual characteristic speeds with a fixed joint derivative loss

The original N01 coefficient estimates give unweighted joint growth.
The discriminant is the actual polynomial in those three coefficients.
The quantitative positive optical collar controls its square root and
the reciprocal of the radial coefficient. Their product is the original
minus characteristic speed. Every resulting constant is uniform in the
component label and physical point; the fixed component powers are
retained explicitly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

section ScalarCoefficients

variable {ι E P : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {U : Set (E × P)} {a b c : E × P → ℝ}

private def scalarDiscriminantDirections
    (JA : SmoothDirections U a) (JB : SmoothDirections U b) (JC : SmoothDirections U c) :
    SmoothDirections U (fun z => b z ^ 2 - a z * c z) :=
  (smoothDirectionsProd JA (smoothDirectionsProd JB JC)).comp_contDiff isOpen_univ
    (((contDiff_snd.fst.pow 2).sub (contDiff_fst.mul contDiff_snd.snd)) :
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => q.2.1 ^ 2 - q.1 * q.2.2)).contDiffOn
    (fun _ _ => mem_univ _)

private def scalarMinusCharacteristicDirections
    (JA : SmoothDirections U a) (JB : SmoothDirections U b) (JC : SmoothDirections U c)
    (ha : ∀ z ∈ U, 0 < a z) (hd : ∀ z ∈ U, 0 < b z ^ 2 - a z * c z) :
    SmoothDirections U (fun z => b z / a z - Real.sqrt (b z ^ 2 - a z * c z) / a z) := by
  let JD := scalarDiscriminantDirections JA JB JC
  let JQ := JD.comp_contDiff isOpen_Ioi
    (contDiffOn_id.sqrt (fun t (ht : t ∈ Ioi (0 : ℝ)) => ht.ne')) hd
  let JI := JA.comp_contDiff isOpen_Ioi
    (contDiffOn_id.inv (fun t (ht : t ∈ Ioi (0 : ℝ)) => ht.ne')) ha
  let L : (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ
  let JN := smoothDirectionsPostContinuousLinear (smoothDirectionsProd JB JQ) L
  apply (JN.mul JI).congrOn
  intro z hz
  change (b z - Real.sqrt (b z ^ 2 - a z * c z)) * (a z)⁻¹ = _
  rw [div_eq_mul_inv, div_eq_mul_inv, sub_mul]

private theorem scalar_characteristic_joint_growth
    {U : Set E} {V : ι → Set P} {a b c : ι → E × P → ℝ}
    (JA : ∀ i, SmoothDirections (U ×ˢ V i) (a i))
    (JB : ∀ i, SmoothDirections (U ×ˢ V i) (b i))
    (JC : ∀ i, SmoothDirections (U ×ˢ V i) (c i))
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hIp : HasInterpolation p)
    (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i) (base loss : ℕ)
    (hA : UniformWeightedJointGrowth p (fun _ => 1) JA base loss)
    (hB : UniformWeightedJointGrowth p (fun _ => 1) JB base loss)
    (hC : UniformWeightedJointGrowth p (fun _ => 1) JC base loss)
    {lam P₀ : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P₀)
    (halower : ∀ i x, x ∈ U → ∀ y ∈ V i, lam * W i ^ (-P₀) ≤ a i (x, y))
    (hdlower : ∀ i x, x ∈ U → ∀ y ∈ V i,
      lam ^ 2 * W i ^ (-(2 * P₀)) ≤ b i (x, y) ^ 2 - a i (x, y) * c i (x, y))
    (K : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => b i z / a i z - Real.sqrt (b i z ^ 2 - a i z * c i z) / a i z)) :
    ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p W K B L := by
  have hWpos (i : ι) : 0 < W i := zero_lt_one.trans_le (hW i)
  have hapos (i : ι) (z : E × P) (hz : z ∈ U ×ˢ V i) : 0 < a i z :=
    (mul_pos hlam (Real.rpow_pos_of_pos (hWpos i) _)).trans_le
      (halower i z.1 hz.1 z.2 hz.2)
  have hdpos (i : ι) (z : E × P) (hz : z ∈ U ×ˢ V i) :
      0 < b i z ^ 2 - a i z * c i z :=
    (mul_pos (pow_pos hlam 2) (Real.rpow_pos_of_pos (hWpos i) _)).trans_le
      (hdlower i z.1 hz.1 z.2 hz.2)
  let JD := fun i => scalarDiscriminantDirections (JA i) (JB i) (JC i)
  let JQ := fun i => (JD i).comp_contDiff isOpen_Ioi
    (contDiffOn_id.sqrt (fun t (ht : t ∈ Ioi (0 : ℝ)) => ht.ne')) (hdpos i)
  let JI := fun i => (JA i).comp_contDiff isOpen_Ioi
    (contDiffOn_id.inv (fun t (ht : t ∈ Ioi (0 : ℝ)) => ht.ne')) (hapos i)
  let G : ℝ × (ℝ × ℝ) → ℝ := fun q => q.2.1 ^ 2 - q.1 * q.2.2
  have hG : ContDiff ℝ ∞ G :=
    (contDiff_snd.fst.pow 2).sub (contDiff_fst.mul contDiff_snd.snd)
  have htriple := hA.prodMk hp (fun _ => le_rfl) (hB.prodMk hp (fun _ => le_rfl) hC)
  obtain ⟨BD, LD, hBD, hLD, hD⟩ := htriple.comp_smooth_unweighted hp hIp G hG JD
  obtain ⟨BQ, LQ, hBQ, hLQ, hQ⟩ := (hD.withWeight W).sqrt hp hIp hW
    (pow_pos hlam 2) (show 0 ≤ 2 * P₀ from mul_nonneg (by norm_num) hP) hdlower JQ
  obtain ⟨BI, LI, hBI, hLI, hI⟩ := (hA.withWeight W).inv hp hIp hW hlam hP halower JI
  let B : ℕ := max base (max BQ BI)
  let L : ℕ := max loss (max LQ LI)
  have hW0 (i : ι) : 0 ≤ W i := zero_le_one.trans (hW i)
  have hBw : UniformWeightedJointGrowth p W JB B L :=
    (hB.withWeight W).mono hp hW0 (le_max_left _ _) (le_max_left _ _)
  have hQw : UniformWeightedJointGrowth p W JQ B L :=
    hQ.mono hp hW0 ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _))
  have hIw : UniformWeightedJointGrowth p W JI B L :=
    hI.mono hp hW0 ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _))
  let subL : (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ
  let JN := fun i => smoothDirectionsPostContinuousLinear (smoothDirectionsProd (JB i) (JQ i)) subL
  have hN : UniformWeightedJointGrowth p W JN B L := hBw.sub hp hW hQw JN
  let JP := fun i => (JN i).mul (JI i)
  obtain ⟨B', L', hB', hL', hP'⟩ := hN.mul hp hIp hW hIw JP
  refine ⟨B', L', (le_max_left _ _).trans hB', (le_max_left _ _).trans hL', ?_⟩
  apply hP'.congr K
  intro i z hz
  change (b i z - Real.sqrt (b i z ^ 2 - a i z * c i z)) * (a i z)⁻¹ = _
  rw [div_eq_mul_inv, div_eq_mul_inv, sub_mul]

end ScalarCoefficients

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

local instance n01CharacteristicJointGrowthStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The original joint coefficient tower restricted to a buffered strip.
Its derivatives remain exactly those of the original N01 tower. -/
def N01Properties.originalCoefficient_stripTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    (i : Fin 3) (m : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        originalCoefficientEntry D S C i (liftSectorParameter S C x.1) x.2) :=
  (hN.originalCoefficient_parameterSpatialTower hS hT m (j m) (hcell m) i).restrict
    ((sectorNeighborhood_isOpen S base ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ⟨hx.1, ⟨(hl m).trans hx.2.1.1, hx.2.1.2.trans (hh m)⟩, hx.2.2⟩)

theorem N01Properties.originalCoefficient_stripTower_apply
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    (i : Fin 3) (m n : ℕ) (z : (StateDirections S × ℝ) × PolarPoint)
    (v : Fin n → (StateDirections S × ℝ) × PolarPoint) :
    (hN.originalCoefficient_stripTower hS hT j hcell l h hl hh i m).D n z v =
      (hN.originalCoefficient_parameterSpatialTower hS hT m (j m) (hcell m) i).D n z v := rfl

theorem N01Properties.originalCoefficient_strip_joint_growth
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    (i : Fin 3) :
    UniformWeightedJointGrowth (pairGrading (sectorGrading S) realGrading) (fun _ => 1)
      (hN.originalCoefficient_stripTower hS hT j hcell l h hl hh i) base loss := by
  apply uniformWeightedJointGrowth_of_mixed_parameter_oneHigh
    (hN.originalCoefficient_stripTower hS hT j hcell l h hl hh i)
    (fun _ => isOpen_Ioo.prod isOpen_univ)
    (fun m => (sectorNeighborhood_convex S base ε ε).prod
      ((convex_Ioo (l m) (h m)).prod convex_univ))
    (pairGrading (sectorGrading S) realGrading) (sectorPairGrading_monotone S)
    (fun _ => 1) base loss base le_rfl
  intro R hR n s
  let data := hN.originalCoefficient_joint_mixed_uniform_oneHigh hS hT n s
  refine ⟨data.choose, data.choose_spec.1, ?_⟩
  intro m x hx hlow y hy v a b hab
  have heq : (fun q =>
      (hN.originalCoefficient_stripTower hS hT j hcell l h hl hh i m).D
        n (x, q) (fun k => (v k, 0))) =
      fun q => (hN.originalCoefficient_parameterSpatialTower hS hT m (j m) (hcell m) i).D
        n (x, q) (fun k => (v k, 0)) :=
    funext fun q => hN.originalCoefficient_stripTower_apply hS hT j hcell l h hl hh i m n
      (x, q) (fun k => (v k, 0))
  exact (congrArg (fun g : PolarPoint → ℝ => |mixedDerivative a b g y|) heq).trans_le
    (data.choose_spec.2 m (j m) (hcell m) i a b hab x hx v y
      ⟨⟨(hl m).trans hy.1.1, hy.1.2.trans (hh m)⟩, hy.2⟩)

private theorem originalCoefficientEntry_zero_apply
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    originalCoefficientEntry D S C 0 z p = (originalCoefficients D S C z).a p := by
  simp only [originalCoefficientEntry, if_pos rfl]

private theorem originalCoefficientEntry_one_apply
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    originalCoefficientEntry D S C 1 z p = (originalCoefficients D S C z).b p := by
  norm_num [originalCoefficientEntry]

private theorem originalCoefficientEntry_two_apply
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    originalCoefficientEntry D S C 2 z p = (originalCoefficients D S C z).c p := by
  norm_num [originalCoefficientEntry]

/-- The actual buffered-collar hypotheses suffice for the genuine
characteristic tower; no parameter regularity is assumed here. -/
def N01Properties.minusCharacteristicSpeed_stripTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    (hapos : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ (m : ℕ) (p : PolarPoint),
      p.1 ∈ Ioo (l m) (h m) → 0 < (originalCoefficients D S C (liftSectorParameter S C z)).a p)
    (hdpos : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ (m : ℕ) (p : PolarPoint),
      p.1 ∈ Ioo (l m) (h m) →
        0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C z)).a p *
            (originalCoefficients D S C (liftSectorParameter S C z)).c p)
    (m : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) x.2) := by
  let J := hN.originalCoefficient_stripTower hS hT j hcell l h hl hh
  have ha (x : (StateDirections S × ℝ) × PolarPoint)
      (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ)) :
      0 < originalCoefficientEntry D S C 0 (liftSectorParameter S C x.1) x.2 := by
    rw [originalCoefficientEntry_zero_apply]
    exact hapos x.1 hx.1 m x.2 hx.2.1
  have hd (x : (StateDirections S × ℝ) × PolarPoint)
      (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ)) :
      0 < originalCoefficientEntry D S C 1 (liftSectorParameter S C x.1) x.2 ^ 2 -
        originalCoefficientEntry D S C 0 (liftSectorParameter S C x.1) x.2 *
          originalCoefficientEntry D S C 2 (liftSectorParameter S C x.1) x.2 := by
    rw [originalCoefficientEntry_zero_apply, originalCoefficientEntry_one_apply,
      originalCoefficientEntry_two_apply]
    exact hdpos x.1 hx.1 m x.2 hx.2.1
  apply (scalarMinusCharacteristicDirections (J 0 m) (J 1 m) (J 2 m) ha hd).congrOn
  intro x hx
  simp only [originalCoefficientEntry_zero_apply, originalCoefficientEntry_one_apply,
    originalCoefficientEntry_two_apply, minusCharacteristicSpeed]

/-- Quantitative positivity on the same actual buffered strips gives
fixed-loss growth for any genuine tower of the original minus speed. -/
theorem N01Properties.minusCharacteristicSpeed_strip_joint_growth
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
    (K : ∀ m, SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) x.2)) :
    ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧
      UniformWeightedJointGrowth (pairGrading (sectorGrading S) realGrading)
        (fun m => radialE (D.cellIndex (j m))) K B L := by
  let p := pairGrading (sectorGrading S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone S
  have hIp : HasInterpolation p := hasInterpolation_of_hasSmoothing hp
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  let J := hN.originalCoefficient_stripTower hS hT j hcell l h hl hh
  have hJ (i : Fin 3) : UniformWeightedJointGrowth p (fun _ => 1) (J i) base loss :=
    hN.originalCoefficient_strip_joint_growth hS hT j hcell l h hl hh i
  have ha (m : ℕ) (x : StateDirections S × ℝ)
      (hx : x ∈ sectorNeighborhood S base ε ε) (y : PolarPoint)
      (hy : y ∈ Ioo (l m) (h m) ×ˢ (univ : Set ℝ)) :
      (lam / 2) * W m ^ (-P) ≤ originalCoefficientEntry D S C 0 (liftSectorParameter S C x) y := by
    rw [originalCoefficientEntry_zero_apply]
    have h := (hpositive (liftSectorParameter S C x)
      (liftSectorParameter_mem_stateNeighborhood hx le_rfl) m y hy.1).1
    exact (by ring : (lam / 2) * W m ^ (-P) = lam * W m ^ (-P) / 2).trans_le h
  have hd (m : ℕ) (x : StateDirections S × ℝ)
      (hx : x ∈ sectorNeighborhood S base ε ε) (y : PolarPoint)
      (hy : y ∈ Ioo (l m) (h m) ×ˢ (univ : Set ℝ)) :
      (lam / 2) ^ 2 * W m ^ (-(2 * P)) ≤
        originalCoefficientEntry D S C 1 (liftSectorParameter S C x) y ^ 2 -
          originalCoefficientEntry D S C 0 (liftSectorParameter S C x) y *
            originalCoefficientEntry D S C 2 (liftSectorParameter S C x) y := by
    rw [originalCoefficientEntry_zero_apply, originalCoefficientEntry_one_apply,
      originalCoefficientEntry_two_apply]
    have hw : (W m ^ (-P)) ^ 2 = W m ^ (-(2 * P)) := by
      rw [pow_two, ← Real.rpow_add (zero_lt_one.trans_le (hW m))]
      congr 1
      ring
    have he : (lam / 2) ^ 2 * W m ^ (-(2 * P)) = (lam * W m ^ (-P) / 2) ^ 2 := by
      rw [← hw]
      ring
    exact he.trans_le (hpositive (liftSectorParameter S C x)
      (liftSectorParameter_mem_stateNeighborhood hx le_rfl) m y hy.1).2
  let K' := fun m => (K m).congrOn
    (g := fun x : (StateDirections S × ℝ) × PolarPoint =>
      originalCoefficientEntry D S C 1 (liftSectorParameter S C x.1) x.2 /
          originalCoefficientEntry D S C 0 (liftSectorParameter S C x.1) x.2 -
        Real.sqrt (originalCoefficientEntry D S C 1 (liftSectorParameter S C x.1) x.2 ^ 2 -
          originalCoefficientEntry D S C 0 (liftSectorParameter S C x.1) x.2 *
            originalCoefficientEntry D S C 2 (liftSectorParameter S C x.1) x.2) /
              originalCoefficientEntry D S C 0 (liftSectorParameter S C x.1) x.2)
    (by intro x hx; simp only [originalCoefficientEntry_zero_apply, originalCoefficientEntry_one_apply,
      originalCoefficientEntry_two_apply, minusCharacteristicSpeed])
  obtain ⟨B, L, hB, hL, hb⟩ := scalar_characteristic_joint_growth (J 0) (J 1) (J 2)
    p hp hIp W hW base loss (hJ 0) (hJ 1) (hJ 2) (half_pos hlam) hP ha hd K'
  refine ⟨B, L, hB, hL, ?_⟩
  exact hb.congr K (by intro m x hx; simp only [originalCoefficientEntry_zero_apply,
    originalCoefficientEntry_one_apply, originalCoefficientEntry_two_apply, minusCharacteristicSpeed])

/-- A complete actual tower and its uniform fixed-loss estimate are
constructed from the same quantitative collar witnesses. -/
theorem N01Properties.exists_minusCharacteristicSpeed_strip_joint_growth
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
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    ∃ K : ∀ m, SmoothDirections
        (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
        (fun x : (StateDirections S × ℝ) × PolarPoint =>
          minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) x.2),
      ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧
        UniformWeightedJointGrowth (pairGrading (sectorGrading S) realGrading)
          (fun m => radialE (D.cellIndex (j m))) K B L := by
  have hd (m : ℕ) : 0 < lam * radialE (D.cellIndex (j m)) ^ (-P) / 2 :=
    half_pos (mul_pos hlam (Real.rpow_pos_of_pos
      (zero_lt_one.trans_le (one_le_radialE_of_nat _)) _))
  have ha (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (l m) (h m)) :
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).a p :=
    (hd m).trans_le (hpositive (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl) m p hp).1
  have hdisc (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (l m) (h m)) :
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p :=
    (pow_pos (hd m) 2).trans_le (hpositive (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl) m p hp).2
  let K := hN.minusCharacteristicSpeed_stripTower hS hT j hcell l h hl hh ha hdisc
  exact ⟨K, hN.minusCharacteristicSpeed_strip_joint_growth
    hS hT j hcell l h hl hh hlam hP hpositive K⟩

end ContinuousFlexibility.Statements
