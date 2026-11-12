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

private theorem scalar_characteristic_algebra (a b c : ℝ) :
    (b - Real.sqrt (b ^ 2 - a * c)) * a⁻¹ =
      b / a - Real.sqrt (b ^ 2 - a * c) / a := by
  simp only [div_eq_mul_inv, sub_mul]

private theorem scalar_characteristic_half_mul (a b : ℝ) :
    (a / 2) * b = a * b / 2 := by
  ring

private theorem scalar_characteristic_half_rpow_sq (a W P : ℝ) (hW : 0 < W) :
    (a / 2) ^ 2 * W ^ (-(2 * P)) = (a * W ^ (-P) / 2) ^ 2 := by
  have hw : (W ^ (-P)) ^ 2 = W ^ (-(2 * P)) := by
    rw [pow_two, ← Real.rpow_add hW]
    congr 1
    ring
  rw [← hw]
  ring

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
  exact scalar_characteristic_algebra (a z) (b z) (c z)

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
  exact scalar_characteristic_algebra (a i z) (b i z) (c i z)

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
  simp only [originalCoefficientEntry, eq_self_iff_true, ite_true]

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

private theorem originalCoefficientEntry_discriminant_apply
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    originalCoefficientEntry D S C 1 z p ^ 2 -
        originalCoefficientEntry D S C 0 z p * originalCoefficientEntry D S C 2 z p =
      (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p :=
  congrArg₂ (fun b ac : ℝ => b ^ 2 - ac)
    (originalCoefficientEntry_one_apply D S C z p)
    (congrArg₂ (fun a c : ℝ => a * c)
      (originalCoefficientEntry_zero_apply D S C z p)
      (originalCoefficientEntry_two_apply D S C z p))

private theorem originalCoefficientEntry_minus_apply
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    originalCoefficientEntry D S C 1 z p / originalCoefficientEntry D S C 0 z p -
        Real.sqrt (originalCoefficientEntry D S C 1 z p ^ 2 -
          originalCoefficientEntry D S C 0 z p * originalCoefficientEntry D S C 2 z p) /
            originalCoefficientEntry D S C 0 z p =
      minusCharacteristicSpeed (originalCoefficients D S C z) p :=
  congrArg (fun q : ℝ × ℝ × ℝ =>
    q.2.1 / q.1 - Real.sqrt (q.2.1 ^ 2 - q.1 * q.2.2) / q.1)
    (Prod.ext (originalCoefficientEntry_zero_apply D S C z p)
      (Prod.ext (originalCoefficientEntry_one_apply D S C z p)
        (originalCoefficientEntry_two_apply D S C z p)))

private theorem minusCharacteristicSpeed_stripTower_nonempty
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
    Nonempty (SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) x.2)) := by
  let U : Set (StateDirections S × ℝ) := sectorNeighborhood S base ε ε
  let V : Set PolarPoint := Ioo (l m) (h m) ×ˢ univ
  let f : Fin 3 → (StateDirections S × ℝ) × PolarPoint → ℝ := fun i x =>
    originalCoefficientEntry D S C i (liftSectorParameter S C x.1) x.2
  let J : ∀ i : Fin 3, SmoothDirections (U ×ˢ V) (f i) := fun i =>
    hN.originalCoefficient_stripTower hS hT j hcell l h hl hh i m
  have ha (x : (StateDirections S × ℝ) × PolarPoint)
      (hx : x ∈ U ×ˢ V) : 0 < f 0 x :=
    (hapos x.1 hx.1 m x.2 hx.2.1).trans_eq
      (originalCoefficientEntry_zero_apply D S C (liftSectorParameter S C x.1) x.2).symm
  have hd (x : (StateDirections S × ℝ) × PolarPoint)
      (hx : x ∈ U ×ˢ V) : 0 < f 1 x ^ 2 - f 0 x * f 2 x :=
    (hdpos x.1 hx.1 m x.2 hx.2.1).trans_eq
      (originalCoefficientEntry_discriminant_apply D S C
        (liftSectorParameter S C x.1) x.2).symm
  let K : SmoothDirections (U ×ˢ V)
      (fun x => f 1 x / f 0 x - Real.sqrt (f 1 x ^ 2 - f 0 x * f 2 x) / f 0 x) :=
    scalarMinusCharacteristicDirections (J 0) (J 1) (J 2) ha hd
  refine ⟨K.congrOn ?_⟩
  intro x hx
  exact originalCoefficientEntry_minus_apply D S C (liftSectorParameter S C x.1) x.2

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
        minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) x.2) :=
  Classical.choice (minusCharacteristicSpeed_stripTower_nonempty
    hN hS hT j hcell l h hl hh hapos hdpos m)

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
  let p : ℕ → Seminorm ℝ (StateDirections S × ℝ) :=
    pairGrading (sectorGrading S) realGrading
  let U : Set (StateDirections S × ℝ) := sectorNeighborhood S base ε ε
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let f : Fin 3 → ℕ → (StateDirections S × ℝ) × PolarPoint → ℝ := fun i _ x =>
    originalCoefficientEntry D S C i (liftSectorParameter S C x.1) x.2
  have hp : Monotone p := sectorPairGrading_monotone S
  have hIp : HasInterpolation p := hasInterpolation_of_hasSmoothing hp
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  let J : ∀ i m, SmoothDirections (U ×ˢ V m) (f i m) := fun i m =>
    hN.originalCoefficient_stripTower hS hT j hcell l h hl hh i m
  have hJ (i : Fin 3) : UniformWeightedJointGrowth p (fun _ => 1) (J i) base loss :=
    hN.originalCoefficient_strip_joint_growth hS hT j hcell l h hl hh i
  have ha (m : ℕ) (x : StateDirections S × ℝ)
      (hx : x ∈ U) (y : PolarPoint) (hy : y ∈ V m) :
      (lam / 2) * W m ^ (-P) ≤ f 0 m (x, y) := by
    have hbound : lam * W m ^ (-P) / 2 ≤
        (originalCoefficients D S C (liftSectorParameter S C x)).a y :=
      (hpositive (liftSectorParameter S C x)
        (liftSectorParameter_mem_stateNeighborhood (C := C) hx le_rfl) m y hy.1).1
    exact ((scalar_characteristic_half_mul lam (W m ^ (-P))).trans_le hbound).trans_eq
      (originalCoefficientEntry_zero_apply D S C (liftSectorParameter S C x) y).symm
  have hd (m : ℕ) (x : StateDirections S × ℝ)
      (hx : x ∈ U) (y : PolarPoint) (hy : y ∈ V m) :
      (lam / 2) ^ 2 * W m ^ (-(2 * P)) ≤
        f 1 m (x, y) ^ 2 - f 0 m (x, y) * f 2 m (x, y) := by
    have hbound : (lam * W m ^ (-P) / 2) ^ 2 ≤
        (originalCoefficients D S C (liftSectorParameter S C x)).b y ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C x)).a y *
            (originalCoefficients D S C (liftSectorParameter S C x)).c y :=
      (hpositive (liftSectorParameter S C x)
        (liftSectorParameter_mem_stateNeighborhood (C := C) hx le_rfl) m y hy.1).2
    exact ((scalar_characteristic_half_rpow_sq lam (W m) P
      (zero_lt_one.trans_le (hW m))).trans_le hbound).trans_eq
        (originalCoefficientEntry_discriminant_apply D S C
          (liftSectorParameter S C x) y).symm
  let K' : ∀ m, SmoothDirections (U ×ˢ V m)
      (fun x => f 1 m x / f 0 m x -
        Real.sqrt (f 1 m x ^ 2 - f 0 m x * f 2 m x) / f 0 m x) := fun m =>
    (K m).congrOn (fun x _ =>
      (originalCoefficientEntry_minus_apply D S C (liftSectorParameter S C x.1) x.2).symm)
  let data : ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p W K' B L :=
    scalar_characteristic_joint_growth (ι := ℕ) (E := StateDirections S × ℝ)
      (P := PolarPoint) (U := U) (V := V) (a := f 0) (b := f 1) (c := f 2)
      (J 0) (J 1) (J 2) p hp hIp W hW base loss (hJ 0) (hJ 1) (hJ 2)
      (lam := lam / 2) (P₀ := P) (half_pos hlam) hP ha hd K'
  let B : ℕ := data.choose
  let L : ℕ := data.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.1
  have hL : loss ≤ B := data.choose_spec.choose_spec.2.1
  have hb : UniformWeightedJointGrowth p W K' B L := data.choose_spec.choose_spec.2.2
  exact ⟨B, L, hB, hL, hb.congr K (fun m x _ =>
    originalCoefficientEntry_minus_apply D S C (liftSectorParameter S C x.1) x.2)⟩

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
