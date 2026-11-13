import ContinuousFlexibility.Analysis.N04CoefficientIncrementJointGain
import ContinuousFlexibility.Analysis.N01CharacteristicJointGrowth
import ContinuousFlexibility.Analysis.WeightedJointProducts

/-!
# The actual discriminant increment retains its sample height gain

The original coefficient towers and their reference restrictions are
combined with the already normalized increment towers. Three products
give the literal discriminant difference on the same physical strip.
The low base and loss are chosen before every joint derivative order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

local instance n04DiscriminantIncrementStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

/-- The same original discriminant difference, normalized by the fixed
host sample height, has a genuine joint tower with one fixed loss. -/
theorem N01Properties.exists_discriminantIncrement_strip_joint_growth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ)
    (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m)
    (hh : ∀ m, h m < C.right m) :
    ∃ K : ∀ m, SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun z : (StateDirections S × ℝ) × PolarPoint =>
        (((originalCoefficients D S C (liftSectorParameter S C z.1)).b z.2 ^ 2 -
            (originalCoefficients D S C (liftSectorParameter S C z.1)).a z.2 *
              (originalCoefficients D S C (liftSectorParameter S C z.1)).c z.2) -
          ((originalCoefficients D S C (C.referenceState, 0)).b z.2 ^ 2 -
            (originalCoefficients D S C (C.referenceState, 0)).a z.2 *
              (originalCoefficients D S C (C.referenceState, 0)).c z.2)) /
          T.H (T.sample (j m)) ^ (3 / 4 : ℝ)),
      ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧
        UniformWeightedJointGrowth (pairGrading (sectorGrading S) realGrading)
          (fun m => radialE (D.cellIndex (j m))) K B L := by
  classical
  let E : Type := StateDirections S × ℝ
  let p : ℕ → Seminorm ℝ E := pairGrading (sectorGrading S) realGrading
  let U : Set E := sectorNeighborhood S base ε ε
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  let H : ℕ → ℝ := fun m => T.H (T.sample (j m)) ^ (3 / 4 : ℝ)
  let f : Fin 3 → ℕ → E × PolarPoint → ℝ := fun i _ z =>
    originalCoefficientEntry D S C i (liftSectorParameter S C z.1) z.2
  let f0 : Fin 3 → ℕ → E × PolarPoint → ℝ := fun i _ z =>
    originalCoefficientEntry D S C i (C.referenceState, 0) z.2
  let d : Fin 3 → ℕ → E × PolarPoint → ℝ := fun i m z =>
    (H m)⁻¹ * coefficientFamily D S C i 0 0 z.2 (liftSectorParameter S C z.1)
  have hp : Monotone p := sectorPairGrading_monotone S
  have hIp : HasInterpolation p := hasInterpolation_of_hasSmoothing hp
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hW0 (m : ℕ) : 0 ≤ W m := zero_le_one.trans (hW m)
  have hUV (m : ℕ) : IsOpen (U ×ˢ V m) :=
    (sectorNeighborhood_isOpen S base ε ε).prod (isOpen_Ioo.prod isOpen_univ)
  have hzU : (0 : E) ∈ U := by
    simpa only [U, sectorNeighborhood, Set.mem_setOf_eq, Prod.fst_zero,
      Prod.snd_zero, map_zero, abs_zero] using And.intro hN.2.1 hN.2.1
  let J : ∀ i m, SmoothDirections (U ×ˢ V m) (f i m) := fun i m =>
    hN.originalCoefficient_stripTower hS hT j hcell l h hl hh i m
  have hJu (i : Fin 3) : UniformWeightedJointGrowth p (fun _ => 1) (J i) base loss :=
    hN.originalCoefficient_strip_joint_growth hS hT j hcell l h hl hh i
  have hJ (i : Fin 3) : UniformWeightedJointGrowth p W (J i) base loss :=
    (hJu i).withWeight W
  let L0 : (E × PolarPoint) →L[ℝ] (E × PolarPoint) :=
    (0 : (E × PolarPoint) →L[ℝ] E).prod (ContinuousLinearMap.snd ℝ E PolarPoint)
  have hL0 (z : E × PolarPoint) : L0 z = (0, z.2) := by
    simp only [L0, ContinuousLinearMap.prod_apply, _root_.zero_apply,
      ContinuousLinearMap.coe_snd']
  have hmap (m : ℕ) : MapsTo (fun z => (0 : E × PolarPoint) + L0 z)
      (U ×ˢ V m) (U ×ˢ V m) := by
    intro z hz
    simpa only [zero_add, hL0] using And.intro hzU hz.2
  let J0 : ∀ i m, SmoothDirections (U ×ˢ V m) (f0 i m) := fun i m =>
    ((J i m).compAffine L0 0 (hUV m) (hmap m)).congrOn (by
      intro z hz
      simp [f, f0, hL0, liftSectorParameter])
  have hJ0 (i : Fin 3) : UniformWeightedJointGrowth p W (J0 i) base loss := by
    have href : UniformWeightedJointGrowth p (fun _ => 1) (J0 i) base loss := by
      intro R hR n
      obtain ⟨A, Q, hA, _, hb⟩ := hJu i 0 le_rfl n
      refine ⟨A, 0, hA, le_rfl, ?_⟩
      intro m x hx _ y hy v hv
      have hu (k : Fin n) : p base (0 : E) + ‖(v k).2‖ ≤ 1 := by
        rw [map_zero, zero_add]
        exact (le_add_of_nonneg_left (apply_nonneg (p base) (v k).1)).trans (hv k)
      have hb0 := hb m 0 hzU (by simp only [map_zero, le_refl]) y hy
        (fun k => ((0 : E), (v k).2)) hu
      have heq : (J0 i m).D n (x, y) v =
          (J i m).D n (0, y) (fun k => ((0 : E), (v k).2)) := by
        simp only [J0, SmoothDirections.congrOn, SmoothDirections.compAffine_apply,
          zero_add, hL0]
      rw [heq]
      have hbound : ‖(J i m).D n (0, y) (fun k => ((0 : E), (v k).2))‖ ≤ A := by
        simpa only [map_zero, Finset.sum_const_zero, add_zero, Real.one_rpow, mul_one] using hb0
      have hone : 1 ≤ 1 + p (n + loss) x + ∑ k, p (n + loss) (v k).1 := by
        have hs := Finset.sum_nonneg (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
          apply_nonneg (p (n + loss)) (v k).1)
        linarith [apply_nonneg (p (n + loss)) x]
      simpa only [Real.one_rpow, mul_one] using
        hbound.trans (le_mul_of_one_le_right hA hone)
    exact href.withWeight W
  let JD : ∀ i m, SmoothDirections (U ×ˢ V m) (d i m) := fun i m =>
    ((smoothDirectionsScalarPostcompose
      (hN.coefficientIncrement_parameterSpatialTower hS hT m (j m) (hcell m) i)
      ((H m)⁻¹ • ContinuousLinearMap.id ℝ ℝ)).restrict (hUV m)
        (fun z hz => ⟨hz.1, ⟨(hl m).trans hz.2.1.1, hz.2.1.2.trans (hh m)⟩, hz.2.2⟩)).congrOn
      (by intro z hz; simp only [d, _root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul])
  have hJD (i : Fin 3) : UniformWeightedJointGrowth p W (JD i) base loss := by
    intro R hR n
    obtain ⟨A, Q, hA, hQ, hb⟩ := hN.coefficientIncrement_normalized_joint_growth hS hT j hcell i R hR n
    refine ⟨A, Q, hA, hQ, fun m x hx hlow y hy v hv => ?_⟩
    exact hb m x hx hlow y ⟨⟨(hl m).trans hy.1.1, hy.1.2.trans (hh m)⟩, hy.2⟩ v hv
  let addL : (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ
  let JS : ∀ m, SmoothDirections (U ×ˢ V m)
      (fun z => f 1 m z + f0 1 m z) := fun m => smoothDirectionsAdd (J 1 m) (J0 1 m)
  have hJS : UniformWeightedJointGrowth p W JS base loss := by
    apply (((hJ 1).prodMk hp hW (hJ0 1)).postLinear addL).congr JS
    intro m z hz
    simp only [addL, _root_.add_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  let T1 : ∀ m, SmoothDirections (U ×ˢ V m)
      (fun z => (f 1 m z + f0 1 m z) * d 1 m z) := fun m => (JS m).mul (JD 1 m)
  let T2 : ∀ m, SmoothDirections (U ×ˢ V m)
      (fun z => f 2 m z * d 0 m z) := fun m => (J 2 m).mul (JD 0 m)
  let T3 : ∀ m, SmoothDirections (U ×ˢ V m)
      (fun z => f0 0 m z * d 2 m z) := fun m => (J0 0 m).mul (JD 2 m)
  obtain ⟨B1, L1, hb1, hl1, ht1⟩ := hJS.mul hp hIp hW (hJD 1) T1
  obtain ⟨B2, L2, hb2, hl2, ht2⟩ := (hJ 2).mul hp hIp hW (hJD 0) T2
  obtain ⟨B3, L3, hb3, hl3, ht3⟩ := (hJ0 0).mul hp hIp hW (hJD 2) T3
  let B : ℕ := max B1 (max B2 B3)
  let L : ℕ := max L1 (max L2 L3)
  have ht1' : UniformWeightedJointGrowth p W T1 B L :=
    ht1.mono hp hW0 (le_max_left _ _) (le_max_left _ _)
  have ht2' : UniformWeightedJointGrowth p W T2 B L :=
    ht2.mono hp hW0 ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _))
  have ht3' : UniformWeightedJointGrowth p W T3 B L :=
    ht3.mono hp hW0 ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _))
  let subL : (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ
  let T12 : ∀ m, SmoothDirections (U ×ˢ V m)
      (fun z => (f 1 m z + f0 1 m z) * d 1 m z - f 2 m z * d 0 m z) := fun m =>
    (smoothDirectionsPostContinuousLinear (smoothDirectionsProd (T1 m) (T2 m)) subL).congrOn
      (by intro z hz; simp only [subL, _root_.sub_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'])
  let KT : ∀ m, SmoothDirections (U ×ˢ V m)
      (fun z => ((f 1 m z + f0 1 m z) * d 1 m z - f 2 m z * d 0 m z) -
        f0 0 m z * d 2 m z) := fun m =>
    (smoothDirectionsPostContinuousLinear (smoothDirectionsProd (T12 m) (T3 m)) subL).congrOn
      (by intro z hz; simp only [subL, _root_.sub_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'])
  have hKT : UniformWeightedJointGrowth p W KT B L :=
    (ht1'.sub hp hW ht2' T12).sub hp hW ht3' KT
  have heq (m : ℕ) (z : E × PolarPoint) :
      ((f 1 m z + f0 1 m z) * d 1 m z - f 2 m z * d 0 m z) -
        f0 0 m z * d 2 m z =
      (((originalCoefficients D S C (liftSectorParameter S C z.1)).b z.2 ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C z.1)).a z.2 *
            (originalCoefficients D S C (liftSectorParameter S C z.1)).c z.2) -
        ((originalCoefficients D S C (C.referenceState, 0)).b z.2 ^ 2 -
          (originalCoefficients D S C (C.referenceState, 0)).a z.2 *
            (originalCoefficients D S C (C.referenceState, 0)).c z.2)) / H m := by
    norm_num [f, f0, d, coefficientFamily, mixedDerivative, iteratedDeriv_zero,
      originalCoefficientEntry, ite_apply, div_eq_mul_inv]
    <;> ring
  let K := fun m => (KT m).congrOn (fun z _ => heq m z)
  refine ⟨K, B, L, hb1.trans (le_max_left _ _), hl1.trans (le_max_left _ _), ?_⟩
  exact hKT.congr K (fun m z _ => heq m z)

end ContinuousFlexibility.Statements
