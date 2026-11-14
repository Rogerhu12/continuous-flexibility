import ContinuousFlexibility.Analysis.N04RealizationPrincipalHalfBounds
import ContinuousFlexibility.Analysis.N04SourceColumnsSmallness

/-!
# One state neighborhood preserves all actual interior travel lower bounds

The first parameter jet alone chooses the neighborhood. Its positive
height factor absorbs every sampled material power, including the
inverse reference travel on a smaller root overlap. All later state and
spatial orders therefore use the same positive value interval.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

private theorem currentBand_firstJet_ball
    {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (base loss : ℕ)
    {U : Set X} (hconvex : Convex ℝ U) (hzero : (0 : X) ∈ U)
    {f : I → X → ℝ} (J : ∀ i, SmoothDirections U (f i))
    (M r : I → ℝ) (Q : ℝ) (hQ : 0 < Q) (hM : ∀ i, 0 ≤ M i)
    (hprod : ∀ i, M i * r i ≤ Q)
    (href : ∀ i, 0 < f i 0 ∧ (f i 0)⁻¹ ≤ r i)
    (hfirst : ∀ i y, y ∈ U → ∀ v : Fin 1 → X,
      |(J i).D 1 y v| ≤ M i * oneHighVariationWeight p base loss y v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i x, x ∈ U → p (max base loss) x < δ →
      f i 0 / 2 ≤ f i x ∧ 0 < f i x ∧ (f i x)⁻¹ ≤ 2 * r i := by
  refine ⟨min 1 (6 * Q)⁻¹,
    lt_min zero_lt_one (inv_pos.mpr (mul_pos (by norm_num) hQ)), ?_⟩
  intro i x hx hsmall
  have hlow : p base x ≤ 1 :=
    (hp (le_max_left _ _) x).trans (hsmall.le.trans (min_le_left _ _))
  have hfirstHigh : ∀ y ∈ U, ∀ v : Fin 1 → X,
      |(J i).D 1 y v| ≤ M i * oneHighVariationWeight p base (max base loss) y v := by
    intro y hy v
    exact (hfirst i y hy v).trans (mul_le_mul_of_nonneg_left
      (oneHighVariationWeight_mono hp le_rfl (le_max_right base loss) y v) (hM i))
  exact n04Realization_firstJet_half_reference (J i) p base (max base loss)
    (hp (le_max_left _ _)) hconvex hzero (hM i) hQ (hprod i)
    (href i).1 (href i).2 hfirstHigh hx hlow (hsmall.trans_le (min_le_right _ _))

private theorem currentBand_envelope_product
    {c B E H N P A : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B) (hE : 0 < E)
    (henv : H * E ^ (P + A) ≤ N) :
    (c * E ^ P * H) * (B * E ^ A) ≤ c * B * N := by
  calc
    _ = c * B * (H * E ^ (P + A)) := by rw [Real.rpow_add hE]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left henv (mul_nonneg hc hB)

private theorem currentBand_sector_radius {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ η ≤ 1 / 2 ∧ 2 * η ≤ δ := by
  let η : ℝ := min ε (min (1 / 2) (δ / 2))
  have hηδ : η ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η, lt_min hε (lt_min (by norm_num) (half_pos hδ)),
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  linarith only [hηδ]

set_option diagnostics true in
private theorem currentBand_material_ball
    {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (sample : I → ℕ) (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (base loss : ℕ)
    {U : Set X} (hconvex : Convex ℝ U) (hzero : (0 : X) ∈ U)
    (f : I → X → ℝ) (J : ∀ i, SmoothDirections U (f i))
    (c P B A : ℝ) (hc : 0 < c) (hB : 0 < B)
    (href : ∀ i, 0 < f i 0 ∧ (f i 0)⁻¹ ≤ B * T.E0 (T.sample (sample i)) ^ A)
    (hfirst : ∀ i x, x ∈ U → ∀ v : Fin 1 → X,
      |(J i).D 1 x v| ≤ c * T.E0 (T.sample (sample i)) ^ P *
        T.H (T.sample (sample i)) ^ (3 / 4 : ℝ) * oneHighVariationWeight p base loss x v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i x, x ∈ U → p (max base loss) x < δ →
      f i 0 / 2 ≤ f i x ∧ 0 < f i x ∧
        (f i x)⁻¹ ≤ 2 * B * T.E0 (T.sample (sample i)) ^ A := by
  refine (n07a_materialSample_envelope_bound hD hT
    (by norm_num : 0 < (3 / 4 : ℝ)) (P + A)).elim ?_
  intro N hNdata
  let E : I → ℝ := fun i => T.E0 (T.sample (sample i))
  let H : I → ℝ := fun i => T.H (T.sample (sample i)) ^ (3 / 4 : ℝ)
  let M : I → ℝ := fun i => c * E i ^ P * H i
  let r : I → ℝ := fun i => B * E i ^ A
  let Q : ℝ := c * B * N
  have hQ : 0 < Q := mul_pos (mul_pos hc hB) hNdata.1
  have hpos (i : I) : 0 < E i ∧ 0 ≤ H i := by
    have hs := hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (sample i))
    exact ⟨hs.2.2.1, Real.rpow_nonneg hs.2.1.le _⟩
  have hM (i : I) : 0 ≤ M i :=
    mul_nonneg (mul_nonneg hc.le (Real.rpow_nonneg (hpos i).1.le P)) (hpos i).2
  have hprod (i : I) : M i * r i ≤ Q :=
    currentBand_envelope_product hc.le hB.le (hpos i).1 (hNdata.2 (sample i))
  refine (currentBand_firstJet_ball p hp base loss hconvex hzero J M r Q
    hQ hM hprod href hfirst).elim ?_
  intro δ hδdata
  refine ⟨δ, hδdata.1, fun i x hx hsmall => ?_⟩
  simpa only [r, E, mul_assoc] using hδdata.2 i x hx hsmall

set_option backward.isDefEq.respectTransparency true

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

local instance currentBand_parameterTopology (S : PhysicalSpacesData) :
    TopologicalSpace (Parameter S) := inferInstance

local instance currentBand_parameterAddGroup (S : PhysicalSpacesData) :
    IsTopologicalAddGroup (Parameter S) :=
  (n07aParameterGrading_withSeminorms S).isTopologicalAddGroup

local instance currentBand_parameterSMul (S : PhysicalSpacesData) :
    ContinuousSMul ℝ (Parameter S) :=
  (n07aParameterGrading_withSeminorms S).continuousSMul

set_option diagnostics true in
private theorem currentBand_sector_zero (S : PhysicalSpacesData) (base : ℕ)
    {ε : ℝ} (hε : 0 < ε) : (0 : Parameter S) ∈ sectorNeighborhood S base ε ε := by
  constructor
  · change sectorGrading S base 0 < ε
    exact (sectorGrading S base).map_zero'.trans_lt hε
  · change |(0 : ℝ)| < ε
    simpa only [abs_zero] using hε

set_option diagnostics true in
private theorem currentBand_sector_small (S : PhysicalSpacesData) (base loss : ℕ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ η ≤ 1 / 2 ∧
      ∀ z ∈ sectorNeighborhood S (max base loss) η η,
        z ∈ sectorNeighborhood S base ε ε ∧ parameterGrading S (max base loss) z < δ := by
  have hradius := currentBand_sector_radius hε hδ
  refine ⟨hradius.choose, hradius.choose_spec.1, hradius.choose_spec.2.1,
    hradius.choose_spec.2.2.1, fun z hz => ?_⟩
  exact ⟨n07a_sectorNeighborhood_mono (S := S) (le_max_left _ _) hradius.choose_spec.2.1 hz,
    (n04SourceColumns_parameter_lt hz).trans_le hradius.choose_spec.2.2.2⟩

set_option diagnostics true in
/-- The index may contain a component, side and physical point. The
radius and low base precede all of them and every later derivative order. -/
theorem n04NegativeChart_current_half_reference
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {I : Type*}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (sample : I → ℕ) (base loss : ℕ) (ε : ℝ) (hε : 0 < ε)
    (f : I → Parameter S → ℝ)
    (J : ∀ i, SmoothDirections (sectorNeighborhood S base ε ε) (f i))
    (c P B A : ℝ) (hc : 0 < c) (hB : 0 < B)
    (href : ∀ i, 0 < f i 0 ∧
      (f i 0)⁻¹ ≤ B * T.E0 (T.sample (sample i)) ^ A)
    (hfirst : ∀ i z, z ∈ sectorNeighborhood S base ε ε → ∀ v : Fin 1 → Parameter S,
      |(J i).D 1 z v| ≤ c * T.E0 (T.sample (sample i)) ^ P *
        T.H (T.sample (sample i)) ^ (3 / 4 : ℝ) *
          oneHighVariationWeight (parameterGrading S) base loss z v) :
    ∃ b : ℕ, ∃ η : ℝ, base ≤ b ∧ 0 < η ∧ η ≤ ε ∧ η ≤ 1 / 2 ∧
      ∀ i z, z ∈ sectorNeighborhood S b η η →
        f i 0 / 2 ≤ f i z ∧ 0 < f i z ∧
          (f i z)⁻¹ ≤ 2 * B * T.E0 (T.sample (sample i)) ^ A := by
  have hball := currentBand_material_ball (X := Parameter S) hD hT sample (parameterGrading S)
    (n07aParameterGrading_monotone S) base loss (sectorNeighborhood_convex S base ε ε)
    (currentBand_sector_zero S base hε) f J c P B A hc hB href hfirst
  have hsector := currentBand_sector_small S base loss hε hball.choose_spec.1
  refine ⟨max base loss, hsector.choose, le_max_left _ _,
    hsector.choose_spec.1, hsector.choose_spec.2.1, hsector.choose_spec.2.2.1, fun i z hz => ?_⟩
  have hz' := hsector.choose_spec.2.2.2 z hz
  exact hball.choose_spec.2 i z hz'.1 hz'.2

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_current_half_reference'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_current_half_reference
