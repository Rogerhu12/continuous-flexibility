import ContinuousFlexibility.Analysis.N04PulledFieldsReferenceCost
import ContinuousFlexibility.Analysis.N04RealizationMixedJointDirections
import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization

/-!
# The genuine inverse-point joint tower

The geometry interface differentiates differences from the reference.
Adding the same reference mixed jet gives the raw mixed tower.  The
reference certificate and the difference estimates then supply the
uniform seminorm bounds needed to join both spatial variables.

The resulting point is exactly `G.pulledPoint`; no inverse, coordinate,
or parameter-space representation is reselected.  This module provides
joint regularity, not an estimate for a composed physical coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

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

/-- Add the fixed reference mixed jet to the actual difference tower. -/
def n04PulledFields_currentData_rawMixedRegularity
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hdata : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hreg : ∀ m, ContDiffOn ℝ ∞ (f₀ m) unitStrip) (m : ℕ) :
    MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip (fun z => f z m) := by
  letI : IsTopologicalAddGroup (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).continuousSMul
  have hU := isOpen_sectorNeighborhood S base ε ε
  refine { spatial := fun z hz => (hdata.1 z hz m trivial).1, parameter := ?_ }
  intro i j q hq
  exact (smoothDirectionsAdd (hdata.2.choose m i j ⟨q, hq⟩)
    (smoothDirections_constant hU (mixedDerivative i j (f₀ m) q))).congr
    (fun z hz => by
      rw [mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ)
        (hdata.1 z hz m trivial).1 (hreg m) i j hq, sub_add_cancel])

private theorem n04PulledFieldsInverseJoint_zero_cost
    {A H u v : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H) (huv : u ≤ v) (hv : 0 ≤ v) :
    A * (1 + H * u) ≤ (A * (1 + H)) * (1 + v) := by
  have hh : 1 + H * u ≤ (1 + H) * (1 + v) := by
    nlinarith [mul_le_mul_of_nonneg_left huv hH]
  exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)

section AbstractUniformBounds

variable {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

private theorem n04PulledFieldsInverseJoint_zero_uniform
    {U : Set X} {f : ι → X → ℝ} (J : ∀ i, SmoothDirections U (f i))
    (p : Seminorm ℝ X) (hp : Continuous p)
    {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hb : ∀ i x, x ∈ U → |f i x| ≤ A * (1 + H * p x)) :
    ∃ q : Seminorm ℝ X, ∃ B : ℝ, Continuous q ∧ 0 ≤ B ∧
      ∀ i x, x ∈ U → ∀ v : Fin 0 → X,
        |(J i).D 0 x v| ≤ B * (1 + q x) * ∏ j, q (v j) := by
  refine ⟨p, A * (1 + H), hp, mul_nonneg hA (add_nonneg zero_le_one hH), ?_⟩
  intro i x hx v
  have he := smoothDirections_D_zero_apply (J i) hx v
  have hbound := (hb i x hx).trans
    (n04PulledFieldsInverseJoint_zero_cost hA hH le_rfl (apply_nonneg p x))
  calc
    |(J i).D 0 x v| = |f i x| := congrArg abs he
    _ ≤ (A * (1 + H)) * (1 + p x) := hbound
    _ = (A * (1 + H)) * (1 + p x) * ∏ j : Fin 0, p (v j) := by
      simp only [Fin.prod_univ_zero, mul_one]

private theorem n04PulledFieldsInverseJoint_positive_uniform
    {U : Set X} {f : ι → X → ℝ} {c : ι → ℝ}
    (J : ∀ i, SmoothDirections U (f i))
    (K : ∀ i, SmoothDirections U (fun x => f i x - c i))
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hcp : ∀ n, Continuous (p n))
    (base high : ℕ) {k : ℕ} (hk : 0 < k) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ i x, x ∈ U → ∀ v : Fin k → X,
      |(K i).D k x v| ≤ M * oneHighVariationWeight p base high x v) :
    ∃ q : Seminorm ℝ X, ∃ B : ℝ, Continuous q ∧ 0 ≤ B ∧
      ∀ i x, x ∈ U → ∀ v : Fin k → X,
        |(J i).D k x v| ≤ B * (1 + q x) * ∏ j, q (v j) := by
  let q : Seminorm ℝ X := p (max base high)
  refine ⟨q, M * ((k : ℝ) + 1), hcp _,
    mul_nonneg hM (add_nonneg (Nat.cast_nonneg _) zero_le_one), ?_⟩
  intro i x hx v
  have he := smoothDirections_D_sub_constant (J i) (K i) hk hx v
  have hw := oneHighVariationWeight_le_seminorm_product p q base high
    (hp (le_max_left _ _)) (hp (le_max_right _ _)) x v
  calc
    |(J i).D k x v| = |(K i).D k x v| := congrArg abs he.symm
    _ ≤ M * oneHighVariationWeight p base high x v := hb i x hx v
    _ ≤ M * (((k : ℝ) + 1) * (1 + q x) * ∏ j, q (v j)) :=
      mul_le_mul_of_nonneg_left hw hM
    _ = (M * ((k : ℝ) + 1)) * (1 + q x) * ∏ j, q (v j) := by ring

end AbstractUniformBounds

private theorem n04PulledFieldsInverseJoint_raw_zero_uniform
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hdata : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hreg : ∀ m, ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, ∀ (q : unitStrip) (i j : ℕ),
      i + j ≤ s → |mixedDerivative i j (f₀ m) q.val| ≤
        B * T.E0 (T.sample (cell m)) ^ B)
    (m a b : ℕ)
    (RF : MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip (fun z => f z m)) :
    ∃ p : Seminorm ℝ (Parameter S), ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
      ∀ q : unitStrip, ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin 0 → Parameter S,
        |(RF.parameter a b q.val q.property).D 0 z v| ≤
          B * (1 + p z) * ∏ i, p (v i) := by
  letI : IsTopologicalAddGroup (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).continuousSMul
  have hcp : ∀ n, Continuous (parameterGrading S n) :=
    (n07aParameterGrading_withSeminorms S).continuous_seminorm
  have hv := n04PulledFields_currentData_rawSpatial hdata hE hH
    (fun n _ => hreg n)
    (fun s => ⟨(href s).choose, (href s).choose_spec.1,
      fun n _ q i j hij => (href s).choose_spec.2 n q i j hij⟩)
  have hs := hv.choose_spec (a + b)
  let high : ℕ := a + b + hv.choose
  let A : ℝ := hs.choose * T.E0 (T.sample (cell m)) ^ hs.choose
  let H : ℝ := T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)
  have hA : 0 ≤ A := mul_nonneg hs.choose_spec.1.le
    (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)
  have hH' : 0 ≤ H := Real.rpow_nonneg (hH m) _
  exact n04PulledFieldsInverseJoint_zero_uniform
    (fun q : unitStrip => RF.parameter a b q.val q.property)
    (parameterGrading S high) (hcp high) hA hH'
    (fun q z hz => hs.choose_spec.2 z hz m trivial q a b le_rfl)

private theorem n04PulledFieldsInverseJoint_raw_positive_uniform
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hdata : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hreg : ∀ m, ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (m a b : ℕ)
    (RF : MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip (fun z => f z m))
    (k : ℕ) (hk : 0 < k) :
    ∃ p : Seminorm ℝ (Parameter S), ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
      ∀ q : unitStrip, ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        |(RF.parameter a b q.val q.property).D k z v| ≤
          B * (1 + p z) * ∏ i, p (v i) := by
  letI : IsTopologicalAddGroup (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).continuousSMul
  have hp : Monotone (parameterGrading S) :=
    tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)
  have hcp : ∀ n, Continuous (parameterGrading S n) :=
    (n07aParameterGrading_withSeminorms S).continuous_seminorm
  have hd := hdata.2.choose_spec.2 k
  have hs := hd.choose_spec (a + b)
  let M : ℝ := hs.choose * T.E0 (T.sample (cell m)) ^ hs.choose *
    T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg hs.choose_spec.1.le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _))
    (Real.rpow_nonneg (hH m) _)
  let JD (q : unitStrip) : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => mixedDerivative a b (f z m) q.val - mixedDerivative a b (f₀ m) q.val) :=
    (hdata.2.choose m a b q).congr (fun y hy =>
      mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ)
        (hdata.1 y hy m trivial).1 (hreg m) a b q.property)
  exact n04PulledFieldsInverseJoint_positive_uniform
    (fun q : unitStrip => RF.parameter a b q.val q.property) JD
    (parameterGrading S) hp hcp base (a + b + hd.choose) hk hM
    (fun q z hz v => hs.choose_spec.2 z hz v m trivial q a b le_rfl)

/-- At a fixed piece the actual raw mixed towers have uniform seminorm
bounds over the entire unit strip.  Positive parameter orders use only
the difference estimate; order zero also uses the reference estimate. -/
theorem n04PulledFields_currentData_rawMixed_uniform
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hdata : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hreg : ∀ m, ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, ∀ (q : unitStrip) (i j : ℕ),
      i + j ≤ s → |mixedDerivative i j (f₀ m) q.val| ≤
        B * T.E0 (T.sample (cell m)) ^ B)
    (m a b : ℕ)
    (RF : MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip (fun z => f z m)) :
    UniformScalarJetSeminormBounds
      (fun q : unitStrip => RF.parameter a b q.val q.property) := by
  intro k
  by_cases hk : k = 0
  · subst k
    exact n04PulledFieldsInverseJoint_raw_zero_uniform hdata hE hH hreg href m a b RF
  · exact n04PulledFieldsInverseJoint_raw_positive_uniform hdata hE hH hreg m a b RF k
      (Nat.pos_of_ne_zero hk)

/-- Join the two spatial coordinates using the raw mixed towers and
their per-piece uniform seminorm estimates. -/
def n04PulledFields_currentData_jointDirections
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hdata : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hreg : ∀ m, ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, ∀ (q : unitStrip) (i j : ℕ),
      i + j ≤ s → |mixedDerivative i j (f₀ m) q.val| ≤
        B * T.E0 (T.sample (cell m)) ^ B)
    (m : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ unitStrip)
      (fun z : Parameter S × PolarPoint => f z.1 m z.2) := by
  letI : IsTopologicalAddGroup (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).continuousSMul
  let RF := n04PulledFields_currentData_rawMixedRegularity hdata hreg m
  exact n04Realization_mixedJointDirections RF
    (isOpen_sectorNeighborhood S base ε ε) (sectorNeighborhood_convex S base ε ε)
    isOpen_Ioo (convex_Ioo (0 : ℝ) 1)
    (fun a b => n04PulledFields_currentData_rawMixed_uniform hdata hE hH hreg href m a b RF)

/-- The actual geometry atom is jointly smooth on the original state
neighborhood and canonical unit strip. -/
def n04PulledFields_geometryAtom_jointDirections
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ}
    (hgeo : G.GeometryData η (fun _ => True) base ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (a : Atom) (ha : atomIsGeometry a) (m : ℕ) :
    SmoothDirections (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip)
      (fun z : Parameter (G.S η) × PolarPoint => G.atomFamily η a z.1 m z.2) :=
  n04PulledFields_currentData_jointDirections (hgeo.1 a ha)
    (G.cost_nonneg η).2.2 (G.cost_nonneg η).2.1 (fun n => (href.1 n a).1)
    (fun s => ⟨(href.2 s).choose, (href.2 s).choose_spec.1,
      fun n q i j hij => (href.2 s).choose_spec.2 n a q.val q.property i j hij⟩) m

/-- Undo exactly the normalization in the two inverse-chart atoms. -/
theorem n04PulledFields_pulledPoint_eq_inverseAtoms
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (m : ℕ) (hlen : (G.V η).physicalRight m - (G.V η).physicalLeft m ≠ 0)
    (z : Parameter (G.S η)) (y : PolarPoint) :
    G.pulledPoint η (G.lift η z) m y =
      ((G.V η).physicalLeft m +
        ((G.V η).physicalRight m - (G.V η).physicalLeft m) *
          G.atomFamily η .inverseRadial z m y,
        y.2 + G.atomFamily η .inverseAngleDefect z m y) := by
  apply Prod.ext
  · change ((G.V η).inverseChart (G.lift η z) m (canonicalUnitPoint (G.V η) m y)).1 =
      (G.V η).physicalLeft m +
        ((G.V η).physicalRight m - (G.V η).physicalLeft m) *
          ((((G.V η).inverseChart (G.lift η z) m
              (canonicalUnitPoint (G.V η) m y)).1 - (G.V η).physicalLeft m) /
            ((G.V η).physicalRight m - (G.V η).physicalLeft m))
    field_simp [hlen]
    ring
  · change ((G.V η).inverseChart (G.lift η z) m (canonicalUnitPoint (G.V η) m y)).2 =
      y.2 + (((G.V η).inverseChart (G.lift η z) m
        (canonicalUnitPoint (G.V η) m y)).2 - y.2)
    ring

/-- The joint tower of the same pulled inverse point, recovered from
its two geometry atoms.  Only nonzero physical length is needed for
this affine reconstruction. -/
def n04PulledFields_inversePoint_jointDirections
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ}
    (hgeo : G.GeometryData η (fun _ => True) base ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (m : ℕ) (hlen : (G.V η).physicalRight m - (G.V η).physicalLeft m ≠ 0) :
    SmoothDirections (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip)
      (fun z : Parameter (G.S η) × PolarPoint => G.pulledPoint η (G.lift η z.1) m z.2) := by
  letI : IsTopologicalAddGroup (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).continuousSMul
  have hopen : IsOpen (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip) :=
    (isOpen_sectorNeighborhood (G.S η) base ε ε).prod (isOpen_Ioo.prod isOpen_univ)
  let JR := n04PulledFields_geometryAtom_jointDirections G η hgeo href
    .inverseRadial trivial m
  let JT := n04PulledFields_geometryAtom_jointDirections G η hgeo href
    .inverseAngleDefect trivial m
  let A : (Parameter (G.S η) × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ (Parameter (G.S η)) PolarPoint)
  let JA : SmoothDirections (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip)
      (fun z : Parameter (G.S η) × PolarPoint => z.2.2) :=
    ((smoothDirectionsLinear A).restrict hopen (subset_univ _)).congr
    (fun z _ => by simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd'])
  let Jrad := smoothDirectionsAdd (smoothDirections_constant hopen ((G.V η).physicalLeft m))
    (smoothDirections_realMul
      (smoothDirections_constant hopen ((G.V η).physicalRight m - (G.V η).physicalLeft m)) JR)
  let Jangle := smoothDirectionsAdd JA JT
  exact (smoothDirectionsUniformProd Jrad Jangle).congr
    (fun z _ => (n04PulledFields_pulledPoint_eq_inverseAtoms G η m hlen z.1 z.2).symm)

/-- The supplied admissible family gives geometry for the same atlas,
including after replacement of its auxiliary column. -/
theorem n04PulledFields_admissible_geometry
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε) :
    CanonicalGeometry G.W.D (G.S η) (G.C η) (G.V η) base ε := by
  have hm := hadm.2.2.2.2.2
  let B := hm.choose
  let lower := hm.choose_spec.choose
  let upper := hm.choose_spec.choose_spec.choose
  have hN : G.N = B.region := hm.choose_spec.choose_spec.choose_spec.1
  have hg := n04Realization_gaugeAtlas_of_family G.W.hT G.W.hS G.W.through03
    G.W.field G.X.e₀ G.e G.X.cell G.X.src B G.Y G.H hadm.2.2.2.1
    G.τ G.σ G.Q lower upper hadm.1 hadm.2.1 hadm.2.2.1
    hm.choose_spec.choose_spec.choose_spec.2 hadm.2.2.2.2.1
  have hV : CanonicalGeometry G.W.D G.W.S G.W.C
      (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N) base ε := by
    rw [hN]
    exact hg.1
  exact canonicalGeometry_replaceAuxiliaryColumn hV η

/-- The physical length needed for inverse-atom reconstruction is
strictly positive for every piece of the admissible atlas. -/
theorem n04PulledFields_admissible_physicalLength_pos
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε) (m : ℕ) :
    0 < (G.V η).physicalRight m - (G.V η).physicalLeft m :=
  sub_pos.mpr ((n04PulledFields_admissible_geometry G η hadm).referenceBounds m).1

/-- The same inverse point lies in the physical annulus throughout
the whole product neighborhood. -/
theorem n04PulledFields_pulledPoint_mapsTo
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε) (m : ℕ) :
    MapsTo
      (fun z : Parameter (G.S η) × PolarPoint => G.pulledPoint η (G.lift η z.1) m z.2)
      (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip) (annularOpen G.W.D) := by
  have hg := n04PulledFields_admissible_geometry G η hadm
  intro z hz
  have hzstate : G.lift η z.1 ∈ stateNeighborhood (G.S η) (G.C η) base ε :=
    liftSectorParameter_mem_stateNeighborhood (C := G.C η) hz.1 le_rfl
  have hs : stateSector (G.S η) (G.lift η z.1).1 :=
    G.W.through03.1.1.2.2.1.liftSectorParameter_sector z.1
  have hlen := (hg.referenceBounds m).2.1
  have hp : canonicalUnitPoint (G.V η) m z.2 ∈ canonicalOpen (G.S η) (G.V η) m := by
    have hl := mul_pos (sub_pos.mpr hlen) hz.2.1.1
    have hu := mul_lt_of_lt_one_right (sub_pos.mpr hlen) hz.2.1.2
    refine ⟨?_, mem_univ _⟩
    dsimp only [canonicalUnitPoint]
    constructor <;> linarith
  exact (hg.domains _ hzstate hs m).2.2.1 ((hg.charts _ hzstate hs m).2.1 hp)

/-- Joint regularity of the actual inverse point from the supplied
admissible family, current geometry data and same-atlas reference jets. -/
def n04PulledFields_admissible_inversePoint_jointDirections
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    (hgeo : G.GeometryData η (fun _ => True) base ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (m : ℕ) :
    SmoothDirections (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip)
      (fun z : Parameter (G.S η) × PolarPoint => G.pulledPoint η (G.lift η z.1) m z.2) :=
  n04PulledFields_inversePoint_jointDirections G η hgeo href m
    (n04PulledFields_admissible_physicalLength_pos G η hadm m).ne'

end ContinuousFlexibility.Analysis
