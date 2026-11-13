import ContinuousFlexibility.Analysis.N04NegativeHeightRadialFamilies
import ContinuousFlexibility.Analysis.N04NegativeGeometryFlowBounds
import ContinuousFlexibility.Analysis.ActualNegativeHostMaterialSamples

/-!
# Sharp current jets of the physical radial coefficient

The N01 coefficient tower keeps its sampled height factor. The host-cell
comparison moves that same factor to the retained half sample, and the
fixed radial rescaling costs only a power of the bounded annular length.
Integrating the first parameter derivative gives the reference-difference
value estimate, on one neighborhood fixed before all derivative orders
and before the auxiliary column.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

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

private theorem heightRadial_envelope_scale
    {x l L A H₀ E₀ B₀ H E P B V : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hH : 0 ≤ H) (hV : 0 ≤ V)
    (hl : l ≤ L) (hraw : |x| ≤ A * H₀ * E₀ * V)
    (hsample : H₀ * E₀ ≤ B₀ * (H * E ^ P))
    (hpack : (L * A * B₀) * E ^ P ≤ B * E ^ B) :
    l * |x| ≤ B * E ^ B * H * V := by
  calc
    _ ≤ L * (A * H₀ * E₀ * V) := mul_le_mul hl hraw (abs_nonneg x) hL
    _ = (L * A) * (H₀ * E₀) * V := by ring
    _ ≤ (L * A) * (B₀ * (H * E ^ P)) * V :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsample (mul_nonneg hL hA)) hV
    _ = ((L * A * B₀) * E ^ P) * H * V := by ring
    _ ≤ B * E ^ B * H * V :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpack hH) hV

private theorem heightRadial_value_reorder (A E H V : ℝ) :
    (3 * (A * E ^ A * H)) * V = ((3 * A) * E ^ A) * H * V := by ring

private theorem heightRadial_abs_scale {x c y : ℝ} (hc : 0 ≤ c) (he : x = c * y) :
    |x| = c * |y| :=
  (congrArg abs he).trans ((abs_mul c y).trans
    (congrArg (fun r : ℝ => r * |y|) (abs_of_nonneg hc)))

private theorem heightRadial_drop_zero_material {H₀ M₀ E₀ H M E A P B : ℝ}
    (h : H₀ * M₀ ^ (0 : ℝ) * E₀ ^ A ≤ B * (H * M ^ (0 : ℝ) * E ^ P)) :
    H₀ * E₀ ^ A ≤ B * (H * E ^ P) := by
  simpa only [Real.rpow_zero, mul_one] using h

namespace N04RealizationGauge

attribute [local irreducible] heightRadialDifferenceTower N01Properties.sectorCoefficientTower

variable (G : N04RealizationGauge)
  (η : (G.W.S.height (3 / 4 : ℝ)).Space)

/-- Move the coefficient-height envelope to the retained half sample
before introducing any parameter derivative tower. -/
private theorem heightRadial_sample_envelope (A : ℝ) (hA : 0 ≤ A) :
    ∃ B P : ℝ, 0 < B ∧ 0 ≤ P ∧ ∀ m (hm : G.Neg η m),
      G.W.T.H (G.W.T.sample (G.W.C.cell (G.heightRadialLabel η m hm).1)) ^ (3 / 4 : ℝ) *
        G.W.T.E0 (G.W.T.sample (G.W.C.cell (G.heightRadialLabel η m hm).1)) ^ A ≤
      B * (G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) *
        G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ P) := by
  have hweights := n04bActualTypedAtlas_negative_host_sample_weights G.W.hT G.W.hS
    G.W.through03 G.W.field G.X.e₀ (3 / 4 : ℝ) 0 A hA
  let B : ℝ := hweights.choose
  let P : ℝ := hweights.choose_spec.choose
  have hB : 0 < B := hweights.choose_spec.choose_spec.1
  have hP : 0 ≤ P := hweights.choose_spec.choose_spec.2.1
  refine ⟨B, P, hB, hP, ?_⟩
  intro m hm
  let t := G.heightRadialLabel η m hm
  have ht : G.e m = .inl t := G.heightRadialLabel_spec η m hm
  have hk : G.X.e₀ (G.negativeIndex t) = .inl (t.1, t.2) :=
    G.X.e₀.apply_symm_apply _
  have hfields := G.negative_fields η (G.W.C.referenceState, 0) m t ht
  have hcell : (G.V η).cell m = (G.W.A G.X.e₀).cell (G.negativeIndex t) :=
    hfields.2.2.2.2.2.1
  have hs := heightRadial_drop_zero_material (hweights.choose_spec.choose_spec.2.2
    (G.negativeIndex t) t.1 t.2 hk (G.W.C.cell t.1) (G.W.host t.1))
  rw [← hcell] at hs
  change G.W.T.H (G.W.T.sample (G.W.C.cell t.1)) ^ (3 / 4 : ℝ) *
      G.W.T.E0 (G.W.T.sample (G.W.C.cell t.1)) ^ A ≤
    B * (G.W.T.H (G.W.T.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) *
      G.W.U.E0 (G.W.T.sample ((G.V η).cell m)) ^ P)
  have hH : 0 ≤ G.W.T.H (G.W.T.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg
      (G.W.hT.2.1 _ (materialSample_mem_interval G.W.radial.1 G.W.hT _)).2.1.le _
  have hEP : G.W.T.E0 (G.W.T.sample ((G.V η).cell m)) ^ P ≤
      G.W.U.E0 (G.W.T.sample ((G.V η).cell m)) ^ P :=
    Real.rpow_le_rpow (zero_le_one.trans (G.W.floor _))
      (le_enlargedMaterialData_E0 G.W.T _) hP
  exact hs.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hEP hH) hB.le)

private theorem heightRadial_physicalLength_power_bound
    (m : ℕ) (hm : G.Neg η m) (i s : ℕ) (his : i ≤ s) :
    0 < (G.V η).physicalRight m - (G.V η).physicalLeft m ∧
      ((G.V η).physicalRight m - (G.V η).physicalLeft m) ^ i ≤
        (max 1 (G.W.D.b - G.W.D.a)) ^ s := by
  let t := G.heightRadialLabel η m hm
  have hgeom := G.heightRadial_physicalBounds η m t
    (G.heightRadialLabel_spec η m hm)
  have hlpos := sub_pos.mpr hgeom.2.1
  have hlength : (G.V η).physicalRight m - (G.V η).physicalLeft m ≤
      max 1 (G.W.D.b - G.W.D.a) := by
    have houter : (G.V η).physicalRight m - (G.V η).physicalLeft m ≤
        G.W.D.b - G.W.D.a := by
      linarith only [hgeom.1, hgeom.2.2]
    exact houter.trans (le_max_right _ _)
  exact ⟨hlpos, (pow_le_pow_left₀ hlpos.le hlength i).trans
    (pow_le_pow_right₀ (le_max_left _ _) his)⟩

theorem heightRadialDifferenceTower_bound (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m (hm : G.Neg η m) (q : unitStrip) (i j : ℕ), i + j ≤ s →
      ∀ z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε,
      ∀ v : Fin k → Parameter G.W.S,
        |(G.heightRadialDifferenceTower η m hm i j q).D k z v| ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B *
            G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) *
              oneHighVariationWeight (parameterGrading G.W.S) G.W.base
                (s + G.W.loss) z v := by
  have hcoeff := G.W.through03.1.1.sectorCoefficientTower_bound k s
  let A : ℝ := hcoeff.choose
  have hA : 0 < A := hcoeff.choose_spec.1
  have hb := hcoeff.choose_spec.2
  have hweights := G.heightRadial_sample_envelope η A hA.le
  let B₀ : ℝ := hweights.choose
  let P₀ : ℝ := hweights.choose_spec.choose
  have hsample := hweights.choose_spec.choose_spec.2.2
  let L : ℝ := max 1 (G.W.D.b - G.W.D.a)
  have hL : 1 ≤ L := le_max_left _ _
  have hpacked := coefficientEnvelope_pack (L ^ s * A * B₀) P₀
  let B : ℝ := hpacked.choose
  have hB : 0 < B := hpacked.choose_spec.1
  have hpack := hpacked.choose_spec.2
  refine ⟨B, hB, ?_⟩
  intro m hm q i j hij z hz v
  let t := G.heightRadialLabel η m hm
  have ht : G.e m = .inl t := G.heightRadialLabel_spec η m hm
  have hp := G.heightRadial_physicalUnitPoint_mem η m t ht q.property
  let l : ℝ := (G.V η).physicalRight m - (G.V η).physicalLeft m
  have hlength := G.heightRadial_physicalLength_power_bound η m hm i s (by omega)
  have hlpos : 0 < l := hlength.1
  have hpow : l ^ i ≤ L ^ s := hlength.2
  let E : ℝ := G.W.U.E0 (G.W.U.sample ((G.V η).cell m))
  let H : ℝ := G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ)
  let V : ℝ := oneHighVariationWeight (parameterGrading G.W.S)
    G.W.base (s + G.W.loss) z v
  have hE : 1 ≤ E := (G.cost_nonneg η).2.2 m
  have hH : 0 ≤ H := Real.rpow_nonneg ((G.cost_nonneg η).2.1 m) _
  have hV : 0 ≤ V := oneHighVariationWeight_nonneg _ _ _ _ _
  have hsample' : G.W.T.H (G.W.T.sample (G.W.C.cell t.1)) ^ (3 / 4 : ℝ) *
      G.W.T.E0 (G.W.T.sample (G.W.C.cell t.1)) ^ A ≤ B₀ * (H * E ^ P₀) :=
    hsample m hm
  have hraw := hb (G.W.C.cell t.1) 0 i j (physicalUnitPoint (G.V η) m q.val)
    hij (G.W.host t.1 hp.1) z hz v
  have hraw' :
      |(G.W.through03.1.1.sectorCoefficientTower (G.W.C.cell t.1) 0 i j
        (physicalUnitPoint (G.V η) m q.val) (G.W.host t.1 hp.1)).D k z v| ≤
      A * G.W.T.H (G.W.T.sample (G.W.C.cell t.1)) ^ (3 / 4 : ℝ) *
        G.W.T.E0 (G.W.T.sample (G.W.C.cell t.1)) ^ A * V := hraw
  have hscaled := heightRadial_abs_scale (pow_nonneg hlpos.le i)
    (G.heightRadialDifferenceTower_apply η m hm i j q k hz v)
  exact hscaled.trans_le (heightRadial_envelope_scale hA.le
    (pow_nonneg (zero_le_one.trans hL) s) hH hV hpow hraw' hsample' (hpack E hE))

/-- One neighborhood works for all current radial-coefficient jets and
for every auxiliary-column replacement. -/
theorem negative_physicalRadial_currentData :
    G.Data η (G.Neg η) G.W.base (min G.W.ε (1 / 2))
      (G.physicalRadialFamily η) (G.physicalRadialRef η) := by
  let δ : ℝ := min G.W.ε (1 / 2)
  have hδ : 0 < δ := lt_min G.W.ε_pos (by norm_num)
  have hδle : δ ≤ G.W.ε := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hsub : sectorNeighborhood G.W.S G.W.base δ δ ⊆
      sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε :=
    sectorNeighborhood_mono G.W.S le_rfl hδle hδle
  let J : ∀ m, G.Neg η m → ∀ (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood G.W.S G.W.base δ δ)
        (fun z => mixedDerivative i j
          (fun y => G.physicalRadialFamily η z m y - G.physicalRadialRef η m y) q.val) :=
    fun m hm i j q => (G.heightRadialDifferenceTower η m hm i j q).restrict
      (sectorNeighborhood_isOpen G.W.S G.W.base δ δ) hsub
  refine ⟨fun z hz m hm => G.physicalRadial_spatial η z (hsub hz) m hm,
    J, ⟨G.W.base + G.W.loss, fun s => ?_⟩, fun k => ⟨G.W.loss, fun s => ?_⟩⟩
  · have hfirstBound := G.heightRadialDifferenceTower_bound η 1 s
    let A : ℝ := hfirstBound.choose
    have hA : 0 < A := hfirstBound.choose_spec.1
    have hb := hfirstBound.choose_spec.2
    have hpacked := coefficientEnvelope_pack (3 * A) A
    let B : ℝ := hpacked.choose
    have hB : 0 < B := hpacked.choose_spec.1
    have hpack := hpacked.choose_spec.2
    refine ⟨B, hB, ?_⟩
    intro z hz m hm q i j hij
    let E : ℝ := G.W.U.E0 (G.W.U.sample ((G.V η).cell m))
    let H : ℝ := G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ)
    let M : ℝ := A * E ^ A * H
    have hE : 1 ≤ E := (G.cost_nonneg η).2.2 m
    have hH : 0 ≤ H := Real.rpow_nonneg ((G.cost_nonneg η).2.1 m) _
    have hM : 0 ≤ M := mul_nonneg
      (mul_nonneg hA.le (Real.rpow_nonneg (zero_le_one.trans hE) _)) hH
    have hhigh : s + G.W.loss ≤ s + (G.W.base + G.W.loss) := by omega
    have hfirst : ∀ y ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε,
        ∀ v : Fin 1 → Parameter G.W.S,
        |(G.heightRadialDifferenceTower η m hm i j q).D 1 y v| ≤
          M * oneHighVariationWeight (parameterGrading G.W.S)
            G.W.base (s + (G.W.base + G.W.loss)) y v := by
      intro y hy v
      exact (hb m hm q i j hij y hy v).trans
        (mul_le_mul_of_nonneg_left
          (oneHighVariationWeight_mono (sectorPairGrading_monotone G.W.S)
            le_rfl hhigh y v) hM)
    have hzero : mixedDerivative i j
        (fun y => G.physicalRadialFamily η 0 m y - G.physicalRadialRef η m y) q.val = 0 := by
      have he := congrArg
        (fun F : PolarPoint → ℝ => mixedDerivative i j
          (fun y => F y - G.physicalRadialRef η m y) q.val)
        (G.physicalRadialFamily_zero η m)
      exact he.trans (by simp only [sub_self, mixedDerivative_fun_zero])
    have hvalue := n04NegativeGeometry_sector_difference_bound
      (G.heightRadialDifferenceTower η m hm i j q) G.W.ε_pos hδle hδhalf
      (by omega : G.W.base ≤ s + (G.W.base + G.W.loss)) hzero hM hfirst hz
    have hweight : 0 ≤ parameterGrading G.W.S (s + (G.W.base + G.W.loss)) z :=
      apply_nonneg _ _
    calc
      _ ≤ (3 * M) * parameterGrading G.W.S (s + (G.W.base + G.W.loss)) z := hvalue
      _ = ((3 * A) * E ^ A) * H *
          parameterGrading G.W.S (s + (G.W.base + G.W.loss)) z :=
        heightRadial_value_reorder A E H _
      _ ≤ B * E ^ B * H * parameterGrading G.W.S (s + (G.W.base + G.W.loss)) z :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hpack E hE) hH) hweight
  · have hbound := G.heightRadialDifferenceTower_bound η k s
    exact ⟨hbound.choose, hbound.choose_spec.1, fun z hz v m hm q i j hij =>
      hbound.choose_spec.2 m hm q i j hij z (hsub hz) v⟩

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negative_physicalRadial_currentData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negative_physicalRadial_currentData
