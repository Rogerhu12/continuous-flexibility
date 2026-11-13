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

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

namespace N04RealizationGauge

variable (G : N04RealizationGauge)
  (η : (G.W.S.height (3 / 4 : ℝ)).Space)

theorem heightRadialDifferenceTower_bound (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m (hm : G.Neg η m) (q : unitStrip) (i j : ℕ), i + j ≤ s →
      ∀ z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε,
      ∀ v : Fin k → Parameter G.W.S,
        |(G.heightRadialDifferenceTower η m hm i j q).D k z v| ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B *
            G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) *
              oneHighVariationWeight (parameterGrading G.W.S) G.W.base
                (s + G.W.loss) z v := by
  obtain ⟨A, hA, hb⟩ := G.W.through03.1.1.sectorCoefficientTower_bound k s
  obtain ⟨B₀, P₀, hB₀, hP₀, hsample⟩ :=
    n04bActualTypedAtlas_negative_host_sample_weights G.W.hT G.W.hS
      G.W.through03 G.W.field G.X.e₀ (3 / 4 : ℝ) 0 A hA.le
  let L : ℝ := max 1 (G.W.D.b - G.W.D.a)
  have hL : 1 ≤ L := le_max_left _ _
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (L ^ s * A * B₀) P₀
  refine ⟨B, hB, ?_⟩
  intro m hm q i j hij z hz v
  let t := G.heightRadialLabel η m hm
  have ht : G.e m = .inl t := G.heightRadialLabel_spec η m hm
  have hk : G.X.e₀ (G.negativeIndex t) = .inl (t.1, t.2) :=
    G.X.e₀.apply_symm_apply _
  have hp := G.heightRadial_physicalUnitPoint_mem η m t ht q.property
  have hgeom := G.heightRadial_physicalBounds η m t ht
  let l : ℝ := (G.V η).physicalRight m - (G.V η).physicalLeft m
  have hlpos : 0 < l := sub_pos.mpr hgeom.2.1
  have hlL : l ≤ L := (by
    dsimp only [l]
    linarith only [hgeom.1, hgeom.2.2] : l ≤ G.W.D.b - G.W.D.a).trans (le_max_right _ _)
  have hpow : l ^ i ≤ L ^ s :=
    (pow_le_pow_left₀ hlpos.le hlL i).trans (pow_le_pow_right₀ hL (by omega))
  have hfields := G.negative_fields η (G.W.C.referenceState, 0) m t ht
  have hcell : (G.V η).cell m = (G.W.A G.X.e₀).cell (G.negativeIndex t) :=
    hfields.2.2.2.2.2.1
  have hs := hsample (G.negativeIndex t) t.1 t.2 hk (G.W.C.cell t.1) (G.W.host t.1)
  simp only [Real.rpow_zero, mul_one] at hs
  rw [← hcell] at hs
  let E : ℝ := G.W.U.E0 (G.W.U.sample ((G.V η).cell m))
  let H : ℝ := G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ)
  let V : ℝ := oneHighVariationWeight (parameterGrading G.W.S)
    G.W.base (s + G.W.loss) z v
  have hE : 1 ≤ E := (G.cost_nonneg η).2.2 m
  have hH : 0 ≤ H := Real.rpow_nonneg ((G.cost_nonneg η).2.1 m) _
  have hV : 0 ≤ V := oneHighVariationWeight_nonneg _ _ _ _ _
  have hEP : G.W.T.E0 (G.W.T.sample ((G.V η).cell m)) ^ P₀ ≤ E ^ P₀ :=
    Real.rpow_le_rpow (zero_le_one.trans (G.W.floor _))
      (le_enlargedMaterialData_E0 G.W.T _) hP₀
  have hsample' : G.W.T.H (G.W.T.sample (G.W.C.cell t.1)) ^ (3 / 4 : ℝ) *
      G.W.T.E0 (G.W.T.sample (G.W.C.cell t.1)) ^ A ≤ B₀ * (H * E ^ P₀) :=
    hs.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEP hH) hB₀.le)
  have hraw := hb (G.W.C.cell t.1) 0 i j (physicalUnitPoint (G.V η) m q.val)
    hij (G.W.host t.1 hp.1) z hz v
  have hraw' :
      |(G.W.through03.1.1.sectorCoefficientTower (G.W.C.cell t.1) 0 i j
        (physicalUnitPoint (G.V η) m q.val) (G.W.host t.1 hp.1)).D k z v| ≤
      A * G.W.T.H (G.W.T.sample (G.W.C.cell t.1)) ^ (3 / 4 : ℝ) *
        G.W.T.E0 (G.W.T.sample (G.W.C.cell t.1)) ^ A * V := hraw
  rw [G.heightRadialDifferenceTower_apply η m hm i j q k hz v,
    abs_mul, abs_of_nonneg (pow_nonneg hlpos.le i)]
  change l ^ i * _ ≤ B * E ^ B * H * V
  calc
    _ ≤ L ^ s * (A * G.W.T.H (G.W.T.sample (G.W.C.cell t.1)) ^ (3 / 4 : ℝ) *
        G.W.T.E0 (G.W.T.sample (G.W.C.cell t.1)) ^ A * V) :=
      mul_le_mul hpow hraw' (abs_nonneg _) (pow_nonneg (zero_le_one.trans hL) _)
    _ = (L ^ s * A) *
        (G.W.T.H (G.W.T.sample (G.W.C.cell t.1)) ^ (3 / 4 : ℝ) *
          G.W.T.E0 (G.W.T.sample (G.W.C.cell t.1)) ^ A) * V := by ring
    _ ≤ (L ^ s * A) * (B₀ * (H * E ^ P₀)) * V :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsample'
        (mul_nonneg (pow_nonneg (zero_le_one.trans hL) _) hA.le)) hV
    _ = ((L ^ s * A * B₀) * E ^ P₀) * H * V := by ring
    _ ≤ B * E ^ B * H * V :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hpack E hE) hH) hV

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
  · obtain ⟨A, hA, hb⟩ := G.heightRadialDifferenceTower_bound η 1 s
    obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (3 * A) A
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
      simp only [G.physicalRadialFamily_zero, sub_self, mixedDerivative_fun_zero]
    have hvalue := n04NegativeGeometry_sector_difference_bound
      (G.heightRadialDifferenceTower η m hm i j q) G.W.ε_pos hδle hδhalf
      (by omega : G.W.base ≤ s + (G.W.base + G.W.loss)) hzero hM hfirst hz
    have hweight : 0 ≤ parameterGrading G.W.S (s + (G.W.base + G.W.loss)) z :=
      apply_nonneg _ _
    calc
      _ ≤ (3 * M) * parameterGrading G.W.S (s + (G.W.base + G.W.loss)) z := hvalue
      _ = ((3 * A) * E ^ A) * H *
          parameterGrading G.W.S (s + (G.W.base + G.W.loss)) z := by dsimp only [M]; ring
      _ ≤ B * E ^ B * H * parameterGrading G.W.S (s + (G.W.base + G.W.loss)) z :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hpack E hE) hH) hweight
  · obtain ⟨B, hB, hb⟩ := G.heightRadialDifferenceTower_bound η k s
    exact ⟨B, hB, fun z hz v m hm q i j hij => hb m hm q i j hij z (hsub hz) v⟩

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negative_physicalRadial_currentData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negative_physicalRadial_currentData
