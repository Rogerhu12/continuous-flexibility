import ContinuousFlexibility.Analysis.N04NegativeGeometryAuxiliary
import ContinuousFlexibility.Analysis.N04NegativeGeometryReductions
import ContinuousFlexibility.Analysis.N04RealizationLeadNegativeSplit
import ContinuousFlexibility.Analysis.WholeReferenceGaugeNegativeGeometryJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeNegativeReferenceRegularity
import ContinuousFlexibility.Analysis.WholeReferenceGaugeLengthReferenceJets
import ContinuousFlexibility.Analysis.N07aInverseChartDisplacement

/-!
# Reference costs and uniform smallness for negative inversion

All reference estimates concern the retained actual typed atlas.  Their
constants precede the auxiliary column, the selected negative piece and
the spatial point.  The eight geometry atoms and the four static length
atoms are collected in one interface.

The small-neighborhood lemma uses the positive sampled height power to
absorb a coefficient envelope only when choosing a neighborhood.  It
does not replace an E0 polynomial in a final current-jet estimate by a
subpower bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

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

/-- Reference inputs used by negative inversion: the geometry atoms and
the four fixed physical/canonical length factors. -/
def atomIsNegativeInverseReference (a : Atom) : Prop :=
  atomIsGeometry a ∨ ∃ canonical inverse : Bool,
    a = canonicalLengthSelector canonical inverse

theorem atomIsNegativeInverseReference_ne_auxiliary
    {a : Atom} (ha : atomIsNegativeInverseReference a) : a ≠ .auxiliaryColumn := by
  rcases ha with ha | ⟨canonical, inverse, rfl⟩
  · cases a <;> simp_all [atomIsGeometry]
  · cases canonical <;> cases inverse <;> simp [canonicalLengthSelector]

private theorem negativeInverse_geometry_reference_cases
    (a : Atom) (ha : atomIsGeometry a) :
    a = .chartRadial ∨ a = .chartAngleDefect ∨ a = .inverseRadial ∨
      a = .inverseAngleDefect ∨ a = .height ∨ a = .heightInverse ∨
      a = .jacobian ∨ a = .jacobianInverse ∨ a = .sourceFactor ∨ a = .sourceFactorInverse := by
  cases a <;> simp_all [atomIsGeometry]

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem inverseReference_atomRef_unreplaced
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (a : Atom)
    (ha : a ≠ .auxiliaryColumn) :
    G.atomRef η a m =
      atom G.W.D G.W.U G.W.S G.W.C G.W.L
        (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N)
        (G.W.C.referenceState, 0) m a :=
  canonicalAtom_replaceAuxiliaryColumn_of_ne G.W.D G.W.U G.W.S G.W.C G.W.L
    (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N)
    η (G.W.C.referenceState, 0) m a ha

/-- The supplied gauge may have arbitrary positive fields: negative
reference geometry is fixed by the original typed atlas. -/
theorem negativeInverse_reference_geometry_regular
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m)
    (a : Atom) (ha : atomIsGeometry a) :
    ContDiffOn ℝ ∞ (G.atomRef η a m) unitStrip ∧
      ∀ p ∈ unitStrip, G.atomRef η a m (p + (0, Real.pi)) = G.atomRef η a m p := by
  have hne : a ≠ .auxiliaryColumn :=
    atomIsNegativeInverseReference_ne_auxiliary (Or.inl ha)
  have hE : a ≠ .ratioE0 := by cases a <;> simp [atomIsGeometry] at ha ⊢
  have hEi : a ≠ .ratioE0Inverse := by cases a <;> simp [atomIsGeometry] at ha ⊢
  rw [G.inverseReference_atomRef_unreplaced η m a hne,
    canonicalAtom_enlargedMaterialData_of_ne_ratios G.W.D G.W.T G.W.S G.W.C G.W.L
      (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N)
      (G.W.C.referenceState, 0) m a hE hEi]
  apply n04WholeReferenceGauge_negative_geometryPotentialReferenceRegularity
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ G.e G.X.cell
    (fun i => positiveReferenceCylinderChart (G.Y i))
    (fun i => positiveReferenceCylinderInverse (G.Y i))
    (fun i p => G.H i p.1) G.τ G.σ G.Q G.N m hm a
  cases a <;> simp [atomIsGeometry] at ha ⊢

theorem negativeInverse_reference_geometry_bounds (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ), G.Neg η m →
        ∀ a : Atom, atomIsGeometry a → ∀ p ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
          |mixedDerivative i j (G.atomRef η a m) p| ≤
            B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  obtain ⟨B, hB, hb⟩ :=
    n04WholeReferenceGauge_negative_geometryReferenceJets_enlargedMaterialData
      G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ G.X.κ_pos s
  refine ⟨B, hB, ?_⟩
  intro η m hm a ha p hp i j hij
  have hne : a ≠ .auxiliaryColumn :=
    atomIsNegativeInverseReference_ne_auxiliary (Or.inl ha)
  rw [G.inverseReference_atomRef_unreplaced η m a hne]
  apply hb G.e G.X.cell
    (fun i => positiveReferenceCylinderChart (G.Y i))
    (fun i => positiveReferenceCylinderInverse (G.Y i))
    (fun i p => G.H i p.1) G.τ G.σ G.Q G.N
    (fun m => ⟨G.W.C.cell m, G.W.host m, G.X.optical m⟩) m hm a
    (negativeInverse_geometry_reference_cases a ha) p hp i j hij

/-- The four length costs are uniform even before selecting a negative
piece.  Their positivity is supplied by the same reference geometry. -/
theorem negativeInverse_length_values :
    ∃ B : ℝ, 0 < B ∧ ∀ (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ),
      0 < (G.V η).physicalRight m - (G.V η).physicalLeft m ∧
      0 < (G.V η).right m - (G.V η).left m ∧
      (G.V η).physicalRight m - (G.V η).physicalLeft m ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B ∧
      ((G.V η).physicalRight m - (G.V η).physicalLeft m)⁻¹ ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B ∧
      (G.V η).right m - (G.V η).left m ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B ∧
      ((G.V η).right m - (G.V η).left m)⁻¹ ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  obtain ⟨B, hB, hb⟩ := n04WholeReferenceGauge_length_values_enlargedMaterialData
    G.W.P G.W.metadata.selected G.W.metadata.first_two one_pos G.W.realizes G.W.hw
    G.W.coordinates G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ G.e G.X.cell G.X.cell_mem
    (fun i => positiveReferenceCylinderChart (G.Y i))
    (fun i => positiveReferenceCylinderInverse (G.Y i))
    (fun i p => G.H i p.1) G.τ G.σ G.Q G.N
  exact ⟨B, hB, fun _ m => hb m⟩

/-- A single selected-reference interface includes all spatial orders of
the chart, inverse, height, Jacobian and fixed interval costs. -/
theorem negativeInverse_referenceJets :
    (∀ (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ), G.Neg η m →
      ∀ a : Atom, atomIsNegativeInverseReference a →
        ContDiffOn ℝ ∞ (G.atomRef η a m) unitStrip ∧
          ∀ p ∈ unitStrip, G.atomRef η a m (p + (0, Real.pi)) = G.atomRef η a m p) ∧
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ), G.Neg η m →
        ∀ a : Atom, atomIsNegativeInverseReference a → ∀ p ∈ unitStrip,
          ∀ i j : ℕ, i + j ≤ s →
            |mixedDerivative i j (G.atomRef η a m) p| ≤
              B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  have hl := n04WholeReferenceGauge_lengthReferenceJets_enlargedMaterialData
    G.W.P G.W.metadata.selected G.W.metadata.first_two one_pos G.W.realizes G.W.hw
    G.W.coordinates G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ G.e G.X.cell G.X.cell_mem
    (fun i => positiveReferenceCylinderChart (G.Y i))
    (fun i => positiveReferenceCylinderInverse (G.Y i))
    (fun i p => G.H i p.1) G.τ G.σ G.Q G.N
  constructor
  · intro η m hm a ha
    rcases ha with ha | ⟨canonical, inverse, rfl⟩
    · exact G.negativeInverse_reference_geometry_regular η m hm a ha
    · have hne : canonicalLengthSelector canonical inverse ≠ .auxiliaryColumn :=
        atomIsNegativeInverseReference_ne_auxiliary
          (Or.inr ⟨canonical, inverse, rfl⟩)
      rw [G.inverseReference_atomRef_unreplaced η m _ hne]
      exact hl.1 (G.W.C.referenceState, 0) m canonical inverse
  · intro s
    obtain ⟨BG, hBG, hG⟩ := G.negativeInverse_reference_geometry_bounds s
    obtain ⟨BL, hBL, hL⟩ := hl.2 s
    let B := max BG BL
    have hB : 0 < B := hBG.trans_le (le_max_left _ _)
    refine ⟨B, hB, ?_⟩
    intro η m hm a ha p hp i j hij
    have hfloor := (G.cost_nonneg η).2.2 m
    have hcost {c : ℝ} (hc : c ≤ B) :
        c * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ c ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B :=
      mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le hfloor hc)
        (Real.rpow_nonneg (zero_le_one.trans hfloor) _) hB.le
    rcases ha with ha | ⟨canonical, inverse, rfl⟩
    · exact (hG η m hm a ha p hp i j hij).trans (hcost (le_max_left _ _))
    · have hne : canonicalLengthSelector canonical inverse ≠ .auxiliaryColumn :=
        atomIsNegativeInverseReference_ne_auxiliary
          (Or.inr ⟨canonical, inverse, rfl⟩)
      rw [G.inverseReference_atomRef_unreplaced η m _ hne]
      exact (hL (G.W.C.referenceState, 0) m canonical inverse p hp i j hij).trans
        (hcost (le_max_right _ _))

end N04RealizationGauge

section UniformSmallness

variable {D : ReferenceData} {S : PhysicalSpacesData} {T : MaterialData}
  {cell : ℕ → ℕ} {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

/-- Every fixed finite spatial prefix becomes uniformly small after one
neighborhood restriction, even with an additional fixed coefficient power. -/
private theorem n04NegativeInverse_valuePrefix_uniform_small
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hvalue : ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m →
        ∀ (q : unitStrip) (i j : ℕ), i + j ≤ s →
          |mixedDerivative i j (fun y => f z m y - f₀ m y) q.val| ≤
            B * T.E0 (T.sample (cell m)) ^ B *
              T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) * parameterGrading S (s + loss) z)
    (s : ℕ) (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : ℕ, ∃ ε' : ℝ, base ≤ b ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ z ∈ sectorNeighborhood S b ε' ε', ∀ m, P m →
        ∀ (q : unitStrip) (i j : ℕ), i + j ≤ s →
          T.E0 (T.sample (cell m)) ^ A *
            |mixedDerivative i j (fun y => f z m y - f₀ m y) q.val| < δ := by
  obtain ⟨loss, hdiff⟩ := hvalue
  obtain ⟨B, hB, hb⟩ := hdiff s
  obtain ⟨C, hC, hbound⟩ := material_sample_height_coefficient_power_bounded
    hD hT cell (A + B) (by norm_num : (0 : ℝ) < 3 / 4)
  let ε' := min ε (δ / (2 * (B * C)))
  have hBC : 0 < B * C := mul_pos hB hC
  have hε' : 0 < ε' := lt_min hε (div_pos hδ (mul_pos (by norm_num) hBC))
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'δ : ε' ≤ δ / (2 * (B * C)) := min_le_right _ _
  refine ⟨max base (s + loss), ε', le_max_left _ _, hε', hε'ε, ?_⟩
  intro z hz m hm q i j hij
  have hzold : z ∈ sectorNeighborhood S base ε ε :=
    sectorNeighborhood_mono S (le_max_left _ _) hε'ε hε'ε hz
  have hsample := hT.2.1 _ (materialSample_mem_interval hD hT (cell m))
  have hE : 0 < T.E0 (T.sample (cell m)) := hsample.2.2.1
  have hg : 0 ≤ parameterGrading S (s + loss) z := apply_nonneg _ _
  have hsmall : (B * C) * parameterGrading S (s + loss) z < δ := by
    calc
      _ < (B * C) * (2 * ε') := mul_lt_mul_of_pos_left
        (n07a_parameterGrading_lt_twice_radius (le_max_right _ _) hz) hBC
      _ ≤ (B * C) * (2 * (δ / (2 * (B * C)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hε'δ (by norm_num)) hBC.le
      _ = δ := by field_simp [hBC.ne']
  calc
    _ ≤ T.E0 (T.sample (cell m)) ^ A *
        (B * T.E0 (T.sample (cell m)) ^ B *
          T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            parameterGrading S (s + loss) z) :=
      mul_le_mul_of_nonneg_left (hb z hzold m hm q i j hij)
        (Real.rpow_nonneg hE.le _)
    _ = B * (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (cell m)) ^ (A + B)) *
          parameterGrading S (s + loss) z := by
      rw [Real.rpow_add hE]
      ring
    _ ≤ (B * C) * parameterGrading S (s + loss) z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound m) hB.le) hg
    _ < δ := hsmall

/-- Only the value-difference part of current data is used to choose
this neighborhood; no parameter jet is requested at this stage. -/
theorem CurrentJetDataOn.negativeInverse_uniform_small
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (s : ℕ) (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : ℕ, ∃ ε' : ℝ, base ≤ b ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ z ∈ sectorNeighborhood S b ε' ε', ∀ m, P m →
        ∀ (q : unitStrip) (i j : ℕ), i + j ≤ s →
          T.E0 (T.sample (cell m)) ^ A *
            |mixedDerivative i j (fun y => f z m y - f₀ m y) q.val| < δ :=
  n04NegativeInverse_valuePrefix_uniform_small hD hT hε h.2.choose_spec.1 s A hδ

end UniformSmallness

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- One auxiliary-column instance chooses the neighborhood; exact atom
preservation then makes that same choice valid for every auxiliary column. -/
theorem negativeInverse_atomData_uniform_small
    {b : ℕ} {ε : ℝ} (hε : 0 < ε) (a : Atom) (ha : a ≠ .auxiliaryColumn)
    (h : G.Data 0 (G.Neg 0) b ε (G.atomFamily 0 a) (G.atomRef 0 a))
    (s : ℕ) (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b' : ℕ, ∃ ε' : ℝ, b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ (η : (G.W.S.height (3 / 4 : ℝ)).Space),
        ∀ z ∈ sectorNeighborhood G.W.S b' ε' ε', ∀ m, G.Neg η m →
          ∀ (q : unitStrip) (i j : ℕ), i + j ≤ s →
            G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ A *
              |mixedDerivative i j
                (fun y => G.atomFamily η a z m y - G.atomRef η a m y) q.val| < δ := by
  have hU := isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT
  obtain ⟨b', ε', hb, hε', hε'ε, hsmall⟩ :=
    h.negativeInverse_uniform_small G.W.radial.1 hU hε s A hδ
  refine ⟨b', ε', hb, hε', hε'ε, ?_⟩
  intro η z hz m hm q i j hij
  rw [G.nonAuxiliary_atomFamily_eq 0 η a ha, G.nonAuxiliary_atomRef_eq 0 η a ha]
  exact hsmall z hz m hm q i j hij

/-- A current geometry atom has a uniform polynomial value bound on one
smaller neighborhood.  The neighborhood is selected before the auxiliary
column and every negative piece. -/
theorem negativeInverse_atom_value_bound
    {b : ℕ} {ε : ℝ} (hε : 0 < ε) (a : Atom) (ha : atomIsGeometry a)
    (h : G.Data 0 (G.Neg 0) b ε (G.atomFamily 0 a) (G.atomRef 0 a)) :
    ∃ b' : ℕ, ∃ ε' B : ℝ, b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧ 0 < B ∧
      ∀ (η : (G.W.S.height (3 / 4 : ℝ)).Space),
        ∀ z ∈ sectorNeighborhood G.W.S b' ε' ε', ∀ m, G.Neg η m →
          ∀ q ∈ unitStrip, |G.atomFamily η a z m q| ≤
            B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  have hne : a ≠ .auxiliaryColumn :=
    atomIsNegativeInverseReference_ne_auxiliary (Or.inl ha)
  obtain ⟨b', ε', hb, hε', hε'ε, hsmall⟩ :=
    G.negativeInverse_atomData_uniform_small hε a hne h 0 0 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨C, hC, href⟩ := G.negativeInverse_reference_geometry_bounds 0
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (1 + C) C
  refine ⟨b', ε', B, hb, hε', hε'ε, hB, ?_⟩
  intro η z hz m hm q hq
  let E := G.W.U.E0 (G.W.U.sample ((G.V η).cell m))
  have hE : 1 ≤ E := (G.cost_nonneg η).2.2 m
  have hdiff : |G.atomFamily η a z m q - G.atomRef η a m q| < 1 := by
    simpa only [Real.rpow_zero, one_mul, spaces_mixedDerivative_zero] using
      hsmall η z hz m hm ⟨q, hq⟩ 0 0 (by omega)
  have hreference : |G.atomRef η a m q| ≤ C * E ^ C := by
    simpa only [spaces_mixedDerivative_zero] using href η m hm a ha q hq 0 0 (by omega)
  calc
    |G.atomFamily η a z m q| =
        |(G.atomFamily η a z m q - G.atomRef η a m q) + G.atomRef η a m q| := by
      rw [sub_add_cancel]
    _ ≤ |G.atomFamily η a z m q - G.atomRef η a m q| + |G.atomRef η a m q| :=
      abs_add_le _ _
    _ ≤ 1 + C * E ^ C := add_le_add hdiff.le hreference
    _ ≤ E ^ C + C * E ^ C := add_le_add_right (Real.one_le_rpow hE hC.le) _
    _ = (1 + C) * E ^ C := by ring
    _ ≤ B * E ^ B := hpack E hE

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_referenceJets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_referenceJets

/-- info: 'ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_uniform_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_uniform_small
