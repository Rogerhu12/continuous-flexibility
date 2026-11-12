import ContinuousFlexibility.Analysis.N07aCanonicalAtomBounds

/-!
# Quantitative displacement of the actual inverse chart

The inverse radial atom is sampled on the fixed canonical unit strip.
Its current-minus-reference bound therefore controls the actual inverse
points without asserting that either current point lies in a reference piece.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

/-- Keep existential elimination independent of the large geometric predicate. -/
private theorem n07a_displacement_with_loss {Condition : ℕ → Prop} {P : Prop}
    (h : ∃ n, Condition n) (hP : ∀ n, Condition n → P) : P := by
  obtain ⟨n, hn⟩ := h
  exact hP n hn

private theorem n07a_displacement_with_positive_bound {Condition : ℝ → Prop} {P : Prop}
    (h : ∃ B, 0 < B ∧ Condition B)
    (hP : ∀ B, 0 < B → Condition B → P) : P := by
  obtain ⟨B, hB, hbound⟩ := h
  exact hP B hB hbound

theorem n07a_parameterGrading_lt_twice_radius
    {b s : ℕ} {η : ℝ} {z : CanonicalGeometry.Parameter S}
    (hs : s ≤ b) (hz : z ∈ sectorNeighborhood S b η η) :
    CanonicalGeometry.parameterGrading S s z < 2 * η := by
  have h₁ : sectorGrading S s z.1 < η :=
    (solve_sectorGrading_monotone S hs z.1).trans_lt hz.1
  have h₂ : |z.2| < η := hz.2
  have he : CanonicalGeometry.parameterGrading S s z =
      sectorGrading S s z.1 + |z.2| :=
    pairGrading_apply (E := StateDirections S) (F := ℝ) (sectorGrading S) realGrading s z
  exact he.trans_lt ((add_lt_add h₁ h₂).trans_eq (two_mul η).symm)

theorem n07a_inverseChart_radial_displacement
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hinterval : ∀ m, K.left m < K.right m)
    (hphysical : ∀ m, K.physicalLeft m < K.physicalRight m) :
    ∃ low : ℕ, ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m y, y ∈ canonicalOpen S K m →
          |(K.inverseChart (liftSectorParameter S C z) m y).1 -
              (K.inverseChart (C.referenceState, 0) m y).1| ≤
            e m * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
              CanonicalGeometry.parameterGrading S low z := by
  refine n07a_displacement_with_loss hcur.2.1 ?_
  intro low hdiff
  refine n07a_displacement_with_positive_bound (hdiff 0) ?_
  intro B hB hBb
  let e : ℕ → ℝ := fun m =>
    (K.physicalRight m - K.physicalLeft m) * (B * T.E0 (T.sample (K.cell m)) ^ B)
  have he : N07aSampleSubpower T K e := N07aSampleSubpower.mul hD hT
    (n07a_physicalLength_subpower hD hT href)
    (N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT B)
      (N07aSampleSubpower.e0_rpow hD hT B))
  have he0 (m : ℕ) : 0 ≤ e m := by
    have hp := hT.2.1 _
      (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
    exact mul_nonneg (sub_pos.mpr (hphysical m)).le
      (mul_nonneg hB.le (Real.rpow_nonneg hp.2.2.1.le B))
  refine ⟨low, e, he, he0, fun z hz m y hy => ?_⟩
  let p := n07aCanonicalUnitInversePoint K m y
  have hp : p ∈ CanonicalGeometry.unitStrip :=
    n07aCanonicalUnitInversePoint_maps (hinterval m) hy
  have hpy : CanonicalGeometry.canonicalUnitPoint K m p = y :=
    n07aCanonicalUnitPoint_inverse (hinterval m) y
  have hraw : |CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m
        .inverseRadial p - CanonicalGeometry.atom D T S C L K
        (C.referenceState, 0) m .inverseRadial p| ≤
      B * T.E0 (T.sample (K.cell m)) ^ B * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        CanonicalGeometry.parameterGrading S low z := by
    simpa only [CanonicalGeometry.differenceJets, spaces_mixedDerivative_zero, Nat.zero_add]
      using hBb z hz m .inverseRadial ⟨p, hp⟩ 0 0 (by omega)
  have hL : 0 < K.physicalRight m - K.physicalLeft m := sub_pos.mpr (hphysical m)
  have heq : (K.inverseChart (liftSectorParameter S C z) m y).1 -
        (K.inverseChart (C.referenceState, 0) m y).1 =
      (K.physicalRight m - K.physicalLeft m) *
        (CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m .inverseRadial p -
          CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m .inverseRadial p) := by
    simp only [CanonicalGeometry.atom, hpy]
    field_simp [hL.ne'] <;> ring
  rw [heq, abs_mul, abs_of_pos hL]
  exact (mul_le_mul_of_nonneg_left hraw hL.le).trans_eq (by dsimp only [e]; ring)

end ContinuousFlexibility.Analysis
