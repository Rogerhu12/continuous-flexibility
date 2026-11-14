module

public import ContinuousFlexibility.Analysis.N04NegativeHeightReferenceIdentity

/-!
# Reference-normalized formulas for the negative height

The angular numerator and the coefficient--Jacobian factor multiplied by
the square of the fixed reference height both equal one at the reference
state.  Taking their square roots therefore leaves only scalar operations
near one; all large or small reference height scales stay in fixed factors.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

/-- Normalize a positive density identity by any positive reference
height.  Both formulas use the same two dimensionless factors. -/
theorem n04NegativeHeight_normalized_scalar
    {N d h h₀ : ℝ} (hd : 0 < d) (hh : 0 < h) (hh₀ : 0 < h₀)
    (hdensity : N = d * h ^ 2) :
    h = h₀ * Real.sqrt N * (Real.sqrt (d * h₀ ^ 2))⁻¹ ∧
      h⁻¹ = h₀⁻¹ * (Real.sqrt N)⁻¹ * Real.sqrt (d * h₀ ^ 2) := by
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hN : Real.sqrt N = Real.sqrt d * h := by
    rw [hdensity, Real.sqrt_mul hd.le, Real.sqrt_sq hh.le]
  have hA : Real.sqrt (d * h₀ ^ 2) = Real.sqrt d * h₀ := by
    rw [Real.sqrt_mul hd.le, Real.sqrt_sq hh₀.le]
  constructor
  · rw [hN, hA]
    field_simp [hsqrt.ne', hh₀.ne'] <;> ring
  · rw [hN, hA]
    field_simp [hsqrt.ne', hh.ne', hh₀.ne'] <;> ring

namespace N04RealizationGauge

variable (G : N04RealizationGauge)
  (η : (G.W.S.height (3 / 4 : ℝ)).Space)

/-- The current physical radial coefficient and Jacobian, normalized by
the fixed reference height. -/
def negativeHeightNormalizedRadialFamily :
    Parameter (G.S η) → ℕ → PolarPoint → ℝ :=
  fun z m q => G.physicalRadialFamily η z m q * G.atomFamily η .jacobian z m q *
    G.atomRef η .height m q ^ 2

/-- The reference value of the normalized coefficient--Jacobian factor. -/
def negativeHeightNormalizedRadialRef : ℕ → PolarPoint → ℝ :=
  fun m q => G.physicalRadialRef η m q * G.atomRef η .jacobian m q *
    G.atomRef η .height m q ^ 2

theorem negativeHeightNormalizedRadialFamily_zero :
    G.negativeHeightNormalizedRadialFamily η 0 =
      G.negativeHeightNormalizedRadialRef η := by
  funext m q
  simp only [negativeHeightNormalizedRadialFamily, negativeHeightNormalizedRadialRef,
    G.physicalRadialFamily_zero η m, G.height_atomFamily_zero η .jacobian]

theorem negativeHeightNormalizedRadialRef_one (m : ℕ) (hm : G.Neg η m)
    (q : PolarPoint) (hq : q ∈ unitStrip) :
    G.negativeHeightNormalizedRadialRef η m q = 1 :=
  G.negativeHeight_referenceDensity η m hm q hq

/-- Current height and absolute Jacobian are strictly positive on every
retained negative reference half, throughout the original neighborhood. -/
theorem negativeHeight_geometry_pos
    (z : Parameter (G.S η))
    (hz : z ∈ sectorNeighborhood (G.S η) G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) (q : PolarPoint) (hq : q ∈ unitStrip) :
    0 < G.atomFamily η .height z m q ∧ 0 < G.atomFamily η .jacobian z m q := by
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
  let K := G.W.A G.X.e₀
  let k := G.negativeIndex j
  have hk : G.X.e₀ k = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  have hA := n04b_actualTypedAtlas_partA
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀
  have hp : physicalUnitPoint K k q ∈ referencePhysicalPieceOpen G.W.S K k :=
    (n04NegativeGeometry_affine_unitPoint (K.physicalLeft k) (K.physicalRight k)
      (hA.referenceBounds k).1).2.1 hq
  have hfields := n04NegativeGeometry_referenceHalf_fields
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ k j.1 j.2 hk
    (liftSectorParameter_mem_stateNeighborhood (C := G.W.C) hz le_rfl)
    (G.W.through03.1.1.2.2.1.liftSectorParameter_sector z)
  have hpos := hfields.2.2.1 (physicalUnitPoint K k q) hp
  rw [G.negative_atomFamily η z m j hi .height (by decide),
    G.negative_atomFamily η z m j hi .jacobian (by decide)]
  exact ⟨hpos.2, abs_pos.mpr hpos.1⟩

/-- The exact density identity expressed in the literal normalized atoms. -/
theorem negativeHeight_currentDensity
    (z : Parameter (G.S η))
    (hz : z ∈ sectorNeighborhood (G.S η) G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) (q : PolarPoint) (hq : q ∈ unitStrip) :
    G.negativeHeightAngularFamily η z m q =
      (G.physicalRadialFamily η z m q * G.atomFamily η .jacobian z m q) *
        G.atomFamily η .height z m q ^ 2 := by
  have hformula := G.negativeHeight_sqrt_formula η z hz m hm q hq
  have hgeom := G.negativeHeight_geometry_pos η z hz m hm q hq
  have hd := mul_pos (G.physicalRadial_pos η z hz m hm hq) hgeom.2
  have hsquare := congrArg (fun x : ℝ => x ^ 2) hformula.2.1
  rw [Real.sq_sqrt (div_pos hformula.1 hd).le] at hsquare
  have he := (eq_div_iff hd.ne').mp hsquare
  exact he.symm.trans (mul_comm _ _)

/-- Both scalar factors are positive throughout the original neighborhood. -/
theorem negativeHeight_normalizedFactors_pos
    (z : Parameter (G.S η))
    (hz : z ∈ sectorNeighborhood (G.S η) G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) (q : PolarPoint) (hq : q ∈ unitStrip) :
    0 < G.negativeHeightAngularFamily η z m q ∧
      0 < G.negativeHeightNormalizedRadialFamily η z m q := by
  refine ⟨(G.negativeHeight_sqrt_formula η z hz m hm q hq).1, ?_⟩
  exact mul_pos
    (mul_pos (G.physicalRadial_pos η z hz m hm hq)
      (G.negativeHeight_geometry_pos η z hz m hm q hq).2)
    (sq_pos_of_pos (G.negative_heightRef_pos η m hm q hq))

/-- Reference-normalized reconstruction of the literal height and its
reciprocal.  There is no new height hypothesis in either formula. -/
theorem negativeHeight_normalized_formula
    (z : Parameter (G.S η))
    (hz : z ∈ sectorNeighborhood (G.S η) G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) (q : PolarPoint) (hq : q ∈ unitStrip) :
    G.atomFamily η .height z m q =
      G.atomRef η .height m q * Real.sqrt (G.negativeHeightAngularFamily η z m q) *
        (Real.sqrt (G.negativeHeightNormalizedRadialFamily η z m q))⁻¹ ∧
      G.atomFamily η .heightInverse z m q =
        G.atomRef η .heightInverse m q *
          (Real.sqrt (G.negativeHeightAngularFamily η z m q))⁻¹ *
            Real.sqrt (G.negativeHeightNormalizedRadialFamily η z m q) := by
  have hgeom := G.negativeHeight_geometry_pos η z hz m hm q hq
  exact n04NegativeHeight_normalized_scalar
    (mul_pos (G.physicalRadial_pos η z hz m hm hq) hgeom.2) hgeom.1
    (G.negative_heightRef_pos η m hm q hq)
    (G.negativeHeight_currentDensity η z hz m hm q hq)

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeHeight_normalized_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeHeight_normalized_formula
