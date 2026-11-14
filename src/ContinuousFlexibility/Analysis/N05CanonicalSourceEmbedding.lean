module

public import ContinuousFlexibility.Analysis.N05CanonicalSourceL2
public import ContinuousFlexibility.Analysis.N05CanonicalSourceLift
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The fixed actual source lift belongs to every weaker reference source space

Singleton localizer weights first give genuine localized L² membership.
The uniformly bounded finite weighted sums then establish the full source
square summability and norm bound. Thus the physical inverse can be applied
to the actual lift without assuming that a physical source already exists.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators

theorem n05_radialCellIntegrable_of_finiteSourceWeights
    {D : ReferenceData} (hD : RadialPartition D) (γ M : ℝ)
    {f : PolarPoint → ℝ}
    (hf : ∀ q : Finset ℕ,
      MemLp (fun p => Real.sqrt (n05ReferenceFiniteSourceWeight D γ M q p.1) * f p)
        2 (radialPhysicalMeasure D)) :
    RadialCellIntegrable D f := by
  intro j
  let e : ℝ := Real.exp
    (2 * M * radialQ (D.cellIndex j) + 2 * γ * radialS (D.cellIndex j))
  have he : 0 < e := Real.exp_pos _
  have hroot : Real.sqrt e ≠ 0 := (Real.sqrt_pos.mpr he).ne'
  have hs := (hf {j}).const_mul (Real.sqrt e)⁻¹
  apply MemLp.ae_eq _ hs
  exact Eventually.of_forall fun p => by
    dsimp only
    rw [n05ReferenceFiniteSourceWeight_singleton,
      Real.sqrt_mul he.le, Real.sqrt_sq (hD.2.1 j p.1)]
    change (Real.sqrt e)⁻¹ * ((Real.sqrt e * D.localizer j p.1) * f p) =
      D.localizer j p.1 * f p
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hroot, one_mul]

theorem n05_finiteSourceNormSquare_eq {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) (q : Finset ℕ) :
    (∑ j ∈ q, sourceCellSquare D γ M f j) = (2 * Real.pi)⁻¹ *
      ∫ p, (Real.sqrt (n05ReferenceFiniteSourceWeight D γ M q p.1) * f p) ^ 2
        ∂radialPhysicalMeasure D := by
  calc
    _ = (2 * Real.pi)⁻¹ * ∑ j ∈ q,
        Real.exp (2 * M * radialQ (D.cellIndex j) + 2 * γ * radialS (D.cellIndex j)) *
          ∫ p, (D.localizer j p.1 * f p) ^ 2 ∂radialPhysicalMeasure D := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [sourceCellSquare, referenceCellSquare_eq_integral hab j hf]
      ring
    _ = (2 * Real.pi)⁻¹ * ∫ p, ∑ j ∈ q,
        Real.exp (2 * M * radialQ (D.cellIndex j) + 2 * γ * radialS (D.cellIndex j)) *
          (D.localizer j p.1 * f p) ^ 2 ∂radialPhysicalMeasure D := by
      congr 1
      rw [integral_finsetSum q (fun j _ => (hf j).integrable_sq.const_mul _)]
      apply Finset.sum_congr rfl
      intro j _
      exact (integral_const_mul _ _).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        symm
        calc
          _ = n05ReferenceFiniteSourceWeight D γ M q p.1 * f p ^ 2 := by
            dsimp only
            rw [mul_pow, Real.sq_sqrt (n05ReferenceFiniteSourceWeight_nonneg D γ M q p.1)]
          _ = _ := by
            rw [n05ReferenceFiniteSourceWeight, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring

/-- A real canonical source representation has the full weaker reference
source norm, not only finite local square estimates. -/
theorem n05_volumeSource_reference_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    {γw γ : ℝ} (hγw : 0 ≤ γw) (hgap : γw < γ) (t M : ℝ) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (v : V.level γ t s) (f : PolarPoint → ℝ),
      Function.Periodic f (0, Real.pi) →
      (∀ m, (V.forget γ t s v m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m f) →
      SourceDerivativeMember D γw M f ∧ sourceNormSquare D γw M (f, 0) ≤ B * ‖v‖ ^ 2 := by
  obtain ⟨B, hB, hb⟩ :=
    n05_volumeSource_finite_weight_bound hD hT h hcoordinates hV hγw hgap t M s
  refine ⟨(2 * Real.pi)⁻¹ * B, by positivity, fun v f hf hrep => ?_⟩
  have hlocal : ∀ q : Finset ℕ,
      MemLp (fun p => Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p)
        2 (radialPhysicalMeasure D) := fun q => (hb q v f hf hrep).1
  have hcell : RadialCellIntegrable D f :=
    n05_radialCellIntegrable_of_finiteSourceWeights hD.choose_spec.2.1 γw M hlocal
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hfinite (q : Finset ℕ) :
      (∑ j ∈ q, sourceCellSquare D γw M f j) ≤ ((2 * Real.pi)⁻¹ * B) * ‖v‖ ^ 2 := by
    rw [n05_finiteSourceNormSquare_eq hab γw M hcell q]
    calc
      _ ≤ (2 * Real.pi)⁻¹ * (B * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hb q v f hf hrep).2 (by positivity)
      _ = _ := (mul_assoc _ _ _).symm
  have hs : Summable (sourceCellSquare D γw M f) :=
    summable_of_sum_le (sourceCellSquare_nonneg hab γw M hcell) hfinite
  have hnorm : (∑' j, sourceCellSquare D γw M f j) ≤
      ((2 * Real.pi)⁻¹ * B) * ‖v‖ ^ 2 :=
    Real.tsum_le_of_sum_le (sourceCellSquare_nonneg hab γw M hcell) hfinite
  refine ⟨⟨hcell, hs⟩, ?_⟩
  simpa only [sourceNormSquare, zero_pow (by decide : 2 ≠ 0), zero_add] using hnorm

/-- The fixed physical lift of every actual volume element belongs to
every strictly weaker positive reference exponent, at any fixed material
order, with a genuine bound by the canonical Hilbert norm. -/
theorem n05_canonicalSourceLift_reference_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    {γw γ : ℝ} (hγw : 0 < γw) (hgap : γw < γ) (t M : ℝ) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v : V.level γ t s,
      SourceDerivativeMember D γw M
        (n05CanonicalSourceLift S C K (V.forget γ t s v)) ∧
      sourceNormSquare D γw M
        (n05CanonicalSourceLift S C K (V.forget γ t s v), 0) ≤ B * ‖v‖ ^ 2 := by
  obtain ⟨B, hB, hb⟩ :=
    n05_volumeSource_reference_bound hD hT h hcoordinates hV hγw.le hgap t M s
  refine ⟨B, hB, fun v => ?_⟩
  have hv : VolumeMember S K V γ t s (V.forget γ t s v) := ⟨v, rfl⟩
  exact hb v (n05CanonicalSourceLift S C K (V.forget γ t s v))
    (n05CanonicalSourceLift_periodic S C K (V.forget γ t s v))
    (n05CanonicalSourceLift_source_ae h hcoordinates (V.forget γ t s v)
      (n05_volumeMember_reflection hV hv))

end ContinuousFlexibility.Statements
