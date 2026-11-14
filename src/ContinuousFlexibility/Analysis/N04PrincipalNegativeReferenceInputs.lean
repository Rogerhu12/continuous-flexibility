module

public import ContinuousFlexibility.Analysis.N04PrincipalNegativePotential
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
public import ContinuousFlexibility.Analysis.SpacesCylinderEvenJets

/-!
# Fixed inputs of the negative unit potential

The squared inverse interval length is a static reference atom. The
canonical radial coordinate on a negative piece is the negative of its
reference angular principal coefficient. Both therefore carry the
actual stored sample envelope, with no comparison between pieces.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

theorem n04PrincipalNegative_canonicalRadial_smooth (m : ℕ) :
    ContDiff ℝ ∞ (fun q : PolarPoint => (canonicalUnitPoint K m q).1) :=
  contDiff_const.add (contDiff_const.mul contDiff_fst)

/-- Every spatial order of the fixed inverse square is bounded by one
polynomial sample envelope; positive spatial derivatives vanish. -/
theorem n04PrincipalNegative_inverseLengthSquare_reference_bound
    (href : ReferenceJets D T S C L K)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m))) :
    ∃ B : ℝ, 0 < B ∧ ∀ m (a b : ℕ) (q : PolarPoint),
      |mixedDerivative a b (fun _ : PolarPoint => (K.right m - K.left m)⁻¹ ^ 2) q| ≤
        B * T.E0 (T.sample (K.cell m)) ^ B := by
  have hzero := href.2 0
  let A : ℝ := hzero.choose
  have hA : 0 < A := hzero.choose_spec.1
  have hpack := coefficientEnvelope_pack (A ^ 2) (A * 2)
  refine ⟨hpack.choose, hpack.choose_spec.1, ?_⟩
  intro m a b q
  have hcenter : ((1 / 2, 0) : PolarPoint) ∈ unitStrip := by
    constructor <;> norm_num
  have hi : |(K.right m - K.left m)⁻¹| ≤ A * T.E0 (T.sample (K.cell m)) ^ A := by
    have hh := hzero.choose_spec.2 m .canonicalLengthInverse (1 / 2, 0) hcenter 0 0 le_rfl
    simpa only [spaces_mixedDerivative_zero, atom] using hh
  have hconst :
      |mixedDerivative a b (fun _ : PolarPoint => (K.right m - K.left m)⁻¹ ^ 2) q| ≤
        |(K.right m - K.left m)⁻¹ ^ 2| := by
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
      simp [mixedDerivative, iteratedDeriv_const, ha, hb] <;> positivity
  have hsquare : |(K.right m - K.left m)⁻¹ ^ 2| ≤
      A ^ 2 * T.E0 (T.sample (K.cell m)) ^ (A * 2) := by
    rw [abs_pow]
    have hh := pow_le_pow_left₀ (abs_nonneg _) hi 2
    rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans (hE m))] at hh
    exact hh
  exact hconst.trans (hsquare.trans (hpack.choose_spec.2 _ (hE m)))

/-- The radial coordinate on each negative piece has the reference
principal-C jet envelope at every order. -/
theorem n04PrincipalNegative_canonicalRadial_reference_bound
    {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (href : ReferenceJets D T S C L K)
    (hzref : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState) :
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, K.positive m = false →
      ∀ (q : PolarPoint), q ∈ unitStrip → ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b (fun p => (canonicalUnitPoint K m p).1) q| ≤
          B * T.E0 (T.sample (K.cell m)) ^ B := by
  intro s
  have hb := href.2 s
  refine ⟨hb.choose, hb.choose_spec.1, ?_⟩
  intro m hm q hq a b hab
  let F : PolarPoint → ℝ := atom D T S C L K (C.referenceState, 0) m .principalC
  have heq : EqOn (fun p => (canonicalUnitPoint K m p).1) (fun p => -F p) unitStrip := by
    intro p hp
    have hc := (hB.2.2.2.1 (C.referenceState, 0) hzref hsref m hm
      (canonicalUnitPoint K m p)
      (n04PrincipalNegative_unitPoint_mem K m (hA.referenceBounds m).2.1 hp)).2.2
    change (canonicalUnitPoint K m p).1 =
      -((K.coefficients (C.referenceState, 0) m).c (canonicalUnitPoint K m p))
    rw [hc, neg_neg]
  have hj : mixedDerivative a b (fun p => (canonicalUnitPoint K m p).1) q =
      -mixedDerivative a b F q := by
    calc
      _ = mixedDerivative a b (fun p => -F p) q :=
        mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) heq a b hq
      _ = _ := by
        simpa only [neg_one_mul] using spaces_mixedDerivative_const_mul F (-1) a b q
  rw [hj, abs_neg]
  exact hb.choose_spec.2 m .principalC q hq a b hab

end ContinuousFlexibility.Analysis
