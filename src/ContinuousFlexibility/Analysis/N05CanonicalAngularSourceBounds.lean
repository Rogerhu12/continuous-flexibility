import ContinuousFlexibility.Analysis.N05CanonicalAngularLift
import ContinuousFlexibility.Analysis.N05CanonicalSourceCoordinateBounds
import ContinuousFlexibility.Analysis.N05ReferenceWeightedPhysical

/-!
# Actual weighted angular source representatives and their limits

The unsigned lift is fixed before any weaker physical exponent or material
order is chosen. Every square-summable jet column has its genuine reference
source bound, and differences obey the same bound. Thus convergence of the
canonical column implies physical L² convergence of these very lifts.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open scoped Topology

def n05CanonicalAngularSource (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (γ t : ℝ)
    (a : CanonicalL2Sequence S K) : PolarPoint → ℝ :=
  n05CanonicalAngularLift S C K (fun m => n05CanonicalSampleWeight T S K γ t m • a m)

theorem n05CanonicalAngularSource_periodic (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (γ t : ℝ)
    (a : CanonicalL2Sequence S K) :
    Function.Periodic (n05CanonicalAngularSource T S C K γ t a) (0, Real.pi) :=
  n05CanonicalAngularLift_periodic S C K _

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)

include h hcoordinates in
theorem n05CanonicalAngularSource_source_ae (γ t : ℝ)
    (a : CanonicalL2Sequence S K) (m : ℕ) :
    (fun p => n05CanonicalSampleWeight T S K γ t m * a m p)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        (n05CanonicalAngularSource T S C K γ t a) := by
  have hsmul : (n05CanonicalSampleWeight T S K γ t m • a m : CanonicalL2 S K m)
      =ᵐ[canonicalMeasure S K m]
        (fun p => n05CanonicalSampleWeight T S K γ t m * a m p) := by
    filter_upwards [Lp.coeFn_smul (n05CanonicalSampleWeight T S K γ t m) (a m)] with p hp
    simpa only [Pi.smul_apply, smul_eq_mul] using hp
  exact hsmul.symm.trans (n05CanonicalAngularLift_source_ae h hcoordinates _ m)

include h hcoordinates in
theorem n05CanonicalAngularSource_linear_combination_ae (γ t : ℝ)
    (a b : CanonicalL2Sequence S K) (c d : ℝ) :
    n05CanonicalAngularSource T S C K γ t (c • a + d • b) =ᵐ[radialPhysicalMeasure D]
      (fun p => c * n05CanonicalAngularSource T S C K γ t a p +
        d * n05CanonicalAngularSource T S C K γ t b p) := by
  have he : (fun m => n05CanonicalSampleWeight T S K γ t m • ((c • a + d • b) m)) =
      c • (fun m => n05CanonicalSampleWeight T S K γ t m • a m) +
        d • (fun m => n05CanonicalSampleWeight T S K γ t m • b m) := by
    funext m
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_add]
    rw [smul_comm (n05CanonicalSampleWeight T S K γ t m) c (a m),
      smul_comm (n05CanonicalSampleWeight T S K γ t m) d (b m)]
  change n05CanonicalAngularLift S C K _ =ᵐ[radialPhysicalMeasure D] _
  rw [he]
  exact n05CanonicalAngularLift_linear_combination_ae h hcoordinates _ _ c d

variable (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)

include h hcoordinates hD hT in
theorem n05CanonicalAngularSource_reference_bound
    {γw γ : ℝ} (hγw : 0 ≤ γw) (hgap : γw < γ) (t M : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : CanonicalL2Sequence S K,
      SourceDerivativeMember D γw M (n05CanonicalAngularSource T S C K γ t a) ∧
      sourceNormSquare D γw M (n05CanonicalAngularSource T S C K γ t a, 0) ≤
        B * ‖a‖ ^ 2 := by
  obtain ⟨B, hB, hb⟩ :=
    n05_canonicalSequenceSource_reference_bound hD hT h hcoordinates hγw hgap t M
  exact ⟨B, hB, fun a => hb a _ (n05CanonicalAngularSource_periodic T S C K γ t a)
    (n05CanonicalAngularSource_source_ae h hcoordinates γ t a)⟩

include h hcoordinates hD hT in
/-- This estimates the difference of the fixed physical representatives,
not just a separately selected representative of the difference class. -/
theorem n05CanonicalAngularSource_sub_reference_bound
    {γw γ : ℝ} (hγw : 0 ≤ γw) (hgap : γw < γ) (t M : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ a b : CanonicalL2Sequence S K,
      SourceDerivativeMember D γw M (fun p =>
        n05CanonicalAngularSource T S C K γ t a p -
          n05CanonicalAngularSource T S C K γ t b p) ∧
      sourceNormSquare D γw M ((fun p =>
        n05CanonicalAngularSource T S C K γ t a p -
          n05CanonicalAngularSource T S C K γ t b p), 0) ≤ B * ‖a - b‖ ^ 2 := by
  obtain ⟨B, hB, hb⟩ :=
    n05_canonicalSequenceSource_reference_bound hD hT h hcoordinates hγw hgap t M
  refine ⟨B, hB, fun a b => hb (a - b) _ ?_ ?_⟩
  · intro p
    change n05CanonicalAngularSource T S C K γ t a (p + (0, Real.pi)) -
      n05CanonicalAngularSource T S C K γ t b (p + (0, Real.pi)) =
        n05CanonicalAngularSource T S C K γ t a p - n05CanonicalAngularSource T S C K γ t b p
    rw [n05CanonicalAngularSource_periodic T S C K γ t a p,
      n05CanonicalAngularSource_periodic T S C K γ t b p]
  · intro m
    filter_upwards [Lp.coeFn_sub (a m) (b m),
      n05CanonicalAngularSource_source_ae h hcoordinates γ t a m,
      n05CanonicalAngularSource_source_ae h hcoordinates γ t b m] with p hp ha hb
    change n05CanonicalSampleWeight T S K γ t m * ((a m - b m) p) = _
    rw [hp]
    simp only [Pi.sub_apply, mul_sub, ha, hb, canonicalSource]
    ring

include h hcoordinates hD hT in
/-- The actual fields converge in physical L² when their canonical
coordinates converge, at any fixed weaker positive reference exponent. -/
theorem n05CanonicalAngularSource_tendsto_physical
    {γw γ : ℝ} (hγw : 0 < γw) (hgap : γw < γ) (t M : ℝ)
    {a : ℕ → CanonicalL2Sequence S K} {b : CanonicalL2Sequence S K}
    (hab : Tendsto a atTop (𝓝 b)) :
    ∃ ha : ∀ n, MemLp (n05CanonicalAngularSource T S C K γ t (a n)) 2
        (radialPhysicalMeasure D),
      ∃ hb : MemLp (n05CanonicalAngularSource T S C K γ t b) 2
          (radialPhysicalMeasure D),
        Tendsto (fun n => (ha n).toLp (n05CanonicalAngularSource T S C K γ t (a n)))
          atTop (𝓝 (hb.toLp (n05CanonicalAngularSource T S C K γ t b))) := by
  obtain ⟨_, _, hsource⟩ :=
    n05CanonicalAngularSource_reference_bound h hcoordinates hD hT hγw.le hgap t M
  obtain ⟨B, _, hsub⟩ :=
    n05CanonicalAngularSource_sub_reference_bound h hcoordinates hD hT hγw.le hgap t M
  have hpart : RadialPartition D := hD.choose_spec.2.1
  have horder : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hmem (c : CanonicalL2Sequence S K) :
      MemLp (n05CanonicalAngularSource T S C K γ t c) 2
        (referenceWeightedMeasure D γw M) :=
    memLp_referenceWeightedMeasure horder hpart (hsource c).1.1 (hsource c).1.2
  have hnorm : Tendsto (fun n => ‖a n - b‖ ^ 2) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      ((hab.sub tendsto_const_nhds).norm.pow 2)
  have hlim : Tendsto (fun n => ∫ p,
      (n05CanonicalAngularSource T S C K γ t (a n) p -
        n05CanonicalAngularSource T S C K γ t b p) ^ 2
          ∂referenceWeightedMeasure D γw M) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg (fun p => sq_nonneg _)) ?_
      (by simpa only [mul_zero] using hnorm.const_mul B)
    intro n
    rw [integral_sq_referenceWeightedMeasure_eq horder hpart
      (hsub (a n) b).1.1 (hsub (a n) b).1.2]
    simpa only [sourceNormSquare, zero_pow (by decide : 2 ≠ 0), zero_add] using
      (hsub (a n) b).2
  exact n05_referenceWeighted_tendsto_physical hD hγw (fun n => hmem (a n)) (hmem b) hlim

end ContinuousFlexibility.Statements
