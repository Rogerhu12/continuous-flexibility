module

public import ContinuousFlexibility.Analysis.N05ReferenceTests
public import ContinuousFlexibility.Analysis.N06LeftColumnSymmetry
public import ContinuousFlexibility.Radial.MatchingCutoffTests
public import ContinuousFlexibility.Scalar.GreenIdentity

/-!
# Actual periodicity of the corrected operator on even local fields

N03 writes the difference from the original operator as an element of the
original source model. Its decoded value is periodic. A radial cutoff
realizes an even periodic smooth strip germ as one genuine HeightPair,
simultaneously along the whole circle. The actual divergence is local
even when no regularity of the corrected coefficients is available.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem n06_divergenceOperator_periodic
    {A : SymmetricCoefficients} {f : PolarPoint → ℝ} {v : PolarPoint}
    (ha : Function.Periodic A.a v) (hb : Function.Periodic A.b v)
    (hc : Function.Periodic A.c v) (hf : Function.Periodic f v) :
    Function.Periodic (divergenceOperator A f) v :=
  (periodic_radialPartial
    ((ha.mul (periodic_radialPartial hf)).add (hb.mul (periodic_angularPartial hf)))).add
      (periodic_angularPartial
        ((hb.mul (periodic_radialPartial hf)).add (hc.mul (periodic_angularPartial hf))))

theorem n06_originalCoefficients_periodic
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) :
    Function.Periodic (originalCoefficients D S C z).a (0, Real.pi) ∧
      Function.Periodic (originalCoefficients D S C z).b (0, Real.pi) ∧
      Function.Periodic (originalCoefficients D S C z).c (0, Real.pi) :=
  periodic_heightCorrectedCoefficients (stateProfile D S C z.1)
    (n06_stateHeight_periodic hS z)

theorem n06_heightPairField_periodic
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (η : HeightPair S) :
    Function.Periodic (heightPairField S η) (0, Real.pi) := by
  have hp := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 η.1).2.2.1
  intro p
  simp only [heightPairField, hp p, Prod.fst_add, add_zero]

/-- The actual N03 source identity forces periodicity on every original
height test, with no periodicity assumption on the corrected coefficients. -/
theorem n06_correctedDivergence_heightPair_periodicOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (η : HeightPair S)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    divergenceOperator (L.coefficients z) (heightPairField S η) (p + (0, Real.pi)) =
      divergenceOperator (L.coefficients z) (heightPairField S η) p := by
  have hcoef := n06_originalCoefficients_periodic (C := C) hS z
  have horig := n06_divergenceOperator_periodic hcoef.1 hcoef.2.1 hcoef.2.2
    (n06_heightPairField_periodic hS η)
  have he := ((hS.1 (3 / 4 : ℝ)).2.2.2.1
    (L.error z (R.residual z) η).val).2.2.1
  have hp' : p + (0, Real.pi) ∈ annularOpen D := by
    exact ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
  have hq := h03.2.2.2.2.2.1 z hz hs η p hp
  have hq' := h03.2.2.2.2.2.1 z hz hs η (p + (0, Real.pi)) hp'
  rw [horig p, he p] at hq'
  exact sub_right_inj.mp (hq'.trans hq.symm)

/-- One compact radial cutoff realizes the entire circle of local germs;
there is no exclusion of reflection angles. -/
theorem n06_exists_heightPair_strip_germ
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {l r t : ℝ} (hsub : Ioo l r ⊆ radialCore D) (ht : t ∈ Ioo l r)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo l r ×ˢ univ))
    (hp : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), f (p + (0, Real.pi)) = f p)
    (he : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), f (p.1, -p.2) = f p) :
    ∃ η : HeightPair S, ∀ θ, heightPairField S η =ᶠ[𝓝 (t, θ)] f := by
  obtain ⟨χ, hχ, hc, hsupp, hone⟩ := exists_matching_cutoff ht.1 ht.2
  let g : PolarPoint → ℝ := fun p => χ p.1 * f p
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hpt : p.1 ∈ tsupport χ
    · exact (hχ.comp contDiff_fst).contDiffAt.mul
        (hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
          ⟨hsupp hpt, mem_univ p.2⟩))
    · apply (contDiffAt_const :
        ContDiffAt ℝ ∞ (fun _ : PolarPoint => (0 : ℝ)) p).congr_of_eventuallyEq
      filter_upwards [(continuous_fst.tendsto p).eventually
        ((isClosed_tsupport χ).isOpen_compl.mem_nhds hpt)] with q hq
      change χ q.1 * f q = 0
      rw [image_eq_zero_of_notMem_tsupport hq, zero_mul]
  have hp' : Function.Periodic g (0, Real.pi) := by
    intro p
    simp only [g, Prod.fst_add, add_zero]
    by_cases hpr : p.1 ∈ Ioo l r
    · rw [hp p ⟨hpr, mem_univ _⟩]
    · have hzero : χ p.1 = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hpr (hsupp h))
      rw [hzero, zero_mul, zero_mul]
  have he' : ∀ a θ, g (a, -θ) = g (a, θ) := by
    intro a θ
    change χ a * f (a, -θ) = χ a * f (a, θ)
    by_cases ha : a ∈ Ioo l r
    · rw [he (a, θ) ⟨ha, mem_univ _⟩]
    · have hzero : χ a = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => ha (hsupp h))
      rw [hzero, zero_mul, zero_mul]
  have hgSupport : HasCompactRadialSupport D g := by
    refine ⟨tsupport χ, hc, hsupp.trans hsub, ?_⟩
    intro a ha θ
    change χ a * f (a, θ) = 0
    rw [image_eq_zero_of_notMem_tsupport ha, zero_mul]
  obtain ⟨η, hη⟩ := n05_exists_heightPair_of_compact_test hT hS hg he' hp' hgSupport
  refine ⟨η, ?_⟩
  intro θ
  rw [hη]
  filter_upwards [(continuous_fst.tendsto (t, θ)).eventually hone] with q hq
  change χ q.1 = 1 at hq
  change χ q.1 * f q = f q
  rw [hq, one_mul]

/-- Genuine local periodicity of Lf, obtained from an actual compact height
test and locality of the totalized divergence. -/
theorem n06_correctedDivergence_periodicOn_strip
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {l r t : ℝ}
    (hsub : Ioo l r ⊆ radialCore D) (ht : t ∈ Ioo l r)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo l r ×ˢ univ))
    (hp : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), f (p + (0, Real.pi)) = f p)
    (he : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), f (p.1, -p.2) = f p) (θ : ℝ) :
    divergenceOperator (L.coefficients z) f (t, θ + Real.pi) =
      divergenceOperator (L.coefficients z) f (t, θ) := by
  obtain ⟨η, hη⟩ := n06_exists_heightPair_strip_germ hT hS hsub ht hf hp he
  have hperiod := n06_correctedDivergence_heightPair_periodicOn hS h03 hz hs η
    (p := (t, θ)) ⟨hsub ht, mem_univ _⟩
  simp only [Prod.mk_add_mk, add_zero] at hperiod
  exact (n05_divergenceOperator_congr (L.coefficients z)
    (hη (θ + Real.pi))).symm.trans
      (hperiod.trans (n05_divergenceOperator_congr (L.coefficients z) (hη θ)))

end ContinuousFlexibility.Statements
