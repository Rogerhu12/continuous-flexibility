import ContinuousFlexibility.Analysis.N07aAngularPhysicalMeasure
import ContinuousFlexibility.Analysis.N07aAngularPhysicalPatch

/-!
# The actual physical source is determined by its canonical source classes

The real chart Jacobian and height are nonzero. Equality of canonical
source classes therefore implies equality of physical sources on each
piece. The original a.e. physical cover then gives the same equality on
every inner strip, with no integrability or regularity premise on the
arbitrarily chosen rough representative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K J : CanonicalData S}
  {base loss n : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07a_physical_piecewise_ae_eq
    (h04 : N04Properties D T S C L K base loss ε)
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo D.a D.b)
    {f g : PolarPoint → ℝ}
    (he : ∀ i, f =ᵐ[canonicalMeasure S (n07aPhysicalIntervalData K) i] g) :
    f =ᵐ[canonicalMeasure S J n] g := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  obtain ⟨E, hE, hcover⟩ := h04.2.2.2.2.2.2.1
  have hEr : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ E := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hE
  have hEr' := hEr.filter_mono (ae_mono (Measure.restrict_le_self
    (μ := (volume : Measure ℝ)) (s := Ioo (J.left n) (J.right n))))
  have hEp : ∀ᵐ p ∂canonicalMeasure S J n, p.1 ∉ E := by
    rw [n07aCanonicalMeasure_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae hEr'
  have hcells : ∀ᵐ p ∂materialCylinderMeasure, ∀ i,
      p ∈ physicalPieceOpen S K i → f p = g p :=
    ae_all_iff.mpr (fun i => n07aCanonical_ae_imp (he i))
  have hc := hcells.filter_mono (ae_mono
    (n07a_canonicalMeasure_le_cylinder (S := S) (J := J) (n := n)))
  filter_upwards [hc, hEp, n07a_canonicalOpen_ae (S := S) (K := J) (m := n)]
    with p hpc hpE hpJ
  obtain ⟨i, hi, _⟩ := hcover p.1 ⟨hsub hpJ.1, hpE⟩
  exact hpc i ⟨hi, mem_univ _⟩

theorem n07a_canonicalSource_ae_injective_piece
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {f g : PolarPoint → ℝ}
    (he : canonicalSource S K z m f =ᵐ[canonicalMeasure S K m] canonicalSource S K z m g) :
    f =ᵐ[canonicalMeasure S (n07aPhysicalIntervalData K) m] g := by
  have hae := n07a_chart_ae_pullback h04 hz hs m he
  obtain ⟨_, _, _, hpoint⟩ := n07a_physicalHalfGeometry h04 hz hs m
  filter_upwards [hae, ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)]
    with p hp hpQ
  have hd := hpoint p hpQ
  simp only [canonicalSource, hd.1] at hp
  exact mul_left_cancel₀ hd.2.1 ((div_left_inj' (abs_ne_zero.mpr hd.2.2)).mp hp)

/-- The source in the original weak relation agrees with the prescribed
physical source whenever they encode the same actual canonical sequence. -/
theorem n07a_sourceRepresentation_local_unique
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo D.a D.b)
    {F : CanonicalSequence S K} {f g : PolarPoint → ℝ}
    (hf : ∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] canonicalSource S K z m f)
    (hg : ∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] canonicalSource S K z m g) :
    f =ᵐ[canonicalMeasure S J n] g :=
  n07a_physical_piecewise_ae_eq h04 hsub
    (fun m => n07a_canonicalSource_ae_injective_piece h04 hz hs m ((hf m).symm.trans (hg m)))

end ContinuousFlexibility.Analysis
