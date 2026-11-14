module

public import ContinuousFlexibility.Analysis.N07aAngularPhysicalRepresentative
public import ContinuousFlexibility.Analysis.N07aReferenceReturn
public import ContinuousFlexibility.Analysis.N07bCanonicalSourceSymmetry

/-!
# The actual current-to-reference physical height on each piece

The same canonical unknown is decoded with the reference chart. The left
scalar remains explicit. An inverse extension may be supplied, but its
only interior hypothesis is equality with the original inverse, so every
interior formula is the literal current-to-reference coordinate change.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

def n07aReferencePieceHeight {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (K : CanonicalData S) (z : AnnularState S × ℝ)
    (g : ℕ → PolarPoint → PolarPoint) (aL : ℝ) (η : PolarPoint → ℝ)
    (m : ℕ) (p : PolarPoint) : ℝ :=
  let q := g m (K.chart (C.referenceState, 0) m p)
  K.height (C.referenceState, 0) m p *
      ((η q - aL * S.chiLeft q.1) / K.height z m q) + aL * S.chiLeft p.1

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07aReferencePieceHeight_eq_actual
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {g : ℕ → PolarPoint → PolarPoint}
    (hg : ∀ m, EqOn (K.inverseChart z m) (g m) (canonicalOpen S K m))
    (aL : ℝ) (η : PolarPoint → ℝ) (m : ℕ) :
    EqOn (n07aReferencePieceHeight C K z g aL η m)
      (n07aReferencePieceHeight C K z (K.inverseChart z) aL η m)
      (referencePhysicalPieceOpen S K m) := by
  intro p hp
  have href := h04.1.charts (C.referenceState, 0)
    (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector m
  rw [h04.1.referenceDomain m] at href
  simp only [n07aReferencePieceHeight, ← hg m (href.1 hp)]

theorem n07aReferencePieceHeight_contDiffOn
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {g : ℕ → PolarPoint → PolarPoint}
    (hg : ∀ m, EqOn (K.inverseChart z m) (g m) (canonicalOpen S K m))
    (aL : ℝ) {η : PolarPoint → ℝ} (hη : ContDiffOn ℝ ∞ η (annularOpen D)) (m : ℕ) :
    ContDiffOn ℝ ∞ (n07aReferencePieceHeight C K z g aL η m)
      (referencePhysicalPieceOpen S K m) := by
  have hc := h04.1.charts z hz hs m
  have hr := h04.1.charts (C.referenceState, 0)
    (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector m
  rw [h04.1.referenceDomain m] at hr
  have hχ : ContDiff ℝ ∞ (fun p : PolarPoint => aL * S.chiLeft p.1) :=
    contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst)
  have hT := hc.2.2.2.2.2.1.comp hr.2.2.2.2.1 hr.1
  have hmaps : MapsTo (K.inverseChart z m ∘ K.chart (C.referenceState, 0) m)
      (referencePhysicalPieceOpen S K m) (physicalPieceOpen S K z m) := hc.2.1.comp hr.1
  have hcore : MapsTo (K.inverseChart z m ∘ K.chart (C.referenceState, 0) m)
      (referencePhysicalPieceOpen S K m) (annularOpen D) :=
    fun _ hp => (h04.1.domains z hz hs m).2.2.1 (hmaps hp)
  have hraw : ContDiffOn ℝ ∞
      (n07aReferencePieceHeight C K z (K.inverseChart z) aL η m)
      (referencePhysicalPieceOpen S K m) :=
    (hr.2.2.2.2.2.2.1.mul (((hη.sub hχ.contDiffOn).comp hT hcore).div
      (hc.2.2.2.2.2.2.1.comp hT hmaps)
      (fun p hp => (hc.2.2.2.2.2.2.2 _ (hmaps hp)).1.ne'))).add hχ.contDiffOn
  exact hraw.congr (n07aReferencePieceHeight_eq_actual h01 h04 hg aL η m)

theorem n07aReferencePieceHeight_periodic_on
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {g : ℕ → PolarPoint → PolarPoint}
    (hg : ∀ m, EqOn (K.inverseChart z m) (g m) (canonicalOpen S K m))
    (aL : ℝ) {η : PolarPoint → ℝ} (hη : Function.Periodic η (0, Real.pi))
    (m : ℕ) :
    ∀ p ∈ referencePhysicalPieceOpen S K m,
      n07aReferencePieceHeight C K z g aL η m (p + (0, Real.pi)) =
        n07aReferencePieceHeight C K z g aL η m p := by
  have hc := h04.1.charts z hz hs m
  have hr := h04.1.charts (C.referenceState, 0)
    (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector m
  rw [h04.1.referenceDomain m] at hr
  intro p hp
  have hpπ : p + (0, Real.pi) ∈ referencePhysicalPieceOpen S K m := by
    exact ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
  rw [n07aReferencePieceHeight_eq_actual h01 h04 hg aL η m hpπ,
    n07aReferencePieceHeight_eq_actual h01 h04 hg aL η m hp]
  have hpr := hr.2.2.2.2.2.2.2 p hp
  have hpc := hc.2.2.2.2.2.2.2 _ (hc.2.1 (hr.1 hp))
  have hgp := n07b_canonicalInverse_add h04.1 hz hs m (hr.1 hp)
  simp only [n07aReferencePieceHeight, hpr.2.2.1, hpr.2.2.2,
    hgp, hpc.2.2.2, hη _, Prod.fst_add, add_zero]

/-- The actual transport preserves the original canonical height class,
including exactly the same left scalar. -/
theorem n07aReferencePieceHeight_canonical
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {g : ℕ → PolarPoint → PolarPoint}
    (hg : ∀ m, EqOn (K.inverseChart z m) (g m) (canonicalOpen S K m))
    (aL : ℝ) (η : PolarPoint → ℝ) {v : PolarPoint → ℝ} (m : ℕ)
    (hv : EqOn v (n07aReferencePieceHeight C K z g aL η m)
      (referencePhysicalPieceOpen S K m)) :
    EqOn (canonicalHeight S K (C.referenceState, 0) m
        (fun p => v p - aL * S.chiLeft p.1))
      (canonicalHeight S K z m (fun p => η p - aL * S.chiLeft p.1))
      (canonicalOpen S K m) := by
  have hr := h04.1.charts (C.referenceState, 0)
    (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector m
  rw [h04.1.referenceDomain m] at hr
  intro p hp
  have hpoint := hr.2.2.2.2.2.2.2 _ (hr.2.1 hp)
  simp only [canonicalHeight, hv (hr.2.1 hp), n07aReferencePieceHeight,
    hr.2.2.2.1 p hp, ← hg m hp]
  field_simp [hpoint.1.ne']
  ring

end ContinuousFlexibility.Analysis
