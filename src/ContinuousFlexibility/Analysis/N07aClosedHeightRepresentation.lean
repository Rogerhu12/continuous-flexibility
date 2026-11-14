module

public import ContinuousFlexibility.Analysis.N07aClosedPhysicalHeight
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalAEPairing

/-!
# The genuine closed reference height represents the original graph field

The scalar cutoff is restored before comparison with the original graph.
The half-period change of variables is extended to the full test period using
periodicity on the actual reference strip.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open N07aClosedJets
open scoped ContDiff Topology

/-- Local periodicity on a fixed strip suffices to extend its a.e. equality
from the canonical half period to the original radial-test period. -/
theorem n07a_fullPeriod_ae_of_half_on_strip {l r : ℝ}
    {f g : PolarPoint → ℝ}
    (hf : ∀ p ∈ openStrip l r, f (p + (0, Real.pi)) = f p)
    (hg : ∀ p ∈ openStrip l r, g (p + (0, Real.pi)) = g p)
    (he : f =ᵐ[volume.restrict (Ioo l r ×ˢ Ioc (0 : ℝ) Real.pi)] g) :
    f =ᵐ[volume.restrict (Ioo l r ×ˢ Ioc (0 : ℝ) (2 * Real.pi))] g := by
  classical
  let f' := (openStrip l r).indicator f
  let g' := (openStrip l r).indicator g
  have hind (v : PolarPoint → ℝ)
      (hv : ∀ p ∈ openStrip l r, v (p + (0, Real.pi)) = v p) :
      Function.Periodic ((openStrip l r).indicator v) (0, Real.pi) := by
    intro p
    have hmem : p + (0, Real.pi) ∈ openStrip l r ↔ p ∈ openStrip l r := by
      simp only [openStrip, mem_prod, mem_Ioo, mem_univ, and_true,
        Prod.fst_add, add_zero]
    by_cases hp : p ∈ openStrip l r
    · rw [indicator_of_mem hp, indicator_of_mem (hmem.mpr hp), hv p hp]
    · rw [indicator_of_notMem hp, indicator_of_notMem (fun h => hp (hmem.mp h))]
  have hmem₁ : ∀ᵐ p ∂volume.restrict (Ioo l r ×ˢ Ioc (0 : ℝ) Real.pi),
      p ∈ openStrip l r :=
    (ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)).mono
      (fun _ hp => ⟨hp.1, mem_univ _⟩)
  have he' : f' =ᵐ[(volume.restrict (Ioo l r)).prod angleMeasure] g' := by
    rw [angleMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod]
    filter_upwards [he, hmem₁] with p hp hpm
    exact (indicator_of_mem hpm f).trans (hp.trans (indicator_of_mem hpm g).symm)
  have hfull := n07a_fullPeriod_ae_of_half (hind f hf) (hind g hg) he'
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hfull
  filter_upwards [hfull,
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpm
  have hm : p ∈ openStrip l r := ⟨hpm.1, mem_univ _⟩
  exact (indicator_of_mem hm f).symm.trans (hp.trans (indicator_of_mem hm g))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The full reference field, including the prescribed scalar cutoff. -/
def n07aClosedReferenceHeight (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (aL : ℝ) (m : ℕ) {v : PolarPoint → ℝ}
    (J : ClosedJetTower (K.left m) (K.right m) v) (p : PolarPoint) : ℝ :=
  n07aClosedPhysicalHeight K (C.referenceState, 0) m J p + aL * S.chiLeft p.1

theorem n07aClosedReferenceHeight_contDiffOn
    (hS : IsPhysicalSpaces D T S)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (aL : ℝ) (m : ℕ) {v : PolarPoint → ℝ}
    (J : ClosedJetTower (K.left m) (K.right m) v) :
    ContDiffOn ℝ ∞ (n07aClosedReferenceHeight S C K aL m J)
      (closedStrip (K.physicalLeft m) (K.physicalRight m)) :=
  (n07aClosedPhysicalHeight_reference_contDiffOn h04 href hsref m J).add
    ((contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst)).contDiffOn)

theorem n07aClosedReferenceHeight_periodic
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (aL : ℝ) (m : ℕ) {v : PolarPoint → ℝ} (hvp : Function.Periodic v (0, Real.pi))
    (J : ClosedJetTower (K.left m) (K.right m) v) :
    ∀ p ∈ closedStrip (K.physicalLeft m) (K.physicalRight m),
      n07aClosedReferenceHeight S C K aL m J (p + (0, Real.pi)) =
        n07aClosedReferenceHeight S C K aL m J p := by
  intro p hp
  simp only [n07aClosedReferenceHeight, Prod.fst_add, add_zero,
    n07aClosedPhysicalHeight_reference_periodic h04 href hsref m hvp J p hp]

theorem n07aClosedReferenceHeight_ae
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K} {η f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K (C.referenceState, 0) U F η f)
    (hηp : Function.Periodic η (0, Real.pi))
    (m : ℕ) {v : PolarPoint → ℝ}
    (hv : (U.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] v)
    (hvp : Function.Periodic v (0, Real.pi))
    (J : ClosedJetTower (K.left m) (K.right m) v) :
    n07aClosedReferenceHeight S C K U.2.1 m J =ᵐ[
      volume.restrict (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ
        Ioc (0 : ℝ) (2 * Real.pi))] η := by
  have hheight := n07aPhysicalHeightRepresentative_ae h04 href hsref hrep m hv
  have hclosed := n07aClosedPhysicalHeight_eqOn h04 href hsref m J
  have he : n07aClosedReferenceHeight S C K U.2.1 m J =ᵐ[
      n07aPhysicalMeasure S K (C.referenceState, 0) m] η := by
    filter_upwards [hheight, n07aPhysicalMeasure_ae h04 href hsref m] with p hp hpm
    change n07aClosedPhysicalHeight K (C.referenceState, 0) m J p +
      U.2.1 * S.chiLeft p.1 = η p
    rw [hclosed hpm, hp]
    ring
  rw [n07aPhysicalMeasure_reference h04 m] at he
  exact n07a_fullPeriod_ae_of_half_on_strip
    (fun p hp => n07aClosedReferenceHeight_periodic h04 href hsref U.2.1 m hvp J p
      ⟨Ioo_subset_Icc_self hp.1, hp.2⟩)
    (fun p _ => hηp p) he

end ContinuousFlexibility.Analysis
