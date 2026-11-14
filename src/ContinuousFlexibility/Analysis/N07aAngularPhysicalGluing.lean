module

public import ContinuousFlexibility.Analysis.N07aAngularInnerIntervals
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalPatch
public import ContinuousFlexibility.Analysis.N07aCanonicalPieceReconstruction

/-!
# Gluing the same actual physical representative on the open annulus

Rational inner intervals provide a countable cover. Their smooth periodic
representatives agree pointwise on overlaps because they represent the
same rough function in the original local measure. This produces one
smooth function on the whole annular open set without boundary traces or
a smooth extension through either accumulation endpoint.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {D : ReferenceData} {S : PhysicalSpacesData} {K : CanonicalData S}

theorem n07a_exists_smooth_physicalRepresentative (η : PolarPoint → ℝ)
    (hlocal : ∀ l r : ℝ, l < r → Icc l r ⊆ Ioo D.a D.b →
      ∃ v : PolarPoint → ℝ,
        ContDiffOn ℝ ∞ v (canonicalOpen S (n07aRadialIntervalData K l r) 0) ∧
        Function.Periodic v (0, Real.pi) ∧
        v =ᵐ[canonicalMeasure S (n07aRadialIntervalData K l r) 0] η) :
    ∃ v : PolarPoint → ℝ, ContDiffOn ℝ ∞ v (annularOpen D) ∧
      Function.Periodic v (0, Real.pi) ∧
      v =ᵐ[canonicalMeasure S (n07aRadialIntervalData K D.a D.b) 0] η ∧
      ∀ p, p ∉ annularOpen D → v p = 0 := by
  classical
  let left (q : ℚ × ℚ) : ℝ := q.1
  let right (q : ℚ × ℚ) : ℝ := q.2
  let valid (q : ℚ × ℚ) : Prop := D.a < left q ∧ left q < right q ∧ right q < D.b
  let J (q : ℚ × ℚ) : CanonicalData S := n07aRadialIntervalData K (left q) (right q)
  have htotal (q : ℚ × ℚ) : ∃ v : PolarPoint → ℝ, valid q →
      ContDiffOn ℝ ∞ v (canonicalOpen S (J q) 0) ∧
      Function.Periodic v (0, Real.pi) ∧ v =ᵐ[canonicalMeasure S (J q) 0] η := by
    by_cases hq : valid q
    · obtain ⟨v, hv⟩ := hlocal (left q) (right q) hq.2.1
        (fun x hx => ⟨hq.1.trans_le hx.1, hx.2.trans_lt hq.2.2⟩)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨0, fun h => (hq h).elim⟩
  choose v hv using htotal
  have hex (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
      ∃ q : ℚ × ℚ, valid q ∧ r ∈ Ioo (left q) (right q) := by
    obtain ⟨l, hal, hlr⟩ := exists_rat_btwn hr.1
    obtain ⟨s, hrs, hsb⟩ := exists_rat_btwn hr.2
    exact ⟨(l, s), ⟨hal, hlr.trans hrs, hsb⟩, hlr, hrs⟩
  let index (r : ℝ) : ℚ × ℚ := if hr : r ∈ Ioo D.a D.b then (hex r hr).choose else (0, 0)
  have hindex (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
      valid (index r) ∧ r ∈ Ioo (left (index r)) (right (index r)) := by
    simp only [index, dite_eq_left hr]
    exact (hex r hr).choose_spec
  have hcross (i j : ℚ × ℚ) (hi : valid i) (hj : valid j) :
      EqOn (v i) (v j)
        (Ioo (max (left i) (left j)) (min (right i) (right j)) ×ˢ (univ : Set ℝ)) := by
    let Q := n07aRadialIntervalData K (max (left i) (left j)) (min (right i) (right j))
    have hsubi : Ioo (max (left i) (left j)) (min (right i) (right j)) ⊆
        Ioo (left i) (right i) := fun _ hp =>
      ⟨(le_max_left _ _).trans_lt hp.1, hp.2.trans_le (min_le_left _ _)⟩
    have hsubj : Ioo (max (left i) (left j)) (min (right i) (right j)) ⊆
        Ioo (left j) (right j) := fun _ hp =>
      ⟨(le_max_right _ _).trans_lt hp.1, hp.2.trans_le (min_le_right _ _)⟩
    have hei : v i =ᵐ[canonicalMeasure S Q 0] η :=
      ((hv i hi).2.2).filter_mono (ae_mono (n07a_radialInterval_measure_mono hsubi))
    have hej : v j =ᵐ[canonicalMeasure S Q 0] η :=
      ((hv j hj).2.2).filter_mono (ae_mono (n07a_radialInterval_measure_mono hsubj))
    exact n07a_canonical_periodic_eqOn_of_ae_eq
      ((hv i hi).1.continuousOn.mono (fun _ hp => ⟨hsubi hp.1, mem_univ _⟩))
      ((hv j hj).1.continuousOn.mono (fun _ hp => ⟨hsubj hp.1, mem_univ _⟩))
      (hv i hi).2.1 (hv j hj).2.1 (hei.trans hej.symm)
  let w : PolarPoint → ℝ := fun p => if p.1 ∈ Ioo D.a D.b then v (index p.1) p else 0
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hi := hindex p.1 hp.1
    have hvp := ((hv (index p.1) hi.1).1.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hi.2, mem_univ _⟩))
    have he : w =ᶠ[𝓝 p] v (index p.1) := by
      have hnear : Ioo (left (index p.1)) (right (index p.1)) ×ˢ (univ : Set ℝ) ∈ 𝓝 p :=
        (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hi.2, mem_univ _⟩
      filter_upwards [hnear] with q hq
      have hqD : q.1 ∈ Ioo D.a D.b :=
        ⟨hi.1.1.trans hq.1.1, hq.1.2.trans hi.1.2.2⟩
      have hj := hindex q.1 hqD
      have hEq := hcross (index q.1) (index p.1) hj.1 hi.1
        ⟨⟨max_lt_iff.mpr ⟨hj.2.1, hq.1.1⟩,
          lt_min_iff.mpr ⟨hj.2.2, hq.1.2⟩⟩, mem_univ _⟩
      exact (ite_eq_left hqD).trans hEq
    exact (hvp.congr_of_eventuallyEq he).contDiffWithinAt
  · intro p
    by_cases hp : p.1 ∈ Ioo D.a D.b
    · simp only [w, Prod.fst_add, add_zero, ite_eq_left hp]
      exact (hv (index p.1) (hindex p.1 hp).1).2.1 p
    · simp only [w, Prod.fst_add, add_zero, ite_eq_right hp]
  · have hall : ∀ᵐ p ∂materialCylinderMeasure, ∀ q : ℚ × ℚ, valid q →
        p ∈ canonicalOpen S (J q) 0 → v q p = η p := by
      apply ae_all_iff.mpr
      intro q
      by_cases hq : valid q
      · exact (n07aCanonical_ae_imp (hv q hq).2.2).mono (fun p hp _ => hp)
      · exact Eventually.of_forall (fun _ hp => (hq hp).elim)
    have ha := hall.filter_mono (ae_mono (n07a_canonicalMeasure_le_cylinder
      (S := S) (J := n07aRadialIntervalData K D.a D.b) (n := 0)))
    filter_upwards [ha, n07a_canonicalOpen_ae
      (S := S) (K := n07aRadialIntervalData K D.a D.b) (m := 0)] with p hp hpD
    have hi := hindex p.1 hpD.1
    exact (ite_eq_left hpD.1).trans (hp (index p.1) hi.1 ⟨hi.2, mem_univ _⟩)
  · intro p hp
    exact ite_eq_right (fun hr => hp ⟨hr, mem_univ _⟩)

end ContinuousFlexibility.Analysis
