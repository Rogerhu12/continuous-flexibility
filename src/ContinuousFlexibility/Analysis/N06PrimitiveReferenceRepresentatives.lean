module

public import ContinuousFlexibility.Analysis.N06IntervalC1Representative
public import ContinuousFlexibility.Analysis.N07aReferenceUnitJets
public import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient

/-!
# Reference coefficients with genuine endpoint representatives

The retained reference jets give bounded second derivatives of the unit
rays. Their C1 representatives are transported to the original canonical
interval, with its actual affine length. Radiality identifies the original
open-strip coefficients. Raw endpoint values are never treated as traces.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

private theorem n06_referenceUnitAtom_C1_representative
    (hJ : ReferenceJets D T S C L K) (m : ℕ) (a : Atom) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 1 g ∧
      EqOn (n07aReferenceUnitAtom D T S C L K m a) g (Ioo (0 : ℝ) 1) := by
  obtain ⟨A, _hA, hb⟩ := n07aReferenceUnitAtom_twoJet_bound hJ
  apply n06_exists_contDiff_one_representative_of_bounded_second_deriv
    (n07aReferenceUnitAtom_contDiff hJ m a)
  intro x hx
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hb m a x hx 2 le_rfl

/-- The actual reference operator has a global C1 leading coefficient
and continuous lower-order representatives on every original interval. -/
theorem n06_primitiveReference_coefficients_representatives
    (hJ : ReferenceJets D T S C L K) (hP : ReferencePrincipal T S C K)
    (m : ℕ) (hlen : K.left m < K.right m) :
    ∃ a c V : ℝ → ℝ, ContDiff ℝ 1 a ∧ Continuous c ∧ Continuous V ∧
      EqOn (K.coefficients (C.referenceState, 0) m).a (fun p => a p.1)
        (canonicalOpen S K m) ∧
      EqOn (K.coefficients (C.referenceState, 0) m).b 0 (canonicalOpen S K m) ∧
      EqOn (K.coefficients (C.referenceState, 0) m).c (fun p => c p.1)
        (canonicalOpen S K m) ∧
      EqOn (K.potential (C.referenceState, 0) m) (fun p => V p.1)
        (canonicalOpen S K m) := by
  obtain ⟨a, ha, hea⟩ := n06_referenceUnitAtom_C1_representative hJ m .principalA
  obtain ⟨c, hc, hec⟩ := n06_referenceUnitAtom_C1_representative hJ m .principalC
  obtain ⟨v, hv, hev⟩ := n06_referenceUnitAtom_C1_representative hJ m .potential
  let q : ℝ → ℝ := fun y => (y - K.left m) / (K.right m - K.left m)
  have hq : ContDiff ℝ 1 q := (contDiff_id.sub contDiff_const).div_const _
  have hqmem {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
      q p.1 ∈ Ioo (0 : ℝ) 1 :=
    (n07aCanonicalUnitInversePoint_maps hlen hp).1
  have hpoint (y : ℝ) : canonicalUnitPoint K m (q y, 0) = (y, 0) :=
    n07aCanonicalUnitPoint_inverse hlen (y, 0)
  have hA (y : ℝ) : n07aReferenceUnitAtom D T S C L K m .principalA (q y) =
      (K.coefficients (C.referenceState, 0) m).a (y, 0) := by
    change (K.coefficients (C.referenceState, 0) m).a
      (canonicalUnitPoint K m (q y, 0)) = _
    exact congrArg (K.coefficients (C.referenceState, 0) m).a (hpoint y)
  have hC (y : ℝ) : n07aReferenceUnitAtom D T S C L K m .principalC (q y) =
      (K.coefficients (C.referenceState, 0) m).c (y, 0) := by
    change (K.coefficients (C.referenceState, 0) m).c
      (canonicalUnitPoint K m (q y, 0)) = _
    exact congrArg (K.coefficients (C.referenceState, 0) m).c (hpoint y)
  have hV (y : ℝ) : n07aReferenceUnitAtom D T S C L K m .potential (q y) =
      K.potential (C.referenceState, 0) m (y, 0) := by
    change K.potential (C.referenceState, 0) m (canonicalUnitPoint K m (q y, 0)) = _
    exact congrArg (K.potential (C.referenceState, 0) m) (hpoint y)
  refine ⟨a ∘ q, c ∘ q, v ∘ q, ha.comp hq, (hc.comp hq).continuous,
    (hv.comp hq).continuous, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (hP.1 m p hp).2.2.1.trans ((hA p.1).symm.trans (hea (hqmem hp)))
  · intro p hp
    exact (hP.1 m p hp).2.1
  · intro p hp
    exact (hP.1 m p hp).2.2.2.1.trans ((hC p.1).symm.trans (hec (hqmem hp)))
  · intro p hp
    exact (hP.1 m p hp).2.2.2.2.trans ((hV p.1).symm.trans (hev (hqmem hp)))

end ContinuousFlexibility.Statements
