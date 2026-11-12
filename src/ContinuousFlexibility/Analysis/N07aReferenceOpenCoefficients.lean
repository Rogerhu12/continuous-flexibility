import ContinuousFlexibility.Analysis.N07aCanonicalRepresentationPairing

/-!
# The actual reference coefficients as open bounded-jet functions

The reference record is constructed directly from the primitive reference
atoms. It uses no perturbed state or small-neighborhood premise.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

def n07aReferenceOpenCoefficient
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (m : ℕ) (hm : K.left m < K.right m) (i : Fin 5) :
    N07aCanonicalOpenCoefficient S K m :=
  n07aCanonicalOpenCoefficientOfUnit hm
    (n07aPrincipalField K (C.referenceState, 0) m i)
    (by rw [n07aPrincipalField_unit]; exact (hJ.1 m (n07aPrincipalAtom i)).1)
    (by
      intro p hp
      have h := (hJ.1 m (n07aPrincipalAtom i)).2 p hp
      simpa only [← n07aPrincipalField_unit, Function.comp_apply] using h)
    (by
      intro a b
      rw [n07aPrincipalField_unit]
      obtain ⟨B, _, hb⟩ := hJ.2 (a + b)
      refine ⟨|B * T.E0 (T.sample (K.cell m)) ^ B|, abs_nonneg _, ?_⟩
      intro p hp
      exact (hb m (n07aPrincipalAtom i) p hp a b le_rfl).trans (le_abs_self _))

theorem n07aReferenceOpenCoefficient_value
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (m : ℕ) (hm : K.left m < K.right m) (i : Fin 5) :
    (n07aReferenceOpenCoefficient hJ m hm i).value =
      n07aPrincipalField K (C.referenceState, 0) m i := rfl

def n07aReferenceCanonicalRhs
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (m : ℕ) (hm : K.left m < K.right m)
    (U : CanonicalUnknown S K) (F : CanonicalSequence S K) : CanonicalL2 S K m :=
  let q := N07aCanonicalOpenCoefficient.constMul
    (if K.positive m then -1 else (1 : ℝ)) (n07aReferenceOpenCoefficient hJ m hm 4)
  let col := n07aReferenceScalarOpenCoefficient hJ m hm
  F m - q.mul (U.1 m) - U.2.1 • (col 0).toLp -
    U.2.2.1 • (col 1).toLp - U.2.2.2 • (col 2).toLp

end ContinuousFlexibility.Analysis
