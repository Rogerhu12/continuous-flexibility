module

public import ContinuousFlexibility.Analysis.N07aGeometryLengthBounds
public import ContinuousFlexibility.Analysis.N07aSampleJetBounds

/-!
# Quantitative actual principal jets on the original canonical intervals

The genuine unit-piece bounds are transferred by the exact affine jet
formula. All powers of inverse interval length stay in one subpower
envelope until the complete normal expression is formed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

theorem n07a_principalFields_sampleJetBounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hinterval : ∀ m, K.left m < K.right m) :
    ∃ loss : ℕ, ∀ k : Fin 5,
      N07aSampleJetBounds T K (CanonicalGeometry.parameterGrading S)
        (sectorNeighborhood S base ε ε) (canonicalOpen S K) loss
        (fun z m => n07aPrincipalField K (liftSectorParameter S C z) m k) := by
  have hb := n07a_geometryAtom_absolute_jet_bound hD hT href hcur
  let loss : ℕ := hb.choose
  have hbounds := hb.choose_spec
  have hlength := n07a_canonicalLengthInverse_subpower hD hT href
  refine ⟨loss, fun k a b => ?_⟩
  let e : ℕ → ℝ := (hbounds (a + b)).choose
  have he := (hbounds (a + b)).choose_spec.1
  have he0 := (hbounds (a + b)).choose_spec.2.1
  have heb := (hbounds (a + b)).choose_spec.2.2
  refine ⟨fun m => (K.right m - K.left m)⁻¹ ^ a * e m,
    N07aSampleSubpower.mul hD hT (hlength.nat_pow hD hT a) he,
    fun m => mul_nonneg (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr (hinterval m)).le) _) (he0 m), ?_⟩
  intro z hz m y hy
  let f := n07aPrincipalField K (liftSectorParameter S C z) m k
  let x := n07aCanonicalUnitInversePoint K m y
  have hx : x ∈ CanonicalGeometry.unitStrip :=
    n07aCanonicalUnitInversePoint_maps (hinterval m) hy
  have hunit : |mixedDerivative a b (f ∘ CanonicalGeometry.canonicalUnitPoint K m) x| ≤
      e m * (1 + CanonicalGeometry.parameterGrading S (a + b + loss) z) := by
    have heq := congrArg (fun g : PolarPoint → ℝ => mixedDerivative a b g x)
      (n07aPrincipalField_unit (D := D) (T := T) (C := C) (L := L) (K := K)
        (liftSectorParameter S C z) m k)
    exact (congrArg abs heq).le.trans (heb z hz m (n07aPrincipalAtom k) ⟨x, hx⟩ a b le_rfl)
  have hc : 0 ≤ (K.right m - K.left m)⁻¹ ^ a :=
    pow_nonneg (inv_nonneg.mpr (sub_pos.mpr (hinterval m)).le) a
  rw [n07aCanonicalUnit_jet_inverse m (hinterval m) f a b y, abs_mul, abs_of_nonneg hc]
  exact (mul_le_mul_of_nonneg_left hunit hc).trans_eq (by ring)

end ContinuousFlexibility.Analysis
