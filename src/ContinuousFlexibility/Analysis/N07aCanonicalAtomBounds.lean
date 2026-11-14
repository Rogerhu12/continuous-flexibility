module

public import ContinuousFlexibility.Analysis.N07aGeometryLengthBounds
public import ContinuousFlexibility.Analysis.N07aSampleJetBounds

/-!
# Actual raw atoms on the original canonical intervals

The inverse affine rescaling transfers the genuine unit-strip jets, with
all interval factors retained inside sampled subpower envelopes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

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

theorem n07a_mixedDerivative_unitInverse (m : ℕ) (f : PolarPoint → ℝ)
    (a b : ℕ) (y : PolarPoint) :
    mixedDerivative a b (f ∘ n07aCanonicalUnitInversePoint K m) y =
      (K.right m - K.left m)⁻¹ ^ a *
        mixedDerivative a b f (n07aCanonicalUnitInversePoint K m y) := by
  let c := (K.right m - K.left m)⁻¹
  let d := -(K.left m) * c
  have he (p : PolarPoint) : n07aCanonicalUnitInversePoint K m p =
      (d + c * p.1, p.2) := by
    apply Prod.ext
    · change (p.1 - K.left m) / (K.right m - K.left m) =
        -(K.left m) * (K.right m - K.left m)⁻¹ + (K.right m - K.left m)⁻¹ * p.1
      rw [div_eq_mul_inv]
      ring
    · rfl
  have hfun : f ∘ n07aCanonicalUnitInversePoint K m =
      fun p => f (d + c * p.1, p.2) := funext (fun p => congrArg f (he p))
  rw [hfun, n07a_mixedDerivative_radialAffine, ← he y]

def n07aCanonicalAtomField (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (a : CanonicalGeometry.Atom)
    (z : CanonicalGeometry.Parameter S) (m : ℕ) : PolarPoint → ℝ :=
  CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m a ∘
    n07aCanonicalUnitInversePoint K m

theorem n07a_canonicalAtomField_smooth
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hinterval : ∀ m, K.left m < K.right m) (a : CanonicalGeometry.Atom)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) :
    ContDiffOn ℝ ∞ (n07aCanonicalAtomField D T S C L K a z m) (canonicalOpen S K m) :=
  (hcur.1 z hz m a).1.comp n07aCanonicalUnitInversePoint_contDiff.contDiffOn
    (n07aCanonicalUnitInversePoint_maps (hinterval m))

theorem n07a_canonicalAtomFields_sampleJetBounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hinterval : ∀ m, K.left m < K.right m) :
    ∃ loss : ℕ, ∀ a : CanonicalGeometry.Atom,
      N07aSampleJetBounds T K (CanonicalGeometry.parameterGrading S)
        (sectorNeighborhood S base ε ε) (canonicalOpen S K) loss
        (n07aCanonicalAtomField D T S C L K a) := by
  have hb := n07a_geometryAtom_absolute_jet_bound hD hT href hcur
  let loss : ℕ := hb.choose
  have hbounds := hb.choose_spec
  have hlength := n07a_canonicalLengthInverse_subpower hD hT href
  refine ⟨loss, fun atom a b => ?_⟩
  let e : ℕ → ℝ := (hbounds (a + b)).choose
  have he := (hbounds (a + b)).choose_spec.1
  have he0 := (hbounds (a + b)).choose_spec.2.1
  have heb := (hbounds (a + b)).choose_spec.2.2
  refine ⟨fun m => (K.right m - K.left m)⁻¹ ^ a * e m,
    N07aSampleSubpower.mul hD hT (hlength.nat_pow hD hT a) he,
    fun m => mul_nonneg (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr (hinterval m)).le) _) (he0 m), ?_⟩
  intro z hz m y hy
  have hx := n07aCanonicalUnitInversePoint_maps (hinterval m) hy
  have h := heb z hz m atom ⟨n07aCanonicalUnitInversePoint K m y, hx⟩ a b le_rfl
  have hc : 0 ≤ (K.right m - K.left m)⁻¹ ^ a :=
    pow_nonneg (inv_nonneg.mpr (sub_pos.mpr (hinterval m)).le) a
  change |mixedDerivative a b
    (CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m atom ∘
      n07aCanonicalUnitInversePoint K m) y| ≤ _
  rw [n07a_mixedDerivative_unitInverse, abs_mul, abs_of_nonneg hc]
  exact (mul_le_mul_of_nonneg_left h hc).trans_eq (by ring)

end ContinuousFlexibility.Analysis
