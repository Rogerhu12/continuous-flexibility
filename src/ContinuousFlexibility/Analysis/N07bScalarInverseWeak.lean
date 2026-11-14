module

public import ContinuousFlexibility.Analysis.N07bStrongRelation
public import ContinuousFlexibility.Analysis.MaterialHeightRegularity

/-!
# The actual scalar inverse satisfies the weak relation

The source and height regularity used by the Green bridge are discharged
from the already constructed physical spaces. The coefficient smoothness
and angular periodicity remain explicit analytic premises. The conclusion
does not supply a canonical source norm or fixed-graph membership.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

/-- The N07a scalar solution, with the same physical source and scalars,
satisfies the repaired canonical weak relation whenever it is represented.
All height/source regularity is obtained from the actual Sobolev model. -/
theorem n07b_scalarInverse_perturbedCanonicalRelation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {L : ReturnCorrectionData S} {G : ScalarInverseData S}
    {base : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hG : ScalarInverseProperties D S C L G base ε)
    (hab : D.a < D.b)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (f : S.Source)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    (ha : ContDiffOn ℝ ∞ (L.coefficients z).a (annularOpen D))
    (hb : ContDiffOn ℝ ∞ (L.coefficients z).b (annularOpen D))
    (hc : ContDiffOn ℝ ∞ (L.coefficients z).c (annularOpen D))
    (hBp : ∀ r ∈ radialCore D,
      Function.Periodic (fun θ => (L.coefficients z).b (r, θ)) Real.pi)
    (hCp : ∀ r ∈ radialCore D,
      Function.Periodic (fun θ => (L.coefficients z).c (r, θ)) Real.pi)
    (hrep : HasCanonicalRepresentation D S C K z U F
      (heightPairField S (G.G z f).1) ((S.height (3 / 4 : ℝ)).decode f.val))
    (hscalar : U.2.2.1 = (G.G z f).2) (hcompat : U.2.2.2 = 0) :
    PerturbedCanonicalRelation D S C K L z U F := by
  have hη : ContDiff ℝ ∞ (heightPairField S (G.G z f).1) :=
    physical_height_with_cutoff_contDiff hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) (G.G z f).1.1 (G.G z f).1.2
  have hf : ContDiffOn ℝ ∞ ((S.height (3 / 4 : ℝ)).decode f.val)
      (annularOpen D) :=
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 f.val).1
  have hfp : Function.Periodic ((S.height (3 / 4 : ℝ)).decode f.val) (0, Real.pi) :=
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 f.val).2.2.1
  have hmember : HeightMember D T (3 / 4 : ℝ)
      ((S.height (3 / 4 : ℝ)).decode (G.G z f).1.1) :=
    (hS.1 (3 / 4 : ℝ)).2.2.2.1 (G.G z f).1.1
  have hηp : Function.Periodic (heightPairField S (G.G z f).1) (0, Real.pi) := by
    rintro ⟨r, θ⟩
    have hp := hmember.2.2.1 (r, θ)
    change (S.height (3 / 4 : ℝ)).decode (G.G z f).1.1 (r + 0, θ + Real.pi) =
      (S.height (3 / 4 : ℝ)).decode (G.G z f).1.1 (r, θ) at hp
    simp only [add_zero] at hp
    change (S.height (3 / 4 : ℝ)).decode (G.G z f).1.1 (r + 0, θ + Real.pi) +
        (G.G z f).1.2 * S.chiLeft (r + 0) =
      (S.height (3 / 4 : ℝ)).decode (G.G z f).1.1 (r, θ) +
        (G.G z f).1.2 * S.chiLeft r
    simp only [add_zero, hp]
  obtain ⟨hrow, hstrong⟩ := hG.1 z hz hsector f
  apply n07b_perturbedCanonicalRelation_of_strong
    hab ha hb hc hη hf hBp hCp hηp hfp hrep hrow hcompat
  intro p hp
  rw [hscalar]
  exact hstrong p hp

end ContinuousFlexibility.Analysis
