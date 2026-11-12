import ContinuousFlexibility.Analysis.N07aCanonicalEquationPairing

/-!
# The actual perturbed relation on an open canonical piece

The physical witness is tested against a genuine compact pullback. The
Jacobian pairing, the cutoff column identity and interior Green pairing
give the original canonical divergence equation with its actual signed
potential and all three scalar source columns.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

theorem n07a_perturbedCanonical_distribution_of_coefficients
    (hab : D.a ≤ D.b) (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hχ : ContDiff ℝ ∞ S.chiLeft)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    (hrel : PerturbedCanonicalRelation D S C K L z U F)
    (a b c q : N07aCanonicalOpenCoefficient S K m)
    (col : Fin 3 → N07aCanonicalOpenCoefficient S K m)
    (ha : a.value = (K.coefficients z m).a)
    (hb : b.value = (K.coefficients z m).b)
    (hc : c.value = (K.coefficients z m).c)
    (hq : q.value = fun p => (if K.positive m then -1 else (1 : ℝ)) * K.potential z m p)
    (hcol : ∀ i, (col i).value = n07aScalarColumn D S C L K z m i) :
    N07aCanonicalDistributionEquation S K m (K.coefficients z m) (U.1 m)
      (F m - q.mul (U.1 m) - U.2.1 • (col 0).toLp -
        U.2.2.1 • (col 1).toLp - U.2.2.2 • (col 2).toLp) := by
  obtain ⟨η, f, hrep, hηp, hfp, _, hweak⟩ := hrel
  intro W hW
  exact n07a_canonical_distribution_test_pairing hab h04 hz hs hχ
    hrep hηp hfp a b c q col ha hb hc hq hcol hW
    (hweak _ (n07aPhysicalTestPullback_test h04 hz hs hW).1)

end ContinuousFlexibility.Analysis
