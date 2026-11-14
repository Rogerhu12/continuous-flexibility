module

public import ContinuousFlexibility.Analysis.N07aPhysicalCanonicalPairing
public import ContinuousFlexibility.Analysis.N07aCanonicalPotentialGreen

/-!
# The actual perturbed relation on an open canonical piece

The physical witness is tested against a genuine compact pullback. The
Jacobian pairing, the cutoff column identity and interior Green pairing
give the original canonical divergence equation with its actual signed
potential and all three scalar source columns.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

theorem n07a_canonical_distribution_test_pairing
    (hab : D.a ≤ D.b) (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hχ : ContDiff ℝ ∞ S.chiLeft)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    {η f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K z U F η f)
    (hηp : Function.Periodic η (0, Real.pi))
    (hfp : Function.Periodic f (0, Real.pi))
    (a b c q : N07aCanonicalOpenCoefficient S K m)
    (col : Fin 3 → N07aCanonicalOpenCoefficient S K m)
    (ha : a.value = (K.coefficients z m).a)
    (hb : b.value = (K.coefficients z m).b)
    (hc : c.value = (K.coefficients z m).c)
    (hq : q.value = fun p => (if K.positive m then -1 else (1 : ℝ)) * K.potential z m p)
    (hcol : ∀ i, (col i).value = n07aScalarColumn D S C L K z m i)
    {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W)
    (hweak :
      (∫ r in D.a..D.b, radialAngularMean (fun θ => η (r, θ) *
        divergenceOperator (L.coefficients z) (n07aPhysicalTestPullback S K z m W) (r, θ))) +
      U.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        nuColumnField D S C z (r, θ) * n07aPhysicalTestPullback S K z m W (r, θ))) +
      U.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) *
          n07aPhysicalTestPullback S K z m W (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        f (r, θ) * n07aPhysicalTestPullback S K z m W (r, θ))) :
    (∫ p, U.1 m p * divergenceOperator (K.coefficients z m) W p ∂canonicalMeasure S K m) =
      ∫ p, (F m - q.mul (U.1 m) - U.2.1 • (col 0).toLp -
        U.2.2.1 • (col 1).toLp - U.2.2.2 • (col 2).toLp) p * W p
          ∂canonicalMeasure S K m := by
  have has : ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) :=
    ha ▸ a.smooth
  have hbs : ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) :=
    hb ▸ b.smooth
  have hcs : ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m) :=
    hc ▸ c.smooth
  have hap := ha ▸ a.periodic
  have hbp := hb ▸ b.periodic
  have hcp := hc ▸ c.periodic
  have hν : canonicalSource S K z m (nuColumnField D S C z) = (col 1).value :=
    (hcol 1).symm
  have hψ : canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode S.psi) =
      (col 2).value := (hcol 2).symm
  let g := fun p => divergenceOperator (K.coefficients z m) W p + q.value p * W p
  have hdiv := n07a_canonicalTest_divergence (K.coefficients z m)
    has hbs hcs hap hbp hcp hW
  have hqW := n07a_canonicalTest_mul_on hW q.smooth q.periodic
  have hg : CanonicalTest S K m g := n07a_canonicalTest_add hdiv hqW
  have he : EqOn (canonicalSource S K z m (divergenceOperator (L.coefficients z)
      (n07aPhysicalTestPullback S K z m W))) g (canonicalOpen S K m) := by
    simpa only [g, hq] using n07aPhysicalTestPullback_source_operator h04 hz hs hW
  have hop := n07a_pulledTest_operator_pairing hab h04 hz hs hχ hrep hηp hW hg he
  have hcolumn : EqOn (col 0).value
      (fun p => divergenceOperator (K.coefficients z m)
        (n07aCanonicalCutoffHeight S K z m) p +
          q.value p * n07aCanonicalCutoffHeight S K z m p) (canonicalOpen S K m) := by
    simpa only [hcol 0, hq] using n07aCanonicalCutoffHeight_column h04 hz hs hχ
  have hcut : (∫ p, n07aCanonicalCutoffHeight S K z m p * g p
      ∂canonicalMeasure S K m) = ∫ p, (col 0).value p * W p ∂canonicalMeasure S K m :=
    n07a_canonicalOpen_green_potential (K.coefficients z m) has hbs hcs hap hbp hcp
      (n07aCanonicalCutoffHeight_smooth h04 hz hs hχ)
      (n07aCanonicalCutoffHeight_periodic h04 hz hs) q.smooth q.periodic
      (col 0).smooth (col 0).periodic hcolumn hW
  have hiD : Integrable (fun p => U.1 m p * divergenceOperator (K.coefficients z m) W p)
      (canonicalMeasure S K m) := (Lp.memLp (U.1 m)).integrable_mul
    (n07a_canonicalTest_memLp hdiv)
  have hiQ : Integrable (fun p => U.1 m p * (q.value p * W p))
      (canonicalMeasure S K m) := (Lp.memLp (U.1 m)).integrable_mul
    (n07a_canonicalTest_memLp hqW)
  have hsplit : (∫ p, U.1 m p * g p ∂canonicalMeasure S K m) =
      (∫ p, U.1 m p * divergenceOperator (K.coefficients z m) W p ∂canonicalMeasure S K m) +
        ∫ p, U.1 m p * (q.value p * W p) ∂canonicalMeasure S K m := by
    simp only [g, mul_add]
    exact integral_add hiD hiQ
  rw [hcut, hsplit] at hop
  have hνp : ∀ p ∈ physicalPieceOpen S K z m,
      nuColumnField D S C z (p + (0, Real.pi)) = nuColumnField D S C z p := by
    apply n07a_physical_periodic_of_canonicalSource h04 hz hs
    simpa only [hν] using (col 1).periodic
  have hψp : ∀ p ∈ physicalPieceOpen S K z m,
      (S.height (3 / 4 : ℝ)).decode S.psi (p + (0, Real.pi)) =
        (S.height (3 / 4 : ℝ)).decode S.psi p := by
    apply n07a_physical_periodic_of_canonicalSource h04 hz hs
    simpa only [hψ] using (col 2).periodic
  have hiν : Integrable (fun p => canonicalSource S K z m (nuColumnField D S C z) p * W p)
      (canonicalMeasure S K m) := by
    rw [hν]
    exact (col 1).memLp.integrable_mul (n07a_canonicalTest_memLp hW)
  have hiψ : Integrable (fun p => canonicalSource S K z m
      ((S.height (3 / 4 : ℝ)).decode S.psi) p * W p) (canonicalMeasure S K m) := by
    rw [hψ]
    exact (col 2).memLp.integrable_mul (n07a_canonicalTest_memLp hW)
  have hnu := n07a_pulledTest_source_pairing hab h04 hz hs hW hνp hiν
  have haux := n07a_pulledTest_source_pairing hab h04 hz hs hW hψp hiψ
  rw [hν] at hnu
  rw [hψ] at haux
  have hsrc := n07a_pulledTest_source_pairing hab h04 hz hs hW
    (fun p _ => hfp p) (n07a_canonicalRepresentation_source_integrable hrep hW)
  rw [n07a_canonicalRepresentation_source_pairing hrep W] at hsrc
  have h := hweak
  rw [hop, hnu, haux, hsrc] at h
  have hcancel :
      (∫ p, U.1 m p * divergenceOperator (K.coefficients z m) W p ∂canonicalMeasure S K m) +
        (∫ p, U.1 m p * (q.value p * W p) ∂canonicalMeasure S K m) +
          U.2.1 * (∫ p, (col 0).value p * W p ∂canonicalMeasure S K m) +
          U.2.2.1 * (∫ p, (col 1).value p * W p ∂canonicalMeasure S K m) +
          U.2.2.2 * (∫ p, (col 2).value p * W p ∂canonicalMeasure S K m) =
        ∫ p, F m p * W p ∂canonicalMeasure S K m := by
    apply mul_left_cancel₀ (inv_ne_zero Real.pi_ne_zero)
    calc
      _ = Real.pi⁻¹ * ((∫ p, U.1 m p * divergenceOperator (K.coefficients z m) W p
          ∂canonicalMeasure S K m) + (∫ p, U.1 m p * (q.value p * W p)
          ∂canonicalMeasure S K m) + U.2.1 * (∫ p, (col 0).value p * W p
          ∂canonicalMeasure S K m)) +
          U.2.2.1 * (Real.pi⁻¹ * ∫ p, (col 1).value p * W p ∂canonicalMeasure S K m) +
          U.2.2.2 * (Real.pi⁻¹ * ∫ p, (col 2).value p * W p ∂canonicalMeasure S K m) := by ring
      _ = _ := h
  have hqpair : (∫ p, q.mul (U.1 m) p * W p ∂canonicalMeasure S K m) =
      ∫ p, U.1 m p * (q.value p * W p) ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [q.mul_ae (U.1 m)] with p hp
    rw [hp]
    ring
  have hcpair (i : Fin 3) : (∫ p, (col i).toLp p * W p ∂canonicalMeasure S K m) =
      ∫ p, (col i).value p * W p ∂canonicalMeasure S K m :=
    integral_congr_ae ((col i).toLp_ae.mono fun p hp => congrArg (· * W p) hp)
  rw [← n07aCanonicalTestPairing_apply W (n07a_canonicalTest_memLp hW)]
  simp only [map_sub, map_smul, smul_eq_mul, n07aCanonicalTestPairing_apply,
    hqpair, hcpair]
  linarith only [hcancel]

end ContinuousFlexibility.Analysis
