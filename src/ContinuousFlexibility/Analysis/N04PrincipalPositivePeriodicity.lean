import ContinuousFlexibility.Analysis.N04PrincipalPositivePotential

/-!
# Periodicity of the actual positive principal fields

The scalar interface already contains periodicity on the unit strip.
Mixed spatial derivatives preserve this property, so the exact principal
and reciprocal-height flux formulas retain it without a periodicity
assumption on any output field.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem n04PrincipalPositive_mixedDerivative_periodic
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) {m : ℕ} (hm : G.Pos η m)
    {f : PolarPoint → ℝ} (hf : ∀ q ∈ unitStrip, f (q + (0, Real.pi)) = f q)
    (i j : ℕ) : ∀ q ∈ unitStrip,
      mixedDerivative i j f (q + (0, Real.pi)) = mixedDerivative i j f q := by
  have hend := G.n04PrincipalDivided_positive_endpoints η hm
  have hΩ : canonicalOpen (G.S η) (G.V η) m = unitStrip := by
    simp only [canonicalOpen, unitStrip, hend.1, hend.2]
  rw [← hΩ] at hf ⊢
  exact n07a_mixedDerivative_periodic_on hf i j

/-- Periodicity of all four principal atoms follows from the original
geometry and pulled-field interface. -/
theorem n04PrincipalPositive_principal_periodic {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (hg : G.GeometryData η (G.Pos η) b ε) (hf : G.FieldData η b ε)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    {m : ℕ} (hm : G.Pos η m) :
    ∀ q ∈ unitStrip,
      G.atomFamily η .principalA z m (q + (0, Real.pi)) = G.atomFamily η .principalA z m q ∧
      G.atomFamily η .principalAInverse z m (q + (0, Real.pi)) =
        G.atomFamily η .principalAInverse z m q ∧
      G.atomFamily η .principalB z m (q + (0, Real.pi)) = G.atomFamily η .principalB z m q ∧
      G.atomFamily η .principalC z m (q + (0, Real.pi)) = G.atomFamily η .principalC z m q := by
  have hR := ((hg.1 .inverseRadial trivial).1 z hz m hm).2
  have hT := ((hg.1 .inverseAngleDefect trivial).1 z hz m hm).2
  have hRr := G.n04PrincipalPositive_mixedDerivative_periodic η hm hR 1 0
  have hRt := G.n04PrincipalPositive_mixedDerivative_periodic η hm hR 0 1
  have hTr := G.n04PrincipalPositive_mixedDerivative_periodic η hm hT 1 0
  have hTt := G.n04PrincipalPositive_mixedDerivative_periodic η hm hT 0 1
  have hH := (hg.2.1 z hz m hm).2
  have ha := ((hf.1 0).1 z hz m trivial).2
  have hb := ((hf.1 1).1 z hz m trivial).2
  have hc := ((hf.1 2).1 z hz m trivial).2
  intro q hq
  have hq' : q + (0, Real.pi) ∈ unitStrip := by
    exact ⟨by simpa only [Prod.fst_add, add_zero] using hq.1, mem_univ _⟩
  have hform := G.n04PrincipalPositive_principal_unit_formula h η hz hm hq
  have hform' := G.n04PrincipalPositive_principal_unit_formula h η hz hm hq'
  dsimp only at hform hform'
  rw [hRr q hq, hRt q hq, hTr q hq, hTt q hq, hH q hq,
    ha q hq, hb q hq, hc q hq] at hform'
  have hA := hform'.1.trans hform.1.symm
  have hB := hform'.2.1.trans hform.2.1.symm
  have hC := hform'.2.2.trans hform.2.2.symm
  refine ⟨hA, ?_, hB, hC⟩
  change (G.atomFamily η .principalA z m (q + (0, Real.pi)))⁻¹ =
    (G.atomFamily η .principalA z m q)⁻¹
  rw [hA]

/-- The positive potential inherits periodicity from the same fields
after their spatial regularity has been constructed. -/
theorem n04PrincipalPositive_potential_periodic {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (hg : G.GeometryData η (G.Pos η) b ε) (hf : G.FieldData η b ε)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    {m : ℕ} (hm : G.Pos η m)
    (ha : ContDiffOn ℝ ∞ (G.atomFamily η .principalA z m) unitStrip)
    (hb : ContDiffOn ℝ ∞ (G.atomFamily η .principalB z m) unitStrip)
    (hc : ContDiffOn ℝ ∞ (G.atomFamily η .principalC z m) unitStrip) :
    ∀ q ∈ unitStrip,
      G.atomFamily η .potential z m (q + (0, Real.pi)) = G.atomFamily η .potential z m q := by
  let V : PolarPoint → ℝ := fun p => (G.pulledHeight η z m p)⁻¹
  let FR : PolarPoint → ℝ := fun p =>
    G.atomFamily η .principalA z m p * mixedDerivative 1 0 V p +
      G.atomFamily η .principalB z m p * mixedDerivative 0 1 V p
  let FT : PolarPoint → ℝ := fun p =>
    G.atomFamily η .principalB z m p * mixedDerivative 1 0 V p +
      G.atomFamily η .principalC z m p * mixedDerivative 0 1 V p
  have hprincipal := G.n04PrincipalPositive_principal_periodic h η hg hf hz hm
  have hH := (hg.2.1 z hz m hm).2
  have hV : ∀ q ∈ unitStrip, V (q + (0, Real.pi)) = V q := by
    intro q hq
    exact congrArg (fun t : ℝ => t⁻¹) (hH q hq)
  have hVr := G.n04PrincipalPositive_mixedDerivative_periodic η hm hV 1 0
  have hVt := G.n04PrincipalPositive_mixedDerivative_periodic η hm hV 0 1
  have hFR : ∀ q ∈ unitStrip, FR (q + (0, Real.pi)) = FR q := by
    intro q hq
    dsimp only [FR]
    rw [(hprincipal q hq).1, (hprincipal q hq).2.2.1, hVr q hq, hVt q hq]
  have hFT : ∀ q ∈ unitStrip, FT (q + (0, Real.pi)) = FT q := by
    intro q hq
    dsimp only [FT]
    rw [(hprincipal q hq).2.2.1, (hprincipal q hq).2.2.2, hVr q hq, hVt q hq]
  have hFRr := G.n04PrincipalPositive_mixedDerivative_periodic η hm hFR 1 0
  have hFTt := G.n04PrincipalPositive_mixedDerivative_periodic η hm hFT 0 1
  intro q hq
  have hq' : q + (0, Real.pi) ∈ unitStrip := by
    exact ⟨by simpa only [Prod.fst_add, add_zero] using hq.1, mem_univ _⟩
  have hform := G.n04PrincipalPositive_potential_unit_formula h η hz hm ha hb hc hq
  have hform' := G.n04PrincipalPositive_potential_unit_formula h η hz hm ha hb hc hq'
  change G.atomFamily η .potential z m q = G.pulledHeight η z m q *
    (mixedDerivative 1 0 FR q + mixedDerivative 0 1 FT q) at hform
  change G.atomFamily η .potential z m (q + (0, Real.pi)) =
    G.pulledHeight η z m (q + (0, Real.pi)) *
      (mixedDerivative 1 0 FR (q + (0, Real.pi)) +
        mixedDerivative 0 1 FT (q + (0, Real.pi))) at hform'
  rw [hH q hq, hFRr q hq, hFTt q hq] at hform'
  exact hform'.trans hform.symm

end N04RealizationGauge

end ContinuousFlexibility.Analysis
