import ContinuousFlexibility.Radial.InnerGapPhysicalPoisson
import ContinuousFlexibility.Radial.InnerGapJointRealization

/-!
# The same gap inverse, Poisson map, and matrix in the finite weak domain

One closed Dirichlet witness is used for each arbitrary physical L²
source. Adding the actual Poisson field gives the prescribed canonical
trace, the common physical weak equation, and the full outgoing flux
Λξ − P†F computed on the fixed affine hats.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

theorem innerGapAffineEnergy_physical_pair (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b : ℝ} (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (j : ℝ) (p : Fin 2 → ℝ → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i))
    (q : InnerGapEnergyTriple D) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ((innerGapAffineEnergy D hw ha hcore hpos j p hp q ξ).fst,
      (innerGapAffineEnergy D hw ha hcore hpos j p hp q ξ).snd.fst) =
      (q.fst, q.snd.fst) + innerGapPoissonH1 D hw.continuous ha hcore hpos p hp ξ := by
  apply Prod.ext
  · simp only [innerGapAffineEnergy, WithLp.toLp_fst, Prod.fst_add,
      innerGapPoissonH1_value]
  · simp only [innerGapAffineEnergy, WithLp.toLp_snd, WithLp.add_fst,
      innerGapPoissonH1_energy, WithLp.toLp_fst, Prod.snd_add]

theorem innerGapAffineEnergy_physical_potential (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b : ℝ} (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (j : ℝ) (p : Fin 2 → ℝ → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i))
    (q : InnerGapEnergyTriple D) (hq : q ∈ innerGapFormSpace D j a b)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    (innerGapAffineEnergy D hw ha hcore hpos j p hp q ξ).snd.snd =
      innerGapPotentialMultiplier D hw hpos j
        (innerGapAffineEnergy D hw ha hcore hpos j p hp q ξ).fst := by
  have hpot := innerGapFormSpace_potential D hw hpos j q hq
  simp only [innerGapAffineEnergy, WithLp.toLp_fst, WithLp.toLp_snd,
    WithLp.add_snd, innerGapPoissonH1_energy, hpot, map_add,
    innerGapPoissonH1_value]

/-- The local Dirichlet equation for its actual derivative witness,
against every common physical zero-endpoint test. -/
theorem innerGapFormWitness_weakResidual (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b : ℝ}
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ)
    (q : InnerGapEnergyTriple D) (hq : q ∈ innerGapFormSpace D j a b)
    (F : RadialModeL2 D)
    (hform : ∀ r ∈ innerGapFormSpace D j a b, ⟪F, r.fst⟫_ℝ = ⟪q.snd, r.snd⟫_ℝ)
    (r : InnerRadialH1Pair D) (hr : r ∈ innerRadialH1Zero D a b) :
    innerRadialWeakResidual D (q.fst, q.snd.fst)
      (innerGapPotentialMultiplier D hw hpos j
        (innerGapPotentialMultiplier D hw hpos j q.fst)) F 0 0 r = 0 := by
  let M := innerGapPotentialMultiplier D hw hpos j
  have he := hform (innerGapPotentialLift D M r)
    (innerGapPotentialLift_mem D hw hpos j r hr)
  have hpot := innerGapFormSpace_potential D hw hpos j q hq
  have hvalue : ⟪F, r.1⟫_ℝ = ⟪q.snd.fst, r.2⟫_ℝ + ⟪M q.fst, M r.1⟫_ℝ := by
    simpa only [innerGapPotentialLift_apply, WithLp.toLp_fst, WithLp.toLp_snd,
      WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd, hpot] using he
  dsimp only [innerRadialWeakResidual]
  rw [innerGapPotentialMultiplier_square_inner]
  simp only [zero_mul, add_zero]
  linarith

/-- All common-domain and canonical-flux identities for one actual
Dirichlet witness plus the actual Poisson correction. -/
theorem innerGapAffineEnergy_physical (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b j : ℝ} (hab : a < b) (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) D.w (p i) r = 0)
    (q : InnerGapEnergyTriple D) (hq : q ∈ innerGapFormSpace D j a b)
    (F : RadialModeL2 D)
    (hform : ∀ r ∈ innerGapFormSpace D j a b, ⟪F, r.fst⟫_ℝ = ⟪q.snd, r.snd⟫_ℝ)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    let Q := innerGapAffineEnergy D hw ha hcore hpos j p hp q ξ
    let U := (Q.fst, Q.snd.fst)
    let V := innerGapPotentialMultiplier D hw hpos j
      (innerGapPotentialMultiplier D hw hpos j Q.fst)
    U ∈ innerRadialH1Domain D hw.continuous ha hcore hpos ∧
      innerRadialH1Trace D hw.continuous ha hcore hpos U = (fun i => ξ i) ∧
      InnerRadialPotentialClass D j a b U.1 V ∧
      (∀ r ∈ innerRadialH1Zero D a b, innerRadialWeakResidual D U V F 0 0 r = 0) ∧
      ∀ i : Fin 2,
        innerRadialWeakResidual D U V F 0 0
          (innerRadialAffineUnitPair D hw.continuous ha hcore hpos i) =
          (innerGapFluxOperator D.w a b p ξ -
            (innerGapPoissonL2 D hw.continuous ha hcore
              (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) p hp).adjoint F) i := by
  let M := innerGapPotentialMultiplier D hw hpos j
  let P := innerGapPoissonH1 D hw.continuous ha hcore hpos p hp ξ
  let Q := innerGapAffineEnergy D hw ha hcore hpos j p hp q ξ
  have hpair : (Q.fst, Q.snd.fst) = (q.fst, q.snd.fst) + P :=
    innerGapAffineEnergy_physical_pair D hw ha hcore hpos j p hp q ξ
  have hQvalue : Q.fst = q.fst + P.1 := congrArg Prod.fst hpair
  have hQgrad : Q.snd.fst = q.snd.fst + P.2 := congrArg Prod.snd hpair
  have hpot : Q.snd.snd = M Q.fst :=
    innerGapAffineEnergy_physical_potential D hw ha hcore hpos j p hp q hq ξ
  have hzero : (Q.fst, Q.snd.fst) -
      innerRadialAffineLift D hw.continuous ha hcore hpos (fun i => ξ i) ∈
        innerRadialH1Zero D a b := by
    rw [hpair, add_sub_assoc]
    exact (innerRadialH1Zero D a b).add_mem
      (innerGapFormSpace_radialH1 D j a b q hq)
      (innerGapPoissonH1_sub_affine D hw.continuous ha hcore hpos p hp hab hb ξ)
  have htrace := (innerRadialH1Domain_trace_iff D hw.continuous hab ha hcore hpos
    (Q.fst, Q.snd.fst) (fun i => ξ i)).mpr hzero
  have hweak : ∀ r ∈ innerRadialH1Zero D a b,
      innerRadialWeakResidual D (Q.fst, Q.snd.fst) (M (M Q.fst)) F 0 0 r = 0 := by
    intro r hr
    have hD := innerGapFormWitness_weakResidual D hw hpos j q hq F hform r hr
    have hP := innerGapPoissonH1_weakResidual D hw hab.le ha hcore hpos hslope p hp heq ξ r hr
    dsimp only [innerRadialWeakResidual] at hD hP ⊢
    simp only [hQvalue, hQgrad, map_add, inner_add_left, zero_mul, add_zero,
      inner_zero_left, sub_zero] at hD hP ⊢
    linarith
  refine ⟨htrace.1, htrace.2, innerGapPotentialClass D hw hpos hslope j Q.fst, hweak, ?_⟩
  intro i
  exact (innerGapWeakResidual_affineUnit D hw hab ha hcore hpos j p hp hb Q hpot F hweak i).trans
    (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z i)
      (innerGapWeakFlux_affine D hw hab.le ha hcore hpos hslope p hp hb heq q hq F ξ))

/-- The already constructed physical inverse and Poisson map satisfy
the actual finite-piece input, including the fixed-hat flux, for every
physical L² source and every boundary vector. -/
theorem exists_innerGapDirichletPoisson_physical (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b j s : ℝ} (hab : a < b) (ha : 0 < a)
    (hj : 0 < j) (hs : 0 < s) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) D.w (p i) r = 0)
    (F : RadialModeL2 D) (ξ : EuclideanSpace ℝ (Fin 2)) :
    let G := innerGapDirichletInverse D hw hab.le ha hj hs hcore hpos hslope
    let P := innerGapPoissonL2 D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) p hp
    ∃ d v : RadialModeL2 D,
      (G F + P ξ, d) ∈ innerRadialH1Domain D hw.continuous ha hcore hpos ∧
      innerRadialH1Trace D hw.continuous ha hcore hpos (G F + P ξ, d) = (fun i => ξ i) ∧
      InnerRadialPotentialClass D j a b (G F + P ξ) v ∧
      (∀ r ∈ innerRadialH1Zero D a b,
        innerRadialWeakResidual D (G F + P ξ, d) v F 0 0 r = 0) ∧
      ∀ i : Fin 2,
        innerRadialWeakResidual D (G F + P ξ, d) v F 0 0
          (innerRadialAffineUnitPair D hw.continuous ha hcore hpos i) =
            (innerGapFluxOperator D.w a b p ξ - P.adjoint F) i := by
  let G := innerGapDirichletInverse D hw hab.le ha hj hs hcore hpos hslope
  let P := innerGapPoissonL2 D hw.continuous ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) p hp
  obtain ⟨q, hq, hvalue, hform⟩ := (innerGapFormGraph_iff D j a b (G F) F).mp
    (innerGapDirichletInverse_graph D hw hab.le ha hj hs hcore hpos hslope F)
  let Q := innerGapAffineEnergy D hw ha hcore hpos j p hp q ξ
  have hQvalue : Q.fst = G F + P ξ := by
    rw [innerGapAffineEnergy_function, hvalue]
  have h := innerGapAffineEnergy_physical D hw hab ha hcore hpos
    (fun r hr => hs.le.trans (hslope r hr)) p hp hb heq q hq F hform ξ
  refine ⟨Q.snd.fst, innerGapPotentialMultiplier D hw hpos j
    (innerGapPotentialMultiplier D hw hpos j Q.fst), ?_⟩
  simpa only [hQvalue] using h

end ContinuousFlexibility.Radial
