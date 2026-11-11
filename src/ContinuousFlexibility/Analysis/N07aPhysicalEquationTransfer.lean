import ContinuousFlexibility.Analysis.N07aPhysicalRemainder
import ContinuousFlexibility.Analysis.N07aCorrectedForward

/-!
# The actual height pair keeps the original equation

Equality on the open core preserves both derivatives of the original
divergence operator. Source compatibility then removes the actual auxiliary
column using Q(psi)=1, after the genuine height member has been constructed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n07a_divergenceOperator_field_eqOn {U : Set PolarPoint} (hU : IsOpen U)
    {f g : PolarPoint → ℝ} (he : EqOn f g U) (A : SymmetricCoefficients) :
    EqOn (divergenceOperator A f) (divergenceOperator A g) U := by
  have hd {p : PolarPoint} (hp : p ∈ U) : fderiv ℝ f p = fderiv ℝ g p := by
    have hg : f =ᶠ[𝓝 p] g := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact he hq
    exact hg.fderiv_eq
  intro p hp
  have hr : (fun q => A.a q * radialPartial f q + A.b q * angularPartial f q)
      =ᶠ[𝓝 p] (fun q => A.a q * radialPartial g q + A.b q * angularPartial g q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    simp only [radialPartial, angularPartial, hd hq]
  have ht : (fun q => A.b q * radialPartial f q + A.c q * angularPartial f q)
      =ᶠ[𝓝 p] (fun q => A.b q * radialPartial g q + A.c q * angularPartial g q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    simp only [radialPartial, angularPartial, hd hq]
  exact congrArg₂ (fun r t : PolarPoint →L[ℝ] ℝ => r (1, 0) + t (0, 1))
    hr.fderiv_eq ht.fderiv_eq

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07aPhysicalHeightPair_row {K : CanonicalData S} (hS : IsPhysicalSpaces D T S) (hab : D.a ≤ D.b)
    (a : ℝ) (v : PolarPoint → ℝ)
    (hvp : Function.Periodic v (0, Real.pi))
    (hmem : HeightMember D T (3 / 4 : ℝ) (n07aPhysicalRemainder D S a v)) :
    referenceRow D (heightPairField S (n07aPhysicalHeightPair hS a v hmem)) =
      referenceRow D v := by
  let η := n07aPhysicalHeightPair hS a v hmem
  have hηp : Function.Periodic (heightPairField S η) (0, Real.pi) := by
    intro p
    simp only [η, heightPairField, n07aPhysicalHeightPair,
      SobolevModelData.decode_liftHeight,
      n07aPhysicalRemainder_periodic hvp p, Prod.fst_add, add_zero]
  apply n07a_referenceRow_congr_ae (S := S) (K := K) hab hηp hvp
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)]
    with p hp
  exact n07aPhysicalHeightPair_field hS a v hmem ⟨hp.1, mem_univ _⟩

theorem n07a_actualAuxiliaryScalar_zero
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (N : S.Source)
    (hN : ∀ p, (S.height (3 / 4 : ℝ)).decode N.val p =
      nuColumnField D S C (liftSectorParameter S C z) p)
    (η : HeightPair S) (μ aux : ℝ) (f : S.Source)
    (heq : ∀ p ∈ annularOpen D,
      divergenceOperator (L.coefficients (liftSectorParameter S C z))
          (heightPairField S η) p +
        μ * nuColumnField D S C (liftSectorParameter S C z) p +
        aux * (S.height (3 / 4 : ℝ)).decode S.psi p =
          (S.height (3 / 4 : ℝ)).decode f.val p) : aux = 0 := by
  let F : S.Source := n07aCorrectedForwardCLM hS hT h01 h02 h03 z η + μ • N
  have hdecode (p : PolarPoint) (hp : p ∈ annularOpen D) :
      (S.height (3 / 4 : ℝ)).decode F.val p =
        divergenceOperator (L.coefficients (liftSectorParameter S C z))
          (heightPairField S η) p + μ * nuColumnField D S C (liftSectorParameter S C z) p := by
    simp only [F, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      n07aCorrectedForwardCLM_decode hS hT h01 h02 h03 hz η hp, hN p]
  have hheight : F.val + aux • S.psi = f.val := by
    apply (hS.1 (3 / 4 : ℝ)).2.2.2.2.2.1
    funext p
    by_cases hp : p ∈ annularOpen D
    · simpa only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        hdecode p hp] using heq p hp
    · rw [((hS.1 (3 / 4 : ℝ)).2.2.2.1 (F.val + aux • S.psi)).2.2.2.1 p hp,
        ((hS.1 (3 / 4 : ℝ)).2.2.2.1 f.val).2.2.2.1 p hp]
  have hQF : S.Q F.val = 0 := F.property
  have hQf : S.Q f.val = 0 := f.property
  obtain ⟨_, _, _, _, _, _, _, _, _, hQψ, _⟩ := hS
  have hQ := congrArg S.Q hheight
  simpa only [map_add, map_smul, smul_eq_mul, hQF, hQf, hQψ,
    mul_one, zero_add] using hQ

end ContinuousFlexibility.Analysis
