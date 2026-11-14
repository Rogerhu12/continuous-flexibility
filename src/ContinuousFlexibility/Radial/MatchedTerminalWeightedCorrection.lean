module

public import ContinuousFlexibility.Radial.MatchedTerminalLeadingBounds
public import ContinuousFlexibility.Radial.MatchedInnerWeightTransport

/-!
# The original terminal correction after the actual physical weight

The canonical residual is charged only on its true support. The
leading term is estimated from the physical cap density and amplitude.
The resulting inequality contains the norm of the same actual chain
inverse, which the local-piece theorem bounds independently; no weighted
inverse or external-column estimate is assumed here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

/-- The genuine terminal source keeps its original attenuation. Only
an almost-everywhere bound for the actual weight on its support is used. -/
theorem terminalRegional_source_weighted_bound_ae {D : ReferenceData}
    (R : TerminalRegionalData D) (i : Fin 2)
    (E : RadialModeL2 D ≃L[ℝ] RadialModeL2 D) (weight : ℝ → ℝ)
    (hE : ∀ f, E f =ᵐ[radialHilbertMeasure D] fun x => weight x * f x)
    {A : ℝ} (hA : 0 ≤ A)
    (hlocal : ∀ᵐ x ∂radialHilbertMeasure D,
      x ∈ tsupport (deriv (R.cutoff i)) → |weight x| ≤ A) :
    ‖((E).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))
      (terminalCapInnerSource R.matching.innerLeft R.matching.innerRight
        (R.matching.boundaryScale i) (R.cutoff i) (R.standIn i) (R.source_memLp i))‖ ≤
      A * ((R.sourceCost * sqrt (R.matching.D0 i)) * exp (-R.attenuation i)) := by
  let F := terminalCapInnerSource R.matching.innerLeft R.matching.innerRight
    (R.matching.boundaryScale i) (R.cutoff i) (R.standIn i) (R.source_memLp i)
  have hFs : F.2 = 0 := rfl
  have hs : ∀ᵐ x ∂radialHilbertMeasure D,
      x ∉ tsupport (deriv (R.cutoff i)) → F.1 x = 0 := by
    filter_upwards [terminalCapInnerSource_ae (R.source_memLp i)
      (R.cutoff_derivative_inside i)] with x hx hout
    rw [hx]
    by_contra hn
    exact hout (terminalCapHilbertSource_support (R.matching.boundaryScale i)
      D.w (R.cutoff i) (R.standIn i) hn)
  have hnorm : ‖F‖ ≤ (R.sourceCost * sqrt (R.matching.D0 i)) *
      exp (-R.attenuation i) :=
    (terminalCapInnerSource_norm_le_eLpNorm R.matching.innerLeft R.matching.innerRight
      (R.matching.boundaryScale i) (R.cutoff i) (R.standIn i)
      (R.source_memLp i)).trans (R.source_bound i)
  exact (matchedMode_weighted_zeroScalar_support_bound_ae E weight hE F hFs _
    hs hA hlocal).trans (mul_le_mul_of_nonneg_left hnorm hA)

section ActualCap

variable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (R : TerminalRegionalData D) (hM : MatchingLocalRealizations D R.matching)
    (i : Fin 2) (E : RadialModeL2 D ≃L[ℝ] RadialModeL2 D) (weight : ℝ → ℝ)
    (hE : ∀ f, E f =ᵐ[radialHilbertMeasure D] fun x => weight x * f x)

local notation "Em" => ContinuousLinearEquiv.prodCongr E (ContinuousLinearEquiv.refl ℝ ℝ)
local notation "T" =>
  (Em : RadialModePair D →L[ℝ] RadialModePair D) ∘L R.matching.innerInverse ∘L
    matchingSourceInnerCLM D R.matching hM ∘L
    matchedModeScalarGate D (decide (R.matching.frequency = 2)) ∘L
    (ContinuousLinearEquiv.symm Em : RadialModePair D →L[ℝ] RadialModePair D)

include hD hB hM hE

/-- Frozen uniqueness and the actual scalar gate give the exact
norm decomposition before either physical cap estimate is inserted. -/
theorem terminalRegional_innerPoisson_weighted_norm_split :
    ‖Em (R.matching.innerPoisson i)‖ ≤
      ‖Em (terminalCapInnerLift hD R.matching.innerLeft R.matching.innerRight
        (R.matching.boundaryScale i) (R.cutoff_smooth i) (R.standIn_smooth i))‖ +
      ‖T‖ * ‖Em (terminalCapInnerSource R.matching.innerLeft R.matching.innerRight
        (R.matching.boundaryScale i) (R.cutoff i) (R.standIn i) (R.source_memLp i))‖ := by
  let F := terminalCapInnerSource R.matching.innerLeft R.matching.innerRight
    (R.matching.boundaryScale i) (R.cutoff i) (R.standIn i) (R.source_memLp i)
  have hFs : F.2 = 0 := rfl
  have hfix : R.matching.sourceInner F = F := by
    rw [R.inner_source F]
    exact modeInnerSource_idempotent D R.matching.innerLeft R.matching.innerRight _
  have hgate : matchedModeScalarGate D (decide (R.matching.frequency = 2)) F = F :=
    matchedModeScalarGate_eq_self D _ F (fun _ => hFs)
  have happ : T (Em F) = Em (R.matching.innerInverse F) := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, hgate, matchingSourceInnerCLM_apply, hfix]
  have hrem : ‖Em (R.matching.innerInverse F)‖ ≤ ‖T‖ * ‖Em F‖ := by
    rw [← happ]
    exact (T).le_opNorm _
  rw [terminalRegional_innerPoisson_eq hD hB R hM i, map_sub]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl hrem)

/-- Raw cap geometry and the original measured residual give a bound
for the actual external column. The conjugated operator here is the
original restricted matching inverse with its frequency scalar gate. -/
theorem terminalRegional_innerPoisson_weighted_cap_bound
    {a b P H A : ℝ} (hab : a ≤ b) (hP : 0 ≤ P) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hcap : Icc a b ⊆ Icc R.matching.innerLeft R.matching.innerRight)
    (hcover : ∀ x ∈ Icc R.matching.innerLeft R.matching.innerRight,
      R.cutoff i x ≠ 0 → x ∈ Icc a b)
    (hcutoff : ∀ x ∈ Icc a b, |R.cutoff i x| ≤ 1)
    (hvalue : ∀ x ∈ Icc a b, |R.standIn i x| ≤ H)
    (hρ : ∀ x ∈ Icc a b, 12 * D.w x / x ^ 2 ≤ P)
    (hsourceCap : tsupport (deriv (R.cutoff i)) ⊆ Icc a b)
    (hlocal : ∀ᵐ x ∂radialHilbertMeasure D, x ∈ Icc a b → |weight x| ≤ A) :
    ‖Em (R.matching.innerPoisson i)‖ ≤
      A * ((H / sqrt (R.matching.boundaryScale i)) * sqrt (P * (b - a)) +
        ‖T‖ * ((R.sourceCost * sqrt (R.matching.D0 i)) * exp (-R.attenuation i))) := by
  have hf : ‖Em (terminalCapInnerSource R.matching.innerLeft R.matching.innerRight
      (R.matching.boundaryScale i) (R.cutoff i) (R.standIn i) (R.source_memLp i))‖ ≤
      A * ((R.sourceCost * sqrt (R.matching.D0 i)) * exp (-R.attenuation i)) := by
    apply terminalRegional_source_weighted_bound_ae R i E weight hE hA
    filter_upwards [hlocal] with x hx hxs
    exact hx (hsourceCap hxs)
  have hlead := terminalCapInnerLift_weighted_bound hD hab (R.diagonal i).1 hP hH
    (R.cutoff_smooth i) (R.standIn_smooth i) hcap hcover hcutoff hvalue hρ
    E weight hE hA hlocal
  exact (terminalRegional_innerPoisson_weighted_norm_split hD hB R hM i E weight hE).trans
    ((add_le_add hlead (mul_le_mul_of_nonneg_left hf (norm_nonneg T))).trans_eq (by ring))

end ActualCap

section SameChain

variable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hw : ContDiff ℝ ∞ D.w) {n : ℕ} (G : InnerRadialChainGeometry D n)
    (R : TerminalRegionalData D) (hM : MatchingLocalRealizations D R.matching)
    (hleft : R.matching.innerLeft = G.left 0)
    (hright : R.matching.innerRight = G.right (Fin.last n))
    (central : Fin (n + 1)) (column : RadialModeL2 D)
    (hcolumn : column = matchingBorderVector D hD hB)
    (hcolfix : innerL2PieceProjection (radialHilbertMeasure D)
      (Ioo (G.left central) (G.right central)) column = column)
    (C : InnerRadialActualChain D G (decide (R.matching.frequency = 2))
      (R.matching.frequency : ℝ) central column)
    (hS : IsUnit C.fluxMatrix)
    (weight : ℝ → ℝ) (hweight : Measurable weight) (hpos : ∀ x, 0 < weight x)
    (B Binv : ℝ) (hweightB : ∀ x, |weight x| ≤ B)
    (hweightInv : ∀ x, |(weight x)⁻¹| ≤ Binv)

local notation "Hsrc" => InnerRadialPhysicalSource D G (decide (R.matching.frequency = 2))
local notation "E" => innerWeightEquiv (radialHilbertMeasure D)
  weight hweight hpos B Binv hweightB hweightInv
local notation "EH" => innerSupportedWeightEquiv (radialHilbertMeasure D)
  (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G)
  (decide (R.matching.frequency = 2)) weight hweight hpos B Binv hweightB hweightInv
local notation "Em" => matchedModeActualWeight D
  weight hweight hpos B Binv hweightB hweightInv
local notation "K" => ‖(EH : Hsrc →L[ℝ] Hsrc) ∘L C.inverse hw hS ∘L
  (ContinuousLinearEquiv.symm EH : Hsrc →L[ℝ] Hsrc)‖

include hD hB hM hleft hright hcolumn hcolfix

/-- The cap estimate for the same actual C. Its only operator quantity
is the original conjugated C.inverse; the local-piece theorem proves
the required uniform estimate for exactly this quantity. -/
theorem terminalRegional_innerPoisson_sameC_cap_bound
    (i : Fin 2) {a b P H A : ℝ}
    (hab : a ≤ b) (hP : 0 ≤ P) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hcap : Icc a b ⊆ Icc R.matching.innerLeft R.matching.innerRight)
    (hcover : ∀ x ∈ Icc R.matching.innerLeft R.matching.innerRight,
      R.cutoff i x ≠ 0 → x ∈ Icc a b)
    (hcutoff : ∀ x ∈ Icc a b, |R.cutoff i x| ≤ 1)
    (hvalue : ∀ x ∈ Icc a b, |R.standIn i x| ≤ H)
    (hρ : ∀ x ∈ Icc a b, 12 * D.w x / x ^ 2 ≤ P)
    (hsourceCap : tsupport (deriv (R.cutoff i)) ⊆ Icc a b)
    (hlocal : ∀ᵐ x ∂radialHilbertMeasure D, x ∈ Icc a b → |weight x| ≤ A) :
    ‖Em (R.matching.innerPoisson i)‖ ≤
      A * ((H / sqrt (R.matching.boundaryScale i)) * sqrt (P * (b - a)) +
        (sqrt 2 * K) *
          ((R.sourceCost * sqrt (R.matching.D0 i)) * exp (-R.attenuation i))) := by
  have hsub : Icc R.matching.innerLeft R.matching.innerRight ⊆ radialCore D := by
    intro x hx
    exact ⟨R.cut_order.1.trans_le hx.1, hx.2.trans_lt R.cut_order.2.2⟩
  have hK : (0 : ℝ) ≤ K :=
    norm_nonneg ((EH : Hsrc →L[ℝ] Hsrc) ∘L C.inverse hw hS ∘L
      ((EH).symm : Hsrc →L[ℝ] Hsrc))
  have hT := matchedInnerActualInverse_weighted_opNorm_le hD hB hw G R.matching hM
    hleft hright hsub central column hcolumn hcolfix C hS
    weight weight hweight hweight hpos hpos B Binv B Binv
    hweightB hweightInv hweightB hweightInv hK (le_refl K)
  have hE : ∀ f, E f =ᵐ[radialHilbertMeasure D] fun x => weight x * f x :=
    innerWeightEquiv_ae (radialHilbertMeasure D)
      weight hweight hpos B Binv hweightB hweightInv
  have hh := terminalRegional_innerPoisson_weighted_cap_bound hD hB R hM i E weight hE
    hab hP hH hA hcap hcover hcutoff hvalue hρ hsourceCap hlocal
  have hf : 0 ≤ (R.sourceCost * sqrt (R.matching.D0 i)) * exp (-R.attenuation i) :=
    ENNReal.toReal_nonneg.trans (R.source_bound i)
  exact hh.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hT hf)) hA)

end SameChain

end ContinuousFlexibility.Radial
