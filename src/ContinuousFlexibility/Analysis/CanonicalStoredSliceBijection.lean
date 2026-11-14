module

public import ContinuousFlexibility.Analysis.CanonicalStoredFootpointIdentification

/-!
# Actual stored angular slices are bijections

The smooth effective radial coefficient equals the original positive
coefficient even at the cut, by continuity from the open half. Its
adjugate formula forces both Airy angular derivatives to be nonzero.
The genuine glued first jets therefore give injective angular first
integrals on the entire component. Their already proved trajectory
identities and the surjective N01 left gauge imply that every stored
angular slice is onto. No regularity of the stored cut-axis angular
coefficient or separate field realization is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Rolle's theorem excludes two equal values when the actual derivative
never vanishes. No positive derivative sign is needed. -/
theorem scalar_injective_of_deriv_ne_zero
    {f : ℝ → ℝ} (hne : ∀ θ, deriv f θ ≠ 0) : Function.Injective f := by
  have hf : Differentiable ℝ f := fun θ => differentiableAt_of_deriv_ne_zero (hne θ)
  have hordered {x y : ℝ} (hxy : x < y) (he : f x = f y) : False := by
    obtain ⟨t, _, ht⟩ := exists_hasDerivAt_eq_slope f (deriv f) hxy
      hf.continuous.continuousOn (fun t _ => (hf t).hasDerivAt)
    apply hne t
    simpa only [he, sub_self, zero_div] using ht
  intro x y he
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with h | h
  · exact hordered h he
  · exact hordered h he.symm

/-- A nonzero radial adjugate coefficient makes both actual Airy angular
derivatives nonzero. The sign of the planar Jacobian is irrelevant. -/
theorem airyFirstIntegral_angularPartial_ne_zero
    {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (hξ : 0 < (F p).1)
    (ha : (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a p ≠ 0)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    angularPartial (airyFirstIntegral F σ) p ≠ 0 := by
  let ξ : ℝ := (F p).1
  let s : ℝ := Real.sqrt ξ
  let u : ℝ := (fderiv ℝ F p (0, 1)).1
  let v : ℝ := (fderiv ℝ F p (0, 1)).2
  let k : ℝ := 1 / (h p ^ 2 * |planeJacobian F p|)
  have hs : s ^ 2 = ξ := Real.sq_sqrt hξ.le
  have hentry : (adjugateCoordinatePrincipalCoefficients
      canonicalAiryPrincipalCoefficients F h).a p = k * (v ^ 2 - ξ * u ^ 2) := by
    dsimp only [k, v, ξ, u, adjugateCoordinatePrincipalCoefficients,
      canonicalAiryPrincipalCoefficients, coefficientQuadratic]
    ring
  have hpart : angularPartial (airyFirstIntegral F σ) p = v + σ * s * u :=
    (airyFirstIntegral_partials hF hξ σ).2
  have hprod : (v + σ * s * u) * (v - σ * s * u) = v ^ 2 - ξ * u ^ 2 := by
    rw [← hs]
    rcases hσ with rfl | rfl <;> ring
  intro he
  have hz : v + σ * s * u = 0 := hpart.symm.trans he
  have hzero : v ^ 2 - ξ * u ^ 2 = 0 := by rw [← hprod, hz, zero_mul]
  apply ha
  rw [hentry, hzero, mul_zero]

section Canonical

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hN01 : N01Properties D T S C base loss ε)
  (hN03 : N03Properties D T S C R L base ε)
  (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1)

include hS hT hN01 hN03 hA hB hz hs

/-- The original radial coefficient has a genuine continuous extension
to each closed negative half. This identifies the effective coefficient
there, including cut points on the axes, without assertions about stored c. -/
theorem negativeCanonicalClosedCoefficients_radial_eq_original_on_closure
    (i : ℕ) (hi : K.positive i = false) {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S K z i) (hpAnn : p ∈ annularOpen D) :
    (negativeCanonicalClosedCoefficients S K z i).a p =
      (originalCoefficients D S C z).a p := by
  have hOriginal : ContDiffOn ℝ ∞ (originalCoefficients D S C z).a (annularOpen D) :=
    contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 0
  have he : EqOn (negativeCanonicalClosedCoefficients S K z i).a
      (originalCoefficients D S C z).a (physicalPieceOpen S K z i) := by
    intro q hq
    have hqAnn := (hA.domains z hz hs i).2.2.1 hq
    exact negativeCanonicalClosedCoefficients_radial_eq_original hA hB hN03 hz hs i hi hq
      (((hOriginal q hqAnn).contDiffAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds hqAnn)).differentiableAt (by simp))
  have hBc : ContinuousAt (negativeCanonicalClosedCoefficients S K z i).a p :=
    (negativeCanonicalClosedCoefficients_contDiffAt hA hz hs i hp).1.continuousAt
  have hOc : ContinuousAt (originalCoefficients D S C z).a p :=
    ((hOriginal p hpAnn).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpAnn)).continuousAt
  haveI : NeBot (𝓝[physicalPieceOpen S K z i] p) :=
    mem_closure_iff_nhdsWithin_neBot.mp hp
  exact tendsto_nhds_unique_of_eventuallyEq
    (hBc.mono_left nhdsWithin_le_nhds) (hOc.mono_left nhdsWithin_le_nhds)
    (he.eventuallyEq_of_mem self_mem_nhdsWithin)

/-- Both genuine glued angular derivatives are nonzero on the whole open
negative component. Cut-axis coefficient values are not used. -/
theorem canonicalGluedAiryIntegral_angularPartial_ne_zero
    (m : ℕ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    angularPartial (canonicalGluedAiryIntegral S K z m σ) p ≠ 0 := by
  let i : Bool → ℕ := fun side => if side then (K.cutPair m).2 else (K.cutPair m).1
  have hbounds := hN01.2.2.2.1.1 m
  have hpAnn : p ∈ annularOpen D :=
    ⟨⟨hbounds.1.trans hp.1.1, hp.1.2.trans hbounds.2.2⟩, mem_univ _⟩
  obtain ⟨hnegL, hnegR, _, _, _, hρ, hleftL, hleftR, _, _⟩ := hB.1.1 m
  have hpart (side : Bool) (hclosed : p ∈ physicalPieceClosed S K z (i side))
      (hξ : 0 < (K.chart z (i side) p).1)
      (hjet : fderiv ℝ (canonicalGluedAiryIntegral S K z m σ) p =
        fderiv ℝ (airyFirstIntegral (K.chart z (i side)) (if side then -σ else σ)) p) :
      angularPartial (canonicalGluedAiryIntegral S K z m σ) p ≠ 0 := by
    have hnegative : K.positive (i side) = false := by cases side <;> assumption
    have ha : (negativeCanonicalClosedCoefficients S K z (i side)).a p ≠ 0 := by
      rw [negativeCanonicalClosedCoefficients_radial_eq_original_on_closure
        hS hT hN01 hN03 hA hB hz hs (i side) hnegative hclosed hpAnn]
      exact (n01_originalRadialCoefficient_pos hN01 hz hs hpAnn).ne'
    have hF := ((hA.boundary z hz hs (i side)).2.2.2.2.1 p hclosed).1
    have he : angularPartial (canonicalGluedAiryIntegral S K z m σ) p =
        angularPartial (airyFirstIntegral
          (K.chart z (i side)) (if side then -σ else σ)) p :=
      congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1)) hjet
    rw [he]
    apply airyFirstIntegral_angularPartial_ne_zero (hF.differentiableAt (by simp)) hξ ha
    cases side with
    | false => exact hσ
    | true =>
        rcases hσ with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (neg_neg (1 : ℝ))
  by_cases hcut : p ∈ Set.range (canonicalCutPoint S K z m)
  · obtain ⟨θ, hpθ⟩ := hcut
    have hleft := canonicalCut_closed_and_chart hA hB hz hs m false θ
    have hξ : 0 < (K.chart z (i false) p).1 := by rw [← hpθ, hleft.2]; exact hρ
    exact hpart false (by simpa only [hpθ] using hleft.1) hξ
      (by simpa only [i, Bool.false_eq_true, ↓reduceIte, hpθ] using
        canonicalGluedAiryIntegral_fderiv_on_cut hA hB hz hs m σ θ)
  · have hwhere : p ∈ physicalPieceOpen S K z (K.cutPair m).1 ∪
        physicalPieceOpen S K z (K.cutPair m).2 := by
      rw [(hB.1.2 z hz hs m).2.2.2.1]
      exact ⟨hp, hcut⟩
    have hopen (side : Bool) (hq : p ∈ physicalPieceOpen S K z (i side)) :
        angularPartial (canonicalGluedAiryIntegral S K z m σ) p ≠ 0 := by
      have hleft : K.left (i side) = 0 := by cases side <;> assumption
      have hξ : 0 < (K.chart z (i side) p).1 := by
        simpa only [hleft] using ((hA.charts z hz hs (i side)).1 hq).1.1
      exact hpart side (subset_closure hq) hξ
        (canonicalGluedAiryIntegral_fderiv_on_piece hA hB hz hs m side σ hq)
    exact hwhere.elim (hopen false) (hopen true)

/-- Each complete angular first-integral slice is injective. -/
theorem canonicalGluedAiryIntegral_angular_injective
    (m : ℕ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    Function.Injective (fun θ => canonicalGluedAiryIntegral S K z m σ (r, θ)) := by
  let U : PolarPoint → ℝ := canonicalGluedAiryIntegral S K z m σ
  have hU := contDiffOn_canonicalGluedAiryIntegral hA hB hz hs m σ
  apply scalar_injective_of_deriv_ne_zero
  intro θ
  have hp : (r, θ) ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := ⟨hr, mem_univ _⟩
  have hd := ((hU (r, θ) hp).contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt_one.hasFDerivAt.comp_hasDerivAt θ
      ((hasDerivAt_const θ r).prodMk (hasDerivAt_id' θ))
  have he : U ∘ (fun η : ℝ => (r, η)) = (fun η : ℝ => U (r, η)) := by
    funext η
    exact Function.comp_apply
  rw [he] at hd
  rw [hd.deriv]
  exact canonicalGluedAiryIntegral_angularPartial_ne_zero hS hT hN01 hN03 hA hB hz hs m hσ hp

/-- The actual stored N03 angular slice is onto, obtained from the
first-integral identity and its injectivity, without separate flow existence. -/
theorem n03CharacteristicSlice_bijective
    (hN02 : N02Properties D T S C R base ε) (m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    Function.Bijective (L.minusFlow z m r) := by
  refine ⟨(n03CharacteristicSlice_injective hS hT hN01 hN02 hN03 hA hB hz hs m hr).1, ?_⟩
  have hleft : Function.Surjective (stateLeftChart S z.1 m) :=
    surjective_of_deriv_lower_bound (by norm_num : (0 : ℝ) < 1 / 2)
      (fun θ => (hN01.2.2.2.2.2.2.2.1 z hz hs m θ).1)
  have hU := canonicalGluedAiryIntegral_angular_injective
    hS hT hN01 hN03 hA hB hz hs m (σ := 1) (Or.inl rfl) hr
  intro θ
  obtain ⟨θ₀, hθ₀⟩ := hleft (canonicalGluedAiryIntegral S K z m 1 (r, θ))
  refine ⟨θ₀, hU ?_⟩
  exact (canonicalGluedAiryIntegral_on_n03Flows
    hS hT hN01 hN02 hN03 hA hB hz hs m hr θ₀).1.trans hθ₀

/-- Both existing canonical first integrals equal the true stored
footpoint formulas on every physical angular line of the open component. -/
theorem canonicalGluedAiryIntegral_eq_storedFootpoints
    (hN02 : N02Properties D T S C R base ε) (m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    canonicalGluedAiryIntegral S K z m 1 (r, θ) =
        stateLeftChart S z.1 m (Function.invFun (L.minusFlow z m r) θ) ∧
      canonicalGluedAiryIntegral S K z m (-1) (r, θ) =
        stateLeftChart S z.1 m
          (Function.invFun (fun η => -L.minusFlow z m r (-η)) θ) :=
  canonicalGluedAiryIntegral_eq_storedFootpoints_of_surjective
    hS hT hN01 hN02 hN03 hA hB hz hs m hr
    (n03CharacteristicSlice_bijective hS hT hN01 hN03 hA hB hz hs hN02 m hr).2 θ

end Canonical

end ContinuousFlexibility.Analysis
