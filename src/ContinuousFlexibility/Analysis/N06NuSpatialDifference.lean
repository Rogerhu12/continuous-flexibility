module

public import ContinuousFlexibility.Analysis.N06NuSpatialCoordinateCompact

/-!
# Full physical spatial smallness of the actual nu difference

The finite nu formula is evaluated on the genuine original state segment,
where N01 supplies its positive discriminant. Full spatial packet bounds
therefore give a linear small factor in the original order n+4 seminorm.
The same bound controls every mixed radial/angular jet through order n.
Outside the fixed chi support the actual difference vanishes on a
neighborhood, so no extension of its finite formula is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators Topology

theorem n06_abs_mixedDerivative_le_frechet
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    |mixedDerivative a b f p| ≤ ‖iteratedFDeriv ℝ (a + b) f p‖ := by
  induction a generalizing f with
  | zero =>
    induction b generalizing f with
    | zero =>
      change |f p| ≤ ‖iteratedFDeriv ℝ 0 f p‖
      simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, le_refl]
    | succ b ih =>
      have hfa : ContDiffOn ℝ ∞ (angularPartial f) U :=
        n06_spatial_directional_contDiffOn hU hf (0, 1)
      rw [← mixedDerivative_angularPartial hU hf 0 b hp]
      have h := n06_norm_iteratedFDeriv_directional_le hU hf (0, 1) b hp
      have h' : ‖iteratedFDeriv ℝ b (angularPartial f) p‖ ≤
          ‖iteratedFDeriv ℝ (b + 1) f p‖ := by
        change ‖iteratedFDeriv ℝ b (fun q => fderiv ℝ f q (0, 1)) p‖ ≤ _
        simpa [Prod.norm_def] using h
      have he₀ : ‖iteratedFDeriv ℝ (0 + b) (angularPartial f) p‖ =
          ‖iteratedFDeriv ℝ b (angularPartial f) p‖ :=
        congrArg (fun k : ℕ => ‖iteratedFDeriv ℝ k (angularPartial f) p‖) (Nat.zero_add b)
      have he₁ : ‖iteratedFDeriv ℝ (b + 1) f p‖ =
          ‖iteratedFDeriv ℝ (0 + (b + 1)) f p‖ :=
        congrArg (fun k : ℕ => ‖iteratedFDeriv ℝ k f p‖) (Nat.zero_add (b + 1)).symm
      exact (((ih hfa).trans_eq he₀).trans h').trans_eq he₁
  | succ a ih =>
    have hfr : ContDiffOn ℝ ∞ (radialPartial f) U :=
      n06_spatial_directional_contDiffOn hU hf (1, 0)
    rw [← mixedDerivative_radialPartial hU hf a b hp]
    have h := n06_norm_iteratedFDeriv_directional_le hU hf (1, 0) (a + b) hp
    have h' : ‖iteratedFDeriv ℝ (a + b) (radialPartial f) p‖ ≤
        ‖iteratedFDeriv ℝ (a + b + 1) f p‖ := by
      change ‖iteratedFDeriv ℝ (a + b) (fun q => fderiv ℝ f q (1, 0)) p‖ ≤ _
      simpa [Prod.norm_def] using h
    have he : ‖iteratedFDeriv ℝ (a + b + 1) f p‖ =
        ‖iteratedFDeriv ℝ (a + 1 + b) f p‖ :=
      congrArg (fun k : ℕ => ‖iteratedFDeriv ℝ k f p‖) (by omega)
    exact ((ih hfr).trans h').trans_eq he

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n06_nuColumn_spatialDifference_eq_finite_composition
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (n : ℕ) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    iteratedFDeriv ℝ n (fun q => nuColumnField D S C z q -
      nuColumnField D S C (C.referenceState, 0) q) p =
      iteratedFDeriv ℝ n (n06NuFiniteJetMap ∘ n06ActualNuJetCoordinates D S z) p -
      iteratedFDeriv ℝ n
        (n06NuFiniteJetMap ∘ n06ActualNuJetCoordinates D S (C.referenceState, 0)) p := by
  have hcurrent := n06_nuColumn_contDiff hT hS hN01 hz hs
  have href := n06_nuColumn_contDiff hT hS hN01
    (n05_referenceState_mem hN01.2.1) (n05_referenceState_sector hN01.2.2.1)
  have he (w : AnnularState S × ℝ) : nuColumnField D S C w =ᶠ[𝓝 p]
      n06NuFiniteJetMap ∘ n06ActualNuJetCoordinates D S w := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact n06_nuColumn_eq_finiteJetMap hT hS hN01 w hq
  have hsub := iteratedFDeriv_sub_apply (x := p) (i := n)
    (hcurrent.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    (href.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
  exact hsub.trans (congrArg₂ (fun A B => A - B)
    (((he z).iteratedFDeriv ℝ n).eq_of_nhds)
    (((he (C.referenceState, 0)).iteratedFDeriv ℝ n).eq_of_nhds))

def N06NuSpatialDifferenceBound (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) (n : ℕ) (Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ,
    z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (n + 4) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∀ k, k ≤ n → ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ k (fun q => nuColumnField D S C z q -
        nuColumnField D S C (C.referenceState, 0) q) p‖ ≤
          Q * (stateGrading S (n + 4) (z.1 - C.referenceState) + |z.2|)

/-- The actual current-reference nu field has all physical spatial jets
through order n linearly small in one original seminorm of order n+4.
No current canonical chart, final source bound, or prescribed jet enters
the hypotheses. -/
theorem n06_nuColumn_spatialDifference_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06NuSpatialDifferenceBound D S C base ε n Q := by
  classical
  obtain ⟨L, M, hL, hM, hcoords⟩ :=
    n06_actualNuJetCoordinates_spatial_near_fixed_state
      hN01.1.1 hT hS hN01.1.2.2.2.1.1 C.referenceState n
  have hchoices (i : Fin (n + 1)) :=
    n06NuFiniteJetMap_spatial_composition_difference_bound (E := PolarPoint) i.val hM
  choose c hc hcomposition using hchoices
  let Q : ℝ := ∑ i : Fin (n + 1), c i
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => hc i
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  refine ⟨Q * L, mul_nonneg hQ hL₀, ?_⟩
  intro z hz hs hsmall k hk p hp
  let δ : ℝ := stateGrading S (n + 4) (z.1 - C.referenceState) + |z.2|
  have hδ : 0 ≤ δ := add_nonneg (apply_nonneg _ _) (abs_nonneg _)
  by_cases hborder : p.1 ∈ tsupport D.chi
  · let i : Fin (n + 1) := ⟨k, by omega⟩
    have hr : p.1 ≠ 0 := (hN01.1.1.choose_spec.1.1.trans hp.1.1).ne'
    have hu := n06_actualNuJetCoordinates_contDiffAt hT hS
      hN01.1.1.choose_spec.1.2.2.1.1 hN01.1.2.2.2.1.1 z hr
    have hv := n06_actualNuJetCoordinates_contDiffAt hT hS
      hN01.1.1.choose_spec.1.2.2.1.1 hN01.1.2.2.2.1.1 (C.referenceState, 0) hr
    have hU (j : ℕ) (hj : j ≤ k) :
        ‖iteratedFDeriv ℝ j (n06ActualNuJetCoordinates D S z) p‖ ≤ M :=
      (hcoords z hsmall j (hj.trans hk) p hp).1
    have hV (j : ℕ) (hj : j ≤ k) :
        ‖iteratedFDeriv ℝ j (n06ActualNuJetCoordinates D S (C.referenceState, 0)) p‖ ≤ M :=
      (hcoords z hsmall j (hj.trans hk) p hp).2.1
    have hUV (j : ℕ) (hj : j ≤ k) :
        ‖iteratedFDeriv ℝ j (n06ActualNuJetCoordinates D S z) p -
          iteratedFDeriv ℝ j (n06ActualNuJetCoordinates D S (C.referenceState, 0)) p‖ ≤ L * δ :=
      (hcoords z hsmall j (hj.trans hk) p hp).2.2
    have hdisc := n06_actualNuJetDiscriminant_segment_lower hT hS hN01 hz hs hp hborder
    have h := hcomposition i (n06ActualNuJetCoordinates D S z)
      (n06ActualNuJetCoordinates D S (C.referenceState, 0)) p (L * δ)
      hu hv (mul_nonneg hL₀ hδ) hU hV hUV hdisc
    have hi : c i ≤ Q := Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)
    exact (congrArg norm
      (n06_nuColumn_spatialDifference_eq_finite_composition hT hS hN01 hz hs k hp)).trans_le
      (h.trans ((mul_le_mul_of_nonneg_right hi (mul_nonneg hL₀ hδ)).trans_eq
        (mul_assoc Q L δ).symm))
  · have hb : RadialTrueBorder D := hN01.1.2.2.2.1
    have hnear : (fun q => nuColumnField D S C z q -
        nuColumnField D S C (C.referenceState, 0) q) =ᶠ[𝓝 p] (fun _ : PolarPoint => 0) := by
      filter_upwards [(hb.2.1.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds hborder]
        with q hq
      rw [n06_nuColumn_zero_off_tsupport hT hS hN01 z hq,
        n06_nuColumn_zero_off_tsupport hT hS hN01 (C.referenceState, 0) hq, sub_self]
    have he := congrArg norm ((hnear.iteratedFDeriv ℝ k).eq_of_nhds)
    have hzderiv : ‖iteratedFDeriv ℝ k (fun q => nuColumnField D S C z q -
        nuColumnField D S C (C.referenceState, 0) q) p‖ = 0 := by
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using he
    exact hzderiv.trans_le (mul_nonneg (mul_nonneg hQ hL₀) hδ)

def N06NuMixedSpatialDifferenceBound (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) (n : ℕ) (Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ,
    z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (n + 4) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∀ a b, a + b ≤ n → ∀ p ∈ annularOpen D,
      |mixedDerivative a b (fun q => nuColumnField D S C z q -
        nuColumnField D S C (C.referenceState, 0) q) p| ≤
          Q * (stateGrading S (n + 4) (z.1 - C.referenceState) + |z.2|)

theorem n06_nuColumn_mixedSpatialDifference_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06NuMixedSpatialDifferenceBound D S C base ε n Q := by
  obtain ⟨Q, hQ, hbound⟩ := n06_nuColumn_spatialDifference_bound hT hS hN01 n
  refine ⟨Q, hQ, ?_⟩
  intro z hz hs hsmall a b hab p hp
  have hf := (n06_nuColumn_contDiff hT hS hN01 hz hs).sub
    (n06_nuColumn_contDiff hT hS hN01
      (n05_referenceState_mem hN01.2.1) (n05_referenceState_sector hN01.2.2.1))
  exact (n06_abs_mixedDerivative_le_frechet (isOpen_Ioo.prod isOpen_univ)
    hf.contDiffOn a b hp).trans (hbound z hz hs hsmall (a + b) hab p hp)

end ContinuousFlexibility.Statements
