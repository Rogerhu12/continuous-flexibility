import ContinuousFlexibility.Analysis.CanonicalRootGaugeRigidity

/-!
# The existing canonical first integrals along the stored N03 flow

True transport away from the two exceptional physical radii, continuity
at those radii, and the genuine left endpoint trace identify the first
integral at every interior time. The two stored angular slices are then
injective. A separately established slice surjectivity gives the exact
formula in terms of its actual `invFun`; no field realization or flow
regularity theorem is assumed here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Every interior value equals the genuine left trace. No total endpoint
value of the function is used. -/
theorem eq_left_trace_of_hasDerivAt_zero_off_pair
    {f : ℝ → ℝ} {a b c d A : ℝ} (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b)
    (hf : ContinuousOn f (Ioo a b))
    (hzero : ∀ t ∈ Ioo a b, t ≠ c → t ≠ d → HasDerivAt f 0 t)
    (hleft : Tendsto f (𝓝[Ioo a b] a) (𝓝 A)) {t : ℝ} (ht : t ∈ Ioo a b) :
    f t = A := by
  obtain ⟨v, he⟩ := exists_constant_of_hasDerivAt_zero_off_pair hc hd hf hzero
  have hab : a < b := hc.1.trans hc.2
  have hca : a ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨le_rfl, hab.le⟩
  haveI : NeBot (𝓝[Ioo a b] a) := mem_closure_iff_nhdsWithin_neBot.mp hca
  have hA : A = v := tendsto_nhds_unique_of_eventuallyEq hleft tendsto_const_nhds
    (he.eventuallyEq_of_mem self_mem_nhdsWithin)
  exact (he ht).trans hA.symm

/-- Transport identifies the existing first integral along an actual
characteristic at every interior radius, including both exceptional ones. -/
theorem canonicalGluedAiryIntegral_of_actual_ode
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {u : ℝ → ℝ} (hu : ContinuousOn u (Icc (C.left m) (C.right m)))
    (hflow : ∀ r ∈ Ioo (C.left m) (C.right m),
      HasDerivAt u ((L.coefficients z).b (r, u r) / (L.coefficients z).a (r, u r) -
        σ * Real.sqrt ((L.coefficients z).b (r, u r) ^ 2 -
          (L.coefficients z).a (r, u r) * (L.coefficients z).c (r, u r)) /
            (L.coefficients z).a (r, u r)) r)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    canonicalGluedAiryIntegral S K z m σ (r, u r) =
      (K.chart z (K.cutPair m).1 (C.left m, u (C.left m))).2 := by
  let U : PolarPoint → ℝ := canonicalGluedAiryIntegral S K z m σ
  let N : Set PolarPoint := Ioo (C.left m) (C.right m) ×ˢ univ
  let c : ℝ := (canonicalCutPoint S K z m 0).1
  let d : ℝ := (canonicalCutPoint S K z m (Real.pi / 2)).1
  have hN : IsOpen N := isOpen_Ioo.prod isOpen_univ
  have hU : ContDiffOn ℝ 1 U N := contDiffOn_canonicalGluedAiryIntegral hA hB hz hs m σ
  have hc : c ∈ Ioo (C.left m) (C.right m) :=
    ((hB.1.2 z hz hs m).2.1 (mem_range_self (0 : ℝ))).1
  have hd : d ∈ Ioo (C.left m) (C.right m) :=
    ((hB.1.2 z hz hs m).2.1 (mem_range_self (Real.pi / 2))).1
  have hpath : ContinuousOn (fun t : ℝ => (t, u t)) (Ioo (C.left m) (C.right m)) :=
    continuousOn_id.prodMk (hu.mono Ioo_subset_Icc_self)
  have hf : ContinuousOn (fun t => U (t, u t)) (Ioo (C.left m) (C.right m)) :=
    hU.continuousOn.comp hpath (fun t ht => ⟨ht, mem_univ _⟩)
  have hzero (t : ℝ) (ht : t ∈ Ioo (C.left m) (C.right m))
      (htc : t ≠ c) (htd : t ≠ d) : HasDerivAt (fun s => U (s, u s)) 0 t := by
    have hp : (t, u t) ∈ N := ⟨ht, mem_univ _⟩
    have haxis : (t, u t) ∈ Set.range (canonicalCutPoint S K z m) →
        Real.sin (2 * (t, u t).2) ≠ 0 := by
      intro hcut hsin
      rcases canonicalCut_axis_radial_cases hA hB.1.1 hz hs m hcut hsin with h | h
      · exact htc h
      · exact htd h
    have htransport := canonicalGluedAiryIntegral_characteristic_transport
      hS hT hN01 hN03 hA hB hz hs m hσ hp haxis
    have hUd : DifferentiableAt ℝ U (t, u t) :=
      ((hU (t, u t) hp).contDiffAt (hN.mem_nhds hp)).differentiableAt_one
    have hh := hUd.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hflow t ht))
    have he : U ∘ (fun s : ℝ => (s, u s)) = (fun s : ℝ => U (s, u s)) := by
      funext s
      exact Function.comp_apply
    simp only [id_eq] at hh
    rw [he] at hh
    apply hh.congr_deriv
    rw [polarCLM_apply_decompose]
    change 1 * radialPartial U (t, u t) +
      ((L.coefficients z).b (t, u t) / (L.coefficients z).a (t, u t) -
        σ * Real.sqrt ((L.coefficients z).b (t, u t) ^ 2 -
          (L.coefficients z).a (t, u t) * (L.coefficients z).c (t, u t)) /
            (L.coefficients z).a (t, u t)) * angularPartial U (t, u t) = 0
    rw [htransport]
    ring
  have hleft : Tendsto (fun t => U (t, u t))
      (𝓝[Ioo (C.left m) (C.right m)] (C.left m))
      (𝓝 ((K.chart z (K.cutPair m).1 (C.left m, u (C.left m))).2)) := by
    simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using
      canonicalGluedAiryIntegral_tendsto_endpoint hA hB hz hs m false σ hu
  exact eq_left_trace_of_hasDerivAt_zero_off_pair hc hd hf hzero hleft hr

section ActualN03

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hN01 : N01Properties D T S C base loss ε)
  (hN02 : N02Properties D T S C R base ε)
  (hN03 : N03Properties D T S C R L base ε)
  (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1) (m : ℕ)

include hS hT hN01 hN02 hN03 hA hB hz hs

/-- Both first integrals have their actual N01 boundary value along the
original N03 minus flow and its reflected plus flow. -/
theorem canonicalGluedAiryIntegral_on_n03Flows
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    canonicalGluedAiryIntegral S K z m 1 (r, L.minusFlow z m r θ) =
        stateLeftChart S z.1 m θ ∧
      canonicalGluedAiryIntegral S K z m (-1) (r, -L.minusFlow z m r (-θ)) =
        stateLeftChart S z.1 m θ := by
  have hminus := hN03.2.2.2.2.1 z hz hs m θ
  have hreflected := hN03.2.2.2.2.1 z hz hs m (-θ)
  have hplusFlow (t : ℝ) (ht : t ∈ Ioo (C.left m) (C.right m)) :
      HasDerivAt (fun s => -L.minusFlow z m s (-θ))
        ((L.coefficients z).b (t, -L.minusFlow z m t (-θ)) /
            (L.coefficients z).a (t, -L.minusFlow z m t (-θ)) -
          (-1 : ℝ) * Real.sqrt ((L.coefficients z).b (t, -L.minusFlow z m t (-θ)) ^ 2 -
            (L.coefficients z).a (t, -L.minusFlow z m t (-θ)) *
              (L.coefficients z).c (t, -L.minusFlow z m t (-θ))) /
            (L.coefficients z).a (t, -L.minusFlow z m t (-θ))) t := by
    obtain ⟨ha, hb, hc⟩ := hN03.2.2.2.1 z hz hs t (L.minusFlow z m t (-θ))
    have hd := (hreflected.2.2.1 t ht).fun_neg
    rw [neg_minusCharacteristicSpeed_eq_plus_of_reflection ha hb hc] at hd
    simpa only [plusCharacteristicSpeed, neg_one_mul, neg_div, sub_neg_eq_add] using hd
  have hm := canonicalGluedAiryIntegral_of_actual_ode
    hS hT hN01 hN03 hA hB hz hs m (σ := 1) (Or.inl rfl)
    hminus.2.1 (fun t ht => by
      simpa only [minusCharacteristicSpeed, one_mul] using hminus.2.2.1 t ht) hr
  have hp := canonicalGluedAiryIntegral_of_actual_ode
    hS hT hN01 hN03 hA hB hz hs m (σ := -1) (Or.inr rfl)
    hreflected.2.1.neg hplusFlow hr
  rw [hminus.1] at hm
  simp only [Pi.neg_apply] at hp
  rw [hreflected.1, neg_neg] at hp
  have hgauge := (canonicalRootGauges_eq_n01_of_n03
    hS hT hN01 hN02 hN03 hA hB hz hs m).2.1 θ
  exact ⟨hm.trans hgauge, hp.trans hgauge⟩

/-- Injectivity of each stored angular slice follows from the transported
first integral and the strictly increasing N01 left gauge. -/
theorem n03CharacteristicSlice_injective
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    Function.Injective (L.minusFlow z m r) ∧
      Function.Injective (fun θ => -L.minusFlow z m r (-θ)) := by
  have hl : Function.Injective (stateLeftChart S z.1 m) :=
    (strictMono_of_deriv_pos (f := stateLeftChart S z.1 m) (fun θ =>
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (hN01.2.2.2.2.2.2.2.1 z hz hs m θ).1)).injective
  have ht := canonicalGluedAiryIntegral_on_n03Flows
    hS hT hN01 hN02 hN03 hA hB hz hs m hr
  constructor
  · intro θ η he
    apply hl
    rw [← (ht θ).1, ← (ht η).1, he]
  · intro θ η he
    change -L.minusFlow z m r (-θ) = -L.minusFlow z m r (-η) at he
    apply hl
    rw [← (ht θ).2, ← (ht η).2, he]

/-- Once the actual minus slice is onto, both first integrals are exactly
the stored characteristic footpoint formulas. Surjectivity here is a
single ordinary flow-slice property, not a quantitative coordinate bound. -/
theorem canonicalGluedAiryIntegral_eq_storedFootpoints_of_surjective
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m))
    (honto : Function.Surjective (L.minusFlow z m r)) (θ : ℝ) :
    canonicalGluedAiryIntegral S K z m 1 (r, θ) =
        stateLeftChart S z.1 m (Function.invFun (L.minusFlow z m r) θ) ∧
      canonicalGluedAiryIntegral S K z m (-1) (r, θ) =
        stateLeftChart S z.1 m
          (Function.invFun (fun η => -L.minusFlow z m r (-η)) θ) := by
  have ht := canonicalGluedAiryIntegral_on_n03Flows
    hS hT hN01 hN02 hN03 hA hB hz hs m hr
  have hplus : Function.Surjective (fun η => -L.minusFlow z m r (-η)) := by
    intro η
    obtain ⟨φ, hφ⟩ := honto (-η)
    refine ⟨-φ, ?_⟩
    simp only [neg_neg, hφ]
  have hm := (ht (Function.invFun (L.minusFlow z m r) θ)).1
  have hp := (ht (Function.invFun (fun η => -L.minusFlow z m r (-η)) θ)).2
  have hpr : -L.minusFlow z m r
      (-(Function.invFun (fun η => -L.minusFlow z m r (-η)) θ)) = θ :=
    Function.rightInverse_invFun hplus θ
  rw [Function.rightInverse_invFun honto θ] at hm
  rw [hpr] at hp
  exact ⟨hm, hp⟩

end ActualN03

end ContinuousFlexibility.Analysis
