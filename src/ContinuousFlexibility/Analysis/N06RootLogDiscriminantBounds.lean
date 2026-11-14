module

public import ContinuousFlexibility.Analysis.N06PhysicalRootLogHeight

/-!
# Weighted finite jets of the actual root log-discriminant

The original N01 profile germ identifies the actual discriminant with
the finite normalized formula at each true turning root. Absorbing the
parameter into the decaying height entries preserves the factor
`H^(3/4) M |q|`. N01 bounds the discriminant below on the whole parameter
segment, so taking its logarithm preserves this factor in every fixed
finite spatial jet.

These estimates use the physical fields, before choosing any chart or
angular gauge. The oriented version is the precise discriminant term in
the genuine root log-height identity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

def n06RootLogDiscriminant (v : N06RootNormalizedCoordinates) : ℝ :=
  Real.log (n06RootNormalizedDiscriminant v)

theorem n06RootLogDiscriminant_contDiffAt {v : N06RootNormalizedCoordinates}
    (hD : n06RootNormalizedDiscriminant v ≠ 0) :
    ContDiffAt ℝ ∞ n06RootLogDiscriminant v :=
  n06RootNormalizedDiscriminant_contDiff.contDiffAt.log hD

private theorem n06_rootLogDiscriminant_finite_derivative_bound (M : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, k ≤ n → ∀ v : N06RootNormalizedCoordinates,
      ‖v‖ ≤ M → (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant v →
        ‖iteratedFDeriv ℝ k n06RootLogDiscriminant v‖ ≤ C := by
  classical
  let A : Set N06RootNormalizedCoordinates := Metric.closedBall 0 M ∩
    {v | (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant v}
  have hA : IsCompact A := (isCompact_closedBall (0 : N06RootNormalizedCoordinates) M).inter_right
    (isClosed_le continuous_const n06RootNormalizedDiscriminant_contDiff.continuous)
  have hchoices (i : Fin (n + 1)) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ A,
        ‖iteratedFDeriv ℝ i.val n06RootLogDiscriminant v‖ ≤ C := by
    have hc : ContinuousOn
        (fun v => ‖iteratedFDeriv ℝ i.val n06RootLogDiscriminant v‖) A := by
      intro v hv
      have hD : 0 < n06RootNormalizedDiscriminant v :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hv.2
      exact ((n06RootLogDiscriminant_contDiffAt hD.ne').continuousAt_iteratedFDeriv
        (by simp)).norm.continuousWithinAt
    obtain ⟨C, hC⟩ := (hA.image_of_continuousOn hc).bddAbove
    exact ⟨max C 0, le_max_right _ _, fun v hv =>
      (hC ⟨v, hv, rfl⟩).trans (le_max_left _ _)⟩
  choose c hc hb using hchoices
  refine ⟨∑ i : Fin (n + 1), c i, Finset.sum_nonneg (fun i _ => hc i), ?_⟩
  intro k hk v hv hD
  let i : Fin (n + 1) := ⟨k, by omega⟩
  have hvA : v ∈ A :=
    ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hv, hD⟩
  exact (hb i v hvA).trans
    (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i))

/-- One finite-dimensional constant controls every jet through the
chosen order. The lower bound is needed only along the actual segment. -/
theorem n06RootLogDiscriminant_composition_difference_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ (u v : E → N06RootNormalizedCoordinates) (x : E) (δ : ℝ),
      ContDiffAt ℝ ∞ u x → ContDiffAt ℝ ∞ v x → 0 ≤ δ →
      (∀ k, k ≤ n → ‖iteratedFDeriv ℝ k u x‖ ≤ M) →
      (∀ k, k ≤ n → ‖iteratedFDeriv ℝ k v x‖ ≤ M) →
      (∀ k, k ≤ n → ‖iteratedFDeriv ℝ k u x - iteratedFDeriv ℝ k v x‖ ≤ δ) →
      (∀ w ∈ segment ℝ (v x) (u x),
        (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant w) →
      ∀ k, k ≤ n →
        ‖iteratedFDeriv ℝ k (n06RootLogDiscriminant ∘ u) x -
          iteratedFDeriv ℝ k (n06RootLogDiscriminant ∘ v) x‖ ≤ Q * δ := by
  classical
  obtain ⟨C, hC, houter⟩ := n06_rootLogDiscriminant_finite_derivative_bound M (n + 1)
  let Q : ℝ := ∑ i : Fin (n + 1), n06CompositionDifferenceCost i.val C M
  have hcost (i : Fin (n + 1)) : 0 ≤ n06CompositionDifferenceCost i.val C M :=
    n06CompositionDifferenceCost_nonneg i.val hC hM
  refine ⟨Q, Finset.sum_nonneg (fun i _ => hcost i), ?_⟩
  intro u v x δ hu hv hδ hU hV hUV hpositive
  have hu₀ : ‖u x‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using hU 0 (Nat.zero_le n)
  have hv₀ : ‖v x‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using hV 0 (Nat.zero_le n)
  have hdiff₀ : ‖u x - v x‖ ≤ δ := by
    have he := iteratedFDeriv_sub_apply
      (hu.of_le (by simp : (0 : ℕ∞ω) ≤ ∞))
      (hv.of_le (by simp : (0 : ℕ∞ω) ≤ ∞))
    have h := hUV 0 (Nat.zero_le n)
    rw [← he, norm_iteratedFDeriv_zero] at h
    exact h
  have hvalue : ∀ w ∈ segment ℝ (v x) (u x), ‖w‖ ≤ M := by
    intro w hw
    have hvB : v x ∈ Metric.closedBall (0 : N06RootNormalizedCoordinates) M := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hv₀
    have huB : u x ∈ Metric.closedBall (0 : N06RootNormalizedCoordinates) M := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hu₀
    have hwB := (convex_closedBall (0 : N06RootNormalizedCoordinates) M).segment_subset hvB huB hw
    simpa only [Metric.mem_closedBall, dist_zero_right] using hwB
  have hsmooth : ∀ w ∈ segment ℝ (v x) (u x),
      ContDiffAt ℝ ∞ n06RootLogDiscriminant w := by
    intro w hw
    exact n06RootLogDiscriminant_contDiffAt
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hpositive w hw)).ne'
  have hΦu := hsmooth (u x) (right_mem_segment ℝ _ _)
  have hΦv := hsmooth (v x) (left_mem_segment ℝ _ _)
  intro k hk
  have houterValue (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j n06RootLogDiscriminant (u x)‖ ≤ C :=
    houter j (by omega) (u x) hu₀ (hpositive _ (right_mem_segment ℝ _ _))
  have houterDifference (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j n06RootLogDiscriminant (u x) -
        iteratedFDeriv ℝ j n06RootLogDiscriminant (v x)‖ ≤ C * δ := by
    have h := n06_iteratedFDeriv_difference_le_segment j hsmooth
      (fun w hw => houter (j + 1) (by omega) w (hvalue w hw) (hpositive w hw))
    exact h.trans (mul_le_mul_of_nonneg_left hdiff₀ hC)
  have h := n06_iteratedFDeriv_comp_difference_le k hΦu hΦv hu hv hC hM hδ
    houterValue houterDifference
    (fun j hj => hU j (hj.trans hk)) (fun j hj => hV j (hj.trans hk))
    (fun j hj => hUV j (hj.trans hk))
  let i : Fin (n + 1) := ⟨k, by omega⟩
  have hi : n06CompositionDifferenceCost k C M ≤ Q :=
    Finset.single_le_sum (fun j _ => hcost j) (Finset.mem_univ i)
  exact h.trans (mul_le_mul_of_nonneg_right hi hδ)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The N01 root clause supplies a genuine two-variable germ, so the
finite formula identifies all actual spatial derivatives. -/
theorem n06_rootLogDiscriminant_germ_eq_absorbed
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {r : ℝ} (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0) (θ : ℝ) :
    (fun p => Real.log (polarDiscriminant (stateProfile D S C z.1)
      (stateHeight D S C z) p)) =ᶠ[𝓝 (r, θ)]
        n06RootLogDiscriminant ∘ n06ActualRootAbsorbedCoordinates D S z := by
  have hprofile := hN01.2.2.2.2.2.2.2.2.2.2.1 z hz r hr hroot
  have hprofile' := hprofile.comp_tendsto (continuous_fst.tendsto (r, θ))
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  filter_upwards [hprofile', hU.mem_nhds ⟨hr, mem_univ θ⟩] with p hp hpm
  have hr0 : p.1 ≠ 0 := (hN01.1.1.choose_spec.1.1.trans hpm.1.1).ne'
  have hw : D.w p.1 ≠ 0 := (hN01.1.1.choose_spec.1.2.2.2.2.1 _ hpm.1).ne'
  have he := (n06_actualRootAbsorbed_denominators D S z p).2.trans
    ((n06_normalizeRoot_denominators (v := n06ActualNuJetCoordinates D S z p) hw).2.trans
      (n06_rootFinite_denominators_eq hT hS hN01 z hr0 hp).2)
  exact congrArg Real.log he.symm

private theorem n06_rootLogDiscriminant_absorbed_zero_parameter
    (D : ReferenceData) (S : PhysicalSpacesData) (x : AnnularState S) :
    n06RootLogDiscriminant ∘ n06ActualRootAbsorbedCoordinates D S (x, 0) =
      fun _ : PolarPoint => (0 : ℝ) := by
  funext p
  change Real.log (n06RootNormalizedDiscriminant
    (n06ActualRootAbsorbedCoordinates D S (x, 0) p)) = 0
  rw [(n06_actualRootAbsorbed_denominators D S (x, 0) p).2]
  have hq : n06ActualRootNormalizedCoordinates D S (x, 0) p 5 = 0 := rfl
  have hD : n06RootNormalizedDiscriminant
      (n06ActualRootNormalizedCoordinates D S (x, 0) p) = 1 := by
    simp only [n06RootNormalizedDiscriminant, hq, zero_mul,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, mul_one, add_zero]
    ring
  rw [hD, Real.log_one]

def N06RootLogDiscriminantFiniteJetsBound (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (base n : ℕ) (ε Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (n + 7) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∀ r ∈ radialCore D, deriv D.w r = 0 → ∀ θ : ℝ, ∀ k, k ≤ n →
      ‖iteratedFDeriv ℝ k (fun p => Real.log
        (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p)) (r, θ)‖ ≤
          Q * n06RootJetWeight T (r, θ) * |z.2|

/-- The constant is chosen before the state, physical turning root and
angle. The actual material factor is retained, with no chart hypothesis. -/
theorem n06_rootLogDiscriminant_finite_weighted_jets
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06RootLogDiscriminantFiniteJetsBound D T S C base n ε Q := by
  let R : ℝ := stateGrading S (n + 7) C.referenceState + 1
  have hR : 0 ≤ R := add_nonneg (apply_nonneg _ _) zero_le_one
  obtain ⟨M, hM, hpacket⟩ := n06_actualRootAbsorbedCoordinates_spatial_bound
    hN01.1.1 hT hS n hR
  obtain ⟨A, hA, hdifference⟩ := n06_actualRootAbsorbedCoordinates_weighted_difference_bound
    hN01.1.1 hT hS n
  obtain ⟨Q, hQ, hcomposition⟩ :=
    n06RootLogDiscriminant_composition_difference_bound (E := PolarPoint) n hM
  refine ⟨Q * A * R, mul_nonneg (mul_nonneg hQ hA) hR, ?_⟩
  intro z hz hs hsmall r hr hroot θ k hk
  have hgrade : stateGrading S (n + 7) (z.1 - C.referenceState) ≤ 1 :=
    (le_add_of_nonneg_right (abs_nonneg z.2)).trans hsmall
  have hstate : stateGrading S (n + 7) z.1 ≤ R := by
    calc
      stateGrading S (n + 7) z.1 ≤
          stateGrading S (n + 7) (z.1 - C.referenceState) +
            stateGrading S (n + 7) C.referenceState := by
        simpa only [sub_add_cancel] using map_add_le_add
          (stateGrading S (n + 7)) (z.1 - C.referenceState) C.referenceState
      _ ≤ 1 + stateGrading S (n + 7) C.referenceState := add_le_add hgrade le_rfl
      _ = R := add_comm _ _
  have hq : |z.2| ≤ 1 := (le_add_of_nonneg_left
    (apply_nonneg (stateGrading S (n + 7)) (z.1 - C.referenceState))).trans hsmall
  have hp : (r, θ) ∈ annularOpen D := ⟨hr, mem_univ θ⟩
  have hW : 0 ≤ n06RootJetWeight T (r, θ) := n06_rootJetWeight_nonneg hT hp
  have hu := n06_actualRootAbsorbedCoordinates_contDiff hN01.1.1 hT hS z
  have hv := n06_actualRootAbsorbedCoordinates_contDiff hN01.1.1 hT hS (z.1, 0)
  have hdiff (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDeriv ℝ j (n06ActualRootAbsorbedCoordinates D S z) (r, θ) -
        iteratedFDeriv ℝ j (n06ActualRootAbsorbedCoordinates D S (z.1, 0)) (r, θ)‖ ≤
          A * n06RootJetWeight T (r, θ) * R * |z.2| :=
    (hdifference z j hj (r, θ) hp).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hstate (mul_nonneg hA hW)) (abs_nonneg _))
  have hbound := hcomposition
    (n06ActualRootAbsorbedCoordinates D S z)
    (n06ActualRootAbsorbedCoordinates D S (z.1, 0)) (r, θ)
    (A * n06RootJetWeight T (r, θ) * R * |z.2|) hu.contDiffAt hv.contDiffAt
    (mul_nonneg (mul_nonneg (mul_nonneg hA hW) hR) (abs_nonneg _))
    (fun j hj => hpacket z hstate hq j hj (r, θ) hp)
    (fun j hj => hpacket (z.1, 0) hstate (by norm_num) j hj (r, θ) hp)
    hdiff (fun w hw =>
      (n06_actualRootAbsorbed_denominators_segment_lower hT hS hN01 hz hs hr hroot θ w hw).2)
    k hk
  simp only [n06_rootLogDiscriminant_absorbed_zero_parameter,
    iteratedFDeriv_fun_zero, Pi.zero_apply, sub_zero] at hbound
  have hgerm := n06_rootLogDiscriminant_germ_eq_absorbed hT hS hN01 hz hr hroot θ
  have he := (hgerm.iteratedFDeriv ℝ k).eq_of_nhds
  exact ((congrArg norm he).trans_le hbound).trans_eq (by ring)

def N06RootLogDiscriminantOrientedFiniteJetsBound (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (base n : ℕ) (ε Q : ℝ) : Prop :=
    ∀ z : AnnularState S × ℝ,
      z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
      stateGrading S (n + 7) (z.1 - C.referenceState) + |z.2| ≤ 1 →
      ∀ r ∈ radialCore D, deriv D.w r = 0 → ∀ ι : ℝ, (ι = 1 ∨ ι = -1) →
      ∀ θ : ℝ, ∀ k, k ≤ n →
        ‖iteratedFDeriv ℝ k (fun p => Real.log
          (n06RootPhysicalDiscriminant (stateProfile D S C z.1)
            (stateHeight D S C z) r ι p)) (0, θ)‖ ≤
          Q * n06RootJetWeight T (r, θ) * |z.2|

private theorem n06_rootLogDiscriminant_orient_bound {n : ℕ} {Q : ℝ}
    (hbound : N06RootLogDiscriminantFiniteJetsBound D T S C base n ε Q) :
    N06RootLogDiscriminantOrientedFiniteJetsBound D T S C base n ε Q := by
  intro z hz hs hsmall r hr hroot ι hι θ k hk
  let f : PolarPoint → ℝ := fun p => Real.log
    (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p)
  have hb : ‖iteratedFDeriv ℝ k f (r, θ)‖ ≤
      Q * n06RootJetWeight T (r, θ) * |z.2| :=
    hbound z hz hs hsmall r hr hroot θ k hk
  have he : ‖iteratedFDeriv ℝ k (f ∘ rootProfileShift r ι) (0, θ)‖ =
      ‖iteratedFDeriv ℝ k f (r, θ)‖ := by
    simpa only [n06_rootProfileShift_boundary] using
      n06_norm_iteratedFDeriv_rootProfileShift f r ι hι k (0, θ)
  change ‖iteratedFDeriv ℝ k (f ∘ rootProfileShift r ι) (0, θ)‖ ≤ _
  exact he.trans_le hb

/-- The same bound applies to both physical radial orientations, with
no loss from the actual translation or reflection. This is the term in
`n06_N01_rootLogHeight_difference_boundaryJets`. -/
theorem n06_rootLogDiscriminant_oriented_finite_weighted_jets
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z : AnnularState S × ℝ,
      z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
      stateGrading S (n + 7) (z.1 - C.referenceState) + |z.2| ≤ 1 →
      ∀ r ∈ radialCore D, deriv D.w r = 0 → ∀ ι : ℝ, (ι = 1 ∨ ι = -1) →
      ∀ θ : ℝ, ∀ k, k ≤ n →
        ‖iteratedFDeriv ℝ k (fun p => Real.log
          (n06RootPhysicalDiscriminant (stateProfile D S C z.1)
            (stateHeight D S C z) r ι p)) (0, θ)‖ ≤
          Q * n06RootJetWeight T (r, θ) * |z.2| := by
  change ∃ Q : ℝ, 0 ≤ Q ∧
    N06RootLogDiscriminantOrientedFiniteJetsBound D T S C base n ε Q
  obtain ⟨Q, hQ, hbound⟩ := n06_rootLogDiscriminant_finite_weighted_jets hT hS hN01 n
  exact ⟨Q, hQ, n06_rootLogDiscriminant_orient_bound hbound⟩

end ContinuousFlexibility.Statements
