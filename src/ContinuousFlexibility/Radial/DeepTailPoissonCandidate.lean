module

public import ContinuousFlexibility.Radial.DeepTailSmoothInterpolation
public import ContinuousFlexibility.Radial.DeepTailCandidateIdentification
public import ContinuousFlexibility.Radial.DeepTailShiftInterpolation
public import ContinuousFlexibility.Radial.DeepTailJacobiData
public import ContinuousFlexibility.Radial.TailNaturalNodeContinuity

/-!
# Canonical physical candidates and entrance normalization

The signed continued-fraction nodes determine actual Poisson pieces. Their
Jacobi recurrence is precisely equality of the two physical fluxes at each
node. The resulting `morseOutwardGlue` is identified with the original
natural line after shifting once into the tail.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- The physical node values undo the alternating-sign Jacobi convention. -/
def tailPoissonCanonicalValues (b c : ℕ → ℝ)
    (hε : ∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8)) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * tailNodesFromRatio (tailNaturalNodeRatio b c hε) n

@[simp] theorem tailPoissonCanonicalValues_zero (b c : ℕ → ℝ)
    (hε : ∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8)) :
    tailPoissonCanonicalValues b c hε 0 = 1 := by
  simp [tailPoissonCanonicalValues]

@[simp] theorem tailPoissonCanonicalValues_one (b c : ℕ → ℝ)
    (hε : ∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8)) :
    tailPoissonCanonicalValues b c hε 1 = -tailNaturalNodeRatio b c hε 0 := by
  simp [tailPoissonCanonicalValues, tailNodesFromRatio_succ]

theorem tailPoissonCanonicalValues_properties {b c μ : ℕ → ℝ}
    (hb : ∀ n, 0 < b n) (hc : ∀ n, 0 < c n) (hμ : ∀ n, 0 < μ n)
    (hε : ∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8))
    (hr : ∀ n, Real.sqrt (μ (n + 1)) * (c n / b (n + 1)) ≤
      (1 / 4 : ℝ) * Real.sqrt (μ n)) :
    let A := tailPoissonCanonicalValues b c hε
    (∀ n, A n ≠ 0) ∧
      (∀ n, -b (n + 1) * A (n + 1) = c n * A n + c (n + 1) * A (n + 2)) ∧
      Summable (fun n => μ n * A n ^ 2) := by
  have hy := tailNaturalNodes_properties hb hc hμ hε hr
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact mul_ne_zero (pow_ne_zero n (by norm_num)) (hy.1 n).ne'
  · intro n
    exact tailNaturalNodes_signed_recurrence hy.2.1 n
  · exact tailNaturalNodes_signed_summable hy.2.2.2

/-- The signed Jacobi recurrence is the equality of actual adjacent fluxes. -/
theorem tailPoisson_fluxMatch_of_signed_recurrence
    {node : ℕ → ℝ} {p : ℝ → ℝ} {Λ η b₀ : ℝ}
    (hmono : StrictMono node)
    (hp : ∀ n, ContinuousOn p (Icc (node n) (node (n + 1))))
    (B : ∀ n, TailPhysicalPoissonData p (node n) (node (n + 1)) Λ η
      (hmono (Nat.lt_succ_self n)).le)
    {A : ℕ → ℝ}
    (hrec : ∀ n, -tailPoissonJacobiDiagonal B b₀ (n + 1) * A (n + 1) =
      tailPoissonJacobiOffDiagonal B n * A n +
        tailPoissonJacobiOffDiagonal B (n + 1) * A (n + 2)) (n : ℕ) :
    p (node (n + 1)) * deriv ((B n).interpolate (A n) (A (n + 1))) (node (n + 1)) =
      p (node (n + 1)) *
        deriv ((B (n + 1)).interpolate (A (n + 1)) (A (n + 1 + 1))) (node (n + 1)) := by
  rw [(B n).interpolate_right_flux (hmono (Nat.lt_succ_self n)) (hp n),
    (B (n + 1)).interpolate_left_flux (hmono (Nat.lt_succ_self (n + 1)))]
  have h := hrec n
  simp only [tailPoissonJacobiDiagonal_succ, tailPoissonJacobiOffDiagonal_apply] at h
  nlinarith only [h]

theorem deepTail_Poisson_canonical_data {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 64 ≤ T.K)
    (B : ∀ n, TailPhysicalPoissonData T.p (T.node n) (T.node (n + 1)) T.Λ T.η
      (deepTail_node_strictMono hT (Nat.lt_succ_self n)).le)
    {b₀ : ℝ} (hb₀ : T.Λ * tailMass T 0 / 4 ≤ b₀)
    (hε : ∀ n, (tailPoissonJacobiOffDiagonal B n) ^ 2 /
      (tailPoissonJacobiDiagonal B b₀ n * tailPoissonJacobiDiagonal B b₀ (n + 1)) ∈
        Icc 0 (1 / 8)) :
    let A := tailPoissonCanonicalValues (tailPoissonJacobiDiagonal B b₀)
      (tailPoissonJacobiOffDiagonal B) hε
    (∀ n, A n ≠ 0) ∧
      (∀ n, T.p (T.node (n + 1)) *
        deriv ((B n).interpolate (A n) (A (n + 1))) (T.node (n + 1)) =
          T.p (T.node (n + 1)) *
            deriv ((B (n + 1)).interpolate (A (n + 1)) (A (n + 1 + 1)))
              (T.node (n + 1))) ∧
      Summable (fun n => tailMass T n * A n ^ 2) := by
  have hb (n : ℕ) : 0 < tailPoissonJacobiDiagonal B b₀ n :=
    (div_pos (mul_pos hT.2.2.1 (tailMass_pos hT n)) (by norm_num)).trans_le
      (deepTail_Poisson_jacobiDiagonal_bound hT hη hK B hb₀ n)
  have hsmall := deepTail_Poisson_jacobi_smallness hT hη hK B hb₀
  have hA := tailPoissonCanonicalValues_properties hb
    (deepTail_Poisson_offDiagonal_pos hT B) (tailMass_pos hT) hε hsmall.2
  exact ⟨hA.1, tailPoisson_fluxMatch_of_signed_recurrence
    (deepTail_node_strictMono hT) (deepTail_edge_continuous hT) B hA.2.1, hA.2.2⟩

/-- Closed-edge identities provide the only integrability input needed to
normalize the original smooth natural representative. -/
theorem exists_tailNatural_normalized_of_Poisson_edge_candidate
    {C η₀ K₀ : ℝ} (hfull : ContinuousFlexibility.Blueprint.R06Full C η₀ K₀)
    {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hη₀ : T.η ≤ η₀) (hK₀ : K₀ ≤ T.K)
    (hη : T.η ≤ 1 / 16) (hK : 64 ≤ T.K)
    (B : ∀ n, TailPhysicalPoissonData T.p (T.node n) (T.node (n + 1)) T.Λ T.η
      (deepTail_node_strictMono hT (Nat.lt_succ_self n)).le)
    {A : ℕ → ℝ} {v : ℝ → ℝ} {e L : ℝ}
    (hva : ContDiffAt ℝ 1 v T.entrance)
    (hvs : ContDiffOn ℝ ∞ v (Ioo T.entrance T.endpoint))
    (hvode : ∀ x ∈ Ioo T.entrance T.endpoint,
      deriv (fun y => T.p y * deriv v y) x + T.Λ * T.p x * v x = 0)
    (hedge : ∀ n x, x ∈ Icc (T.node n) (T.node (n + 1)) →
      v x = (B n).interpolate (A n) (A (n + 1)) x)
    (hsum : Summable (fun n => tailMass T n * A n ^ 2))
    (hA₂ : A 2 ≠ 0) (he : v T.entrance = e) (he₀ : e ≠ 0)
    (hflux : T.p T.entrance * deriv v T.entrance = L) :
    ∃ u : ℝ → ℝ, TailNaturalEquation T u ∧ u T.entrance = 1 ∧
      deriv u T.entrance = L / (T.p T.entrance * e) := by
  have hc : ContinuousOn v (Ioo (T.node 0) T.endpoint) :=
    hvs.continuousOn.mono fun x hx =>
      ⟨(deepTail_entrance_le_node hT 0).trans_lt hx.1, hx.2⟩
  have hce (n : ℕ) : ContinuousOn v (Icc (T.node n) (T.node (n + 1))) :=
    ((B n).interpolate_differentiable (A n) (A (n + 1))).continuous.continuousOn.congr
      (fun x hx => hedge n x hx)
  have hbound (n : ℕ) :
      (∫ x in T.node n..T.node (n + 1), T.p x * v x ^ 2) ≤
        16 * (tailMass T n * A n ^ 2 + tailMass T (n + 1) * A (n + 1) ^ 2) := by
    have heq : (∫ x in T.node n..T.node (n + 1), T.p x * v x ^ 2) =
        ∫ x in T.node n..T.node (n + 1),
          T.p x * (B n).interpolate (A n) (A (n + 1)) x ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (T.node n) (T.node (n + 1)) := by
        simpa only [uIcc_of_le (deepTail_node_strictMono hT (Nat.lt_succ_self n)).le]
          using hx
      exact congrArg (fun z : ℝ => T.p x * z ^ 2) (hedge n x hx')
    rw [heq]
    exact deepTail_Poisson_interpolate_square_bound hT hη hK B n (A n) (A (n + 1))
  have hvm := deepTail_memLp_shift_of_edge_square_bound hT 1 hc hce
    (by norm_num : (0 : ℝ) ≤ 16) hbound hsum
  have hvne : ∃ x ∈ Ioo (T.node 1) T.endpoint, v x ≠ 0 := by
    refine ⟨T.node 2, ⟨deepTail_node_strictMono hT (by omega),
      deepTail_node_lt_endpoint hT 2⟩, ?_⟩
    rw [hedge 2 (T.node 2) ⟨le_rfl, (deepTail_node_strictMono hT (by omega)).le⟩,
      (B 2).interpolate_left]
    exact hA₂
  obtain ⟨u, hu, hua, hud⟩ := exists_tailNatural_normalized_of_r06Full_candidate
    hfull hT hη₀ hK₀ (by norm_num : 0 < (1 : ℕ)) hva hvs hvm hvode hvne
    (by rw [he]; exact he₀)
  have hp₀ : T.p T.entrance ≠ 0 := (deepTail_pos hT _ ⟨le_rfl, hT.1⟩).ne'
  have hd : deriv v T.entrance = L / T.p T.entrance :=
    (eq_div_iff hp₀).mpr (by simpa only [mul_comm] using hflux)
  refine ⟨u, hu, hua, ?_⟩
  rw [hud, hd, he, div_div]

/-- With no initial edge, node zero already fixes the entrance value. The
auxiliary zeroth Jacobi diagonal is arbitrary subject to its lower bound. -/
theorem exists_tailNatural_normalized_noInitial
    {C η₀ K₀ : ℝ} (hfull : ContinuousFlexibility.Blueprint.R06Full C η₀ K₀)
    {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hη₀ : T.η ≤ η₀) (hK₀ : K₀ ≤ T.K)
    (hη : T.η ≤ 1 / 16) (hK : 64 ≤ T.K)
    (B : ∀ n, TailPhysicalPoissonData T.p (T.node n) (T.node (n + 1)) T.Λ T.η
      (deepTail_node_strictMono hT (Nat.lt_succ_self n)).le)
    (hstart : T.node 0 = T.entrance) (b₀ : ℝ)
    (hb₀ : T.Λ * tailMass T 0 / 4 ≤ b₀)
    (hε : ∀ n, (tailPoissonJacobiOffDiagonal B n) ^ 2 /
      (tailPoissonJacobiDiagonal B b₀ n * tailPoissonJacobiDiagonal B b₀ (n + 1)) ∈
        Icc 0 (1 / 8)) :
    ∃ u : ℝ → ℝ, TailNaturalEquation T u ∧ u T.entrance = 1 ∧
      deriv u T.entrance =
        (-(B 0).leftDiagonal - tailPoissonJacobiOffDiagonal B 0 *
          tailNaturalNodeRatio (tailPoissonJacobiDiagonal B b₀)
            (tailPoissonJacobiOffDiagonal B) hε 0) / T.p T.entrance := by
  let A := tailPoissonCanonicalValues (tailPoissonJacobiDiagonal B b₀)
    (tailPoissonJacobiOffDiagonal B) hε
  let v := morseOutwardGlue T.node (fun n => (B n).interpolate (A n) (A (n + 1)))
  have hA := deepTail_Poisson_canonical_data hT hη hK B hb₀ hε
  have hA₀ : A 0 = 1 := tailPoissonCanonicalValues_zero _ _ _
  have hA₁ : A 1 = -tailNaturalNodeRatio (tailPoissonJacobiDiagonal B b₀)
      (tailPoissonJacobiOffDiagonal B) hε 0 := tailPoissonCanonicalValues_one _ _ _
  have hmono := deepTail_node_strictMono hT
  have hlim : Tendsto T.node atTop (𝓝 T.endpoint) := hT.2.2.2.2.2.2.2.2.2.1
  have hs := smooth_tailPoissonInterpolation hmono hlim
    (by simpa only [hstart] using deepTail_contDiffOn hT)
    (by simpa only [hstart] using deepTail_pos hT) B A hA.2.1
  have hva : ContDiffAt ℝ 1 v T.entrance := by
    rw [← hstart]
    exact contDiffAt_one_morseOutwardGlue_first hmono
      ((B 0).interpolate_differentiable (A 0) (A 1))
      ((B 0).interpolate_derivative_continuous (A 0) (A 1))
  have hgerm : v =ᶠ[𝓝 (T.node 0)] (B 0).interpolate (A 0) (A 1) :=
    morseOutwardGlue_eventually_first hmono
  have he : v T.entrance = 1 := by
    rw [← hstart, hgerm.eq_of_nhds, (B 0).interpolate_left, hA₀]
  have hf : T.p T.entrance * deriv v T.entrance =
      -(B 0).leftDiagonal - tailPoissonJacobiOffDiagonal B 0 *
        tailNaturalNodeRatio (tailPoissonJacobiDiagonal B b₀)
          (tailPoissonJacobiOffDiagonal B) hε 0 := by
    rw [← hstart, hgerm.deriv_eq, (B 0).interpolate_left_flux
      (hmono (Nat.lt_succ_self 0)), hA₀, hA₁]
    simp only [tailPoissonJacobiOffDiagonal_apply]
    ring
  simpa only [mul_one] using exists_tailNatural_normalized_of_Poisson_edge_candidate
    hfull hT hη₀ hK₀ hη hK B hva
    (by simpa only [hstart] using hs.1)
    (by simpa only [hstart] using hs.2.1)
    hs.2.2.1 hA.2.2 (hA.1 2) he one_ne_zero hf

/-- Prepending one entrance edge preserves the common gluing convention. -/
def tailPoissonPrepend {α : Type*} (a : α) (f : ℕ → α) : ℕ → α
  | 0 => a
  | n + 1 => f n

theorem tailPoissonPrepend_strictMono {a : ℝ} {node : ℕ → ℝ}
    (ha : a < node 0) (hmono : StrictMono node) :
    StrictMono (tailPoissonPrepend a node) := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => exact ha
  | succ n => exact hmono (Nat.lt_succ_self n)

theorem tailPoissonPrepend_tendsto {a endpoint : ℝ} {node : ℕ → ℝ}
    (hlim : Tendsto node atTop (𝓝 endpoint)) :
    Tendsto (tailPoissonPrepend a node) atTop (𝓝 endpoint) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact hlim

/-- The initial edge fixes a nonzero entrance value by its exact flux
equation. Normalization is performed on the original natural solution. -/
theorem exists_tailNatural_normalized_initial
    {C η₀ K₀ : ℝ} (hfull : ContinuousFlexibility.Blueprint.R06Full C η₀ K₀)
    {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hη₀ : T.η ≤ η₀) (hK₀ : K₀ ≤ T.K)
    (hη : T.η ≤ 1 / 16) (hK : 64 ≤ T.K)
    (B : ∀ n, TailPhysicalPoissonData T.p (T.node n) (T.node (n + 1)) T.Λ T.η
      (deepTail_node_strictMono hT (Nat.lt_succ_self n)).le)
    (hinitial : T.entrance < T.node 0)
    (BI : TailPhysicalPoissonData T.p T.entrance (T.node 0) T.Λ T.η hinitial.le)
    (hε : ∀ n, (tailPoissonJacobiOffDiagonal B n) ^ 2 /
      (tailPoissonJacobiDiagonal B (-BI.rightDiagonal - (B 0).leftDiagonal) n *
        tailPoissonJacobiDiagonal B (-BI.rightDiagonal - (B 0).leftDiagonal) (n + 1)) ∈
          Icc 0 (1 / 8)) :
    ∃ u : ℝ → ℝ, TailNaturalEquation T u ∧ u T.entrance = 1 ∧
      deriv u T.entrance =
        (BI.offDiagonal - BI.leftDiagonal *
          tailNaturalInitialValue
            (tailPoissonJacobiDiagonal B (-BI.rightDiagonal - (B 0).leftDiagonal))
            (tailPoissonJacobiOffDiagonal B) BI.offDiagonal hε) /
        (T.p T.entrance *
          tailNaturalInitialValue
            (tailPoissonJacobiDiagonal B (-BI.rightDiagonal - (B 0).leftDiagonal))
            (tailPoissonJacobiOffDiagonal B) BI.offDiagonal hε) := by
  let b₀ := -BI.rightDiagonal - (B 0).leftDiagonal
  let b := tailPoissonJacobiDiagonal B b₀
  let c := tailPoissonJacobiOffDiagonal B
  let A := tailPoissonCanonicalValues b c hε
  let e := tailNaturalInitialValue b c BI.offDiagonal hε
  let node := tailPoissonPrepend T.entrance T.node
  let piece := tailPoissonPrepend (BI.interpolate e (A 0))
    (fun n => (B n).interpolate (A n) (A (n + 1)))
  let v := morseOutwardGlue node piece
  have hb₀ := deepTail_initialJacobiDiagonal_bound hT hη hK B hinitial BI
  have hA := deepTail_Poisson_canonical_data hT hη hK B hb₀ hε
  have hA₀ : A 0 = 1 := tailPoissonCanonicalValues_zero _ _ _
  have hA₁ : A 1 = -tailNaturalNodeRatio b c hε 0 := tailPoissonCanonicalValues_one _ _ _
  have hpI := (deepTail_contDiffOn hT).continuousOn.mono
    (deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0))
  have hposI : ∀ x ∈ Icc T.entrance (T.node 0), 0 < T.p x :=
    fun x hx => deepTail_pos hT x
      (deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0) hx)
  have hci : 0 < BI.offDiagonal := BI.offDiagonal_pos hinitial hpI hposI hT.2.2.1.le
  have hb (n : ℕ) : 0 < b n :=
    (div_pos (mul_pos hT.2.2.1 (tailMass_pos hT n)) (by norm_num)).trans_le
      (deepTail_Poisson_jacobiDiagonal_bound hT hη hK B hb₀ n)
  have he₀ : e ≠ 0 := (tailNaturalInitialValue_neg hb hci hε).ne
  have hinitflux : T.p (T.node 0) * deriv (BI.interpolate e (A 0)) (T.node 0) =
      T.p (T.node 0) * deriv ((B 0).interpolate (A 0) (A 1)) (T.node 0) := by
    rw [BI.interpolate_right_flux hinitial hpI, (B 0).interpolate_left_flux
      (deepTail_node_strictMono hT (Nat.lt_succ_self 0)), hA₀, hA₁]
    have hh := tailNaturalInitialValue_flux (b := b) (c := c) hci.ne'
      (show b 0 = -BI.rightDiagonal - (B 0).leftDiagonal from rfl) hε
    simpa only [e, c, mul_one, mul_neg, sub_eq_add_neg, tailPoissonJacobiOffDiagonal_apply]
      using hh
  have hmono : StrictMono node :=
    tailPoissonPrepend_strictMono hinitial (deepTail_node_strictMono hT)
  have hlim : Tendsto node atTop (𝓝 T.endpoint) :=
    tailPoissonPrepend_tendsto hT.2.2.2.2.2.2.2.2.2.1
  have hd (n : ℕ) : Differentiable ℝ (piece n) := by
    cases n with
    | zero => exact BI.interpolate_differentiable e (A 0)
    | succ n => exact (B n).interpolate_differentiable (A n) (A (n + 1))
  have hdc (n : ℕ) : Continuous (deriv (piece n)) := by
    cases n with
    | zero => exact BI.interpolate_derivative_continuous e (A 0)
    | succ n => exact (B n).interpolate_derivative_continuous (A n) (A (n + 1))
  have hode (n : ℕ) (x : ℝ) (hx : x ∈ Ioo (node n) (node (n + 1))) :
      HasDerivAt (fun y => T.p y * deriv (piece n) y) (-(T.Λ * T.p x * piece n x)) x := by
    cases n with
    | zero => exact BI.interpolate_equation e (A 0) hx
    | succ n => exact (B n).interpolate_equation (A n) (A (n + 1)) hx
  have hmatch (n : ℕ) : piece n (node (n + 1)) = piece (n + 1) (node (n + 1)) := by
    cases n with
    | zero =>
      exact (BI.interpolate_right e (A 0)).trans
        ((B 0).interpolate_left (A 0) (A 1)).symm
    | succ n =>
      exact ((B n).interpolate_right (A n) (A (n + 1))).trans
        ((B (n + 1)).interpolate_left (A (n + 1)) (A (n + 1 + 1))).symm
  have hflux (n : ℕ) : T.p (node (n + 1)) * deriv (piece n) (node (n + 1)) =
      T.p (node (n + 1)) * deriv (piece (n + 1)) (node (n + 1)) := by
    cases n with
    | zero => exact hinitflux
    | succ n => exact hA.2.1 n
  have hs := smooth_morseOutwardGlue_of_fluxMatch hmono hlim
    (deepTail_contDiffOn hT) (deepTail_pos hT) hd hdc hode hmatch hflux
  have hva : ContDiffAt ℝ 1 v T.entrance :=
    contDiffAt_one_morseOutwardGlue_first hmono (hd 0) (hdc 0)
  have hgerm : v =ᶠ[𝓝 T.entrance] BI.interpolate e (A 0) :=
    morseOutwardGlue_eventually_first hmono
  have he : v T.entrance = e := by
    rw [hgerm.eq_of_nhds, BI.interpolate_left]
  have hedge (n : ℕ) (x : ℝ) (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
      v x = (B n).interpolate (A n) (A (n + 1)) x :=
    hs.2.2.1 (n + 1) x hx
  have hf : T.p T.entrance * deriv v T.entrance = BI.offDiagonal - BI.leftDiagonal * e := by
    rw [hgerm.deriv_eq, BI.interpolate_left_flux hinitial, hA₀]
    ring
  exact exists_tailNatural_normalized_of_Poisson_edge_candidate
    hfull hT hη₀ hK₀ hη hK B hva hs.1 hs.2.1 hedge hA.2.2 (hA.1 2) he he₀ hf

end ContinuousFlexibility.Radial
