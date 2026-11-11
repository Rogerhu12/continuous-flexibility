import ContinuousFlexibility.Analysis.ScalarInverseJetBounds
import ContinuousFlexibility.Analysis.N01FlowSmallness
import ContinuousFlexibility.Analysis.ReturnCorrectionResidualPeriodicity

/-!
# Uniform angular jets of the actual N01 flow and its inverse

The zeroth parameter tower bounds every pure angular derivative of the
flow difference on the full closed component. Material absorption removes
its sample weights. A single smaller neighborhood bounds the first
angular derivative below by one half. The actual fiberwise inverse and
the specified endpoint inverse then have uniformly bounded positive-order
angular jets.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01FlowInverseJetBoundsStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem N01Properties.minusFlow_reference_angular_iteratedDeriv_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) :
    |iteratedDeriv n (C.minusFlow (C.referenceState, 0) m r) θ| ≤ 1 := by
  have heq : C.minusFlow (C.referenceState, 0) m r =
      fun t => t - opticalTravel D.w (C.left m) r :=
    funext (hN.minusFlow_reference_eq hS hT m hr)
  rw [heq]
  have hsub := iteratedDeriv_fun_sub
    (contDiffAt_id : ContDiffAt ℝ (n : ℕ∞ω) (fun t : ℝ => t) θ)
    (contDiffAt_const : ContDiffAt ℝ (n : ℕ∞ω)
      (fun _ : ℝ => opticalTravel D.w (C.left m) r) θ)
  simp only [id_eq] at hsub
  rw [hsub]
  simp only [iteratedDeriv_id, iteratedDeriv_const, if_neg (by omega : n ≠ 0),
    sub_zero]
  split <;> norm_num

theorem N01Properties.ordinaryFlowFamily_angular_uniform_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m r, r ∈ Ioo (C.left m) (C.right m) → ∀ θ,
      |ordinaryFlowFamily S C m 0 n (r, θ) z| ≤ K := by
  let hdata := hN.2.2.2.2.2.2.2.2.2.2.2.2 0 n
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  obtain ⟨A, hA, hweight⟩ :=
    materialSample_H_E0_envelope hT hN.1.1 (γ := (3 / 4 : ℝ)) (by norm_num) B
  let Q := 1 + pairGrading (stateGrading S) realGrading (n + loss)
    (z - (C.referenceState, 0))
  have hQ : 0 ≤ Q := add_nonneg zero_le_one (apply_nonneg _ _)
  have hpoint : ∀ m r, r ∈ Ioo (C.left m) (C.right m) → ∀ θ,
      |ordinaryFlowFamily S C m 0 n (r, θ) z| ≤ B * A * Q := by
    intro m r hr θ
    obtain ⟨J, hJ⟩ := hdata.choose_spec.2 m 0 n (r, θ) (by simp) hr
    have hraw : |J.D 0 z Fin.elim0| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B * Q := by
      simpa only [pow_zero, one_mul, oneHighVariationWeight, Fin.prod_univ_zero,
        Fin.sum_univ_zero, mul_one, add_zero, Q] using hJ z hz Fin.elim0
    have hzero : J.D 0 z Fin.elim0 = ordinaryFlowFamily S C m 0 n (r, θ) z :=
      J.zero z hz
    have hM : B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B * Q ≤ B * A * Q := by
      have h := mul_le_mul_of_nonneg_left (hweight (C.cell m)) (mul_nonneg hB.le hQ)
      convert h using 1 <;> ring
    exact (congrArg abs hzero).symm.le.trans (hraw.trans hM)
  exact ⟨B * A * Q, mul_nonneg (mul_nonneg hB.le hA.le) hQ, hpoint⟩

theorem N01Properties.minusFlow_angular_iteratedDeriv_uniform_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      |iteratedDeriv n (C.minusFlow z m r) θ| ≤ K := by
  obtain ⟨M, hM, hbound⟩ := hN.ordinaryFlowFamily_angular_uniform_bound hT hz n
  have hpoint : ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      |iteratedDeriv n (C.minusFlow z m r) θ| ≤ M + 1 := by
    intro m r hr θ
    have hC : controlGeometryConditions D S C := hN.2.2.2.1
    have hi (s : ℝ) (hs : s ∈ Ioo (C.left m) (C.right m)) :
        |iteratedDeriv n (C.minusFlow z m s) θ| ≤ M + 1 := by
      have hraw := hbound m s hs θ
      have hclosed : s ∈ Icc (C.left m) (C.right m) := ⟨hs.1.le, hs.2.le⟩
      have hf := (hN.minusFlow_angular_contDiff hS hT hz hsector m hclosed).of_le
        (show (n : ℕ∞ω) ≤ ∞ by simp)
      have hrefeq : C.minusFlow (C.referenceState, 0) m s =
          fun t => t - opticalTravel D.w (C.left m) s :=
        funext (hN.minusFlow_reference_eq hS hT m hclosed)
      have href : ContDiff ℝ (n : ℕ∞ω) (C.minusFlow (C.referenceState, 0) m s) := by
        rw [hrefeq]
        exact contDiff_id.sub contDiff_const
      simp only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero] at hraw
      rw [iteratedDeriv_fun_sub hf.contDiffAt href.contDiffAt] at hraw
      calc
        |iteratedDeriv n (C.minusFlow z m s) θ| =
            |(iteratedDeriv n (C.minusFlow z m s) θ -
                iteratedDeriv n (C.minusFlow (C.referenceState, 0) m s) θ) +
              iteratedDeriv n (C.minusFlow (C.referenceState, 0) m s) θ| := by
                rw [sub_add_cancel]
        _ ≤ |iteratedDeriv n (C.minusFlow z m s) θ -
                iteratedDeriv n (C.minusFlow (C.referenceState, 0) m s) θ| +
              |iteratedDeriv n (C.minusFlow (C.referenceState, 0) m s) θ| := abs_add_le _ _
        _ ≤ M + 1 := add_le_add hraw
          (hN.minusFlow_reference_angular_iteratedDeriv_bound hS hT m hclosed n hn θ)
    have hc : ContinuousOn (fun s => |iteratedDeriv n (C.minusFlow z m s) θ|)
        (Icc (C.left m) (C.right m)) :=
      ((hN.minusFlow_angular_iteratedDeriv_continuousOn hS hT hz hsector m n).comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs, mem_univ θ⟩)).abs
    have hclosure : closure (Ioo (C.left m) (C.right m)) = Icc (C.left m) (C.right m) :=
      closure_Ioo (hC.1 m).2.1.ne
    exact le_on_closure hi (by simpa only [hclosure] using hc) continuousOn_const
      (by simpa only [hclosure] using hr)
  exact ⟨M + 1, add_nonneg hM zero_le_one, hpoint⟩

/-- A common neighborhood controls every actual fiberwise inverse.
The bound at derivative order `n` may depend on the fixed state and
`n`, while the neighborhood and positive first-derivative lower bound
are independent of them. -/
theorem N01Properties.exists_uniform_inverse_angular_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ N01Properties D T S C base' loss ε' ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
      (∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        1 / 2 ≤ deriv (C.minusFlow z m r) θ ∧ deriv (C.minusFlow z m r) θ ≤ 3 / 2) ∧
      (∀ n : ℕ, 1 ≤ n → ∃ K : ℝ, 0 ≤ K ∧
        (∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
          |iteratedDeriv n (Function.invFun (C.minusFlow z m r)) θ| ≤ K) ∧
        (∀ m θ, |iteratedDeriv n (C.minusReturnInverse z m) θ| ≤ K)) := by
  obtain ⟨K, hK, hsmall⟩ := hN.minusFlow_near_reference_uniform hS hT
  let base' := max base (1 + loss)
  let ε' := min ε (min (1 / 2) (1 / (2 * K)))
  have hb : base ≤ base' := le_max_left _ _
  have hh : 1 + loss ≤ base' := le_max_right _ _
  have hε' : 0 < ε' := lt_min hN.2.1
    (lt_min (by norm_num) (div_pos zero_lt_one (mul_pos (by norm_num) hK)))
  have hεε : ε' ≤ ε := min_le_left _ _
  have hεhalf : ε' ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hKε : K * ε' ≤ 1 / 2 := by
    have h := (min_le_right ε (min (1 / 2) (1 / (2 * K)))).trans
      (min_le_right (1 / 2) (1 / (2 * K)))
    have hmul := mul_le_mul_of_nonneg_left h hK.le
    exact hmul.trans_eq (by field_simp [hK.ne'] <;> ring)
  refine ⟨base', ε', hb, hε', hεε,
    hN.restrict_neighborhood hT hb hε' hεε, fun z hz hsector => ?_⟩
  have hzold := stateNeighborhood_mono S C hb hεε hz
  have hbounds (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
      1 / 2 ≤ deriv (C.minusFlow z m r) θ ∧ deriv (C.minusFlow z m r) θ ≤ 3 / 2 := by
    have h := (hsmall base' hb hh ε' hε'.le hεε hεhalf z hz hsector m r hr θ).2
    have hh' := abs_le.mp (h.trans hKε)
    constructor <;> linarith only [hh'.1, hh'.2]
  refine ⟨hbounds, fun n hn => ?_⟩
  let I := Σ m : ℕ, {r : ℝ // r ∈ Icc (C.left m) (C.right m)}
  let f (i : I) : ℝ → ℝ := C.minusFlow z i.1 i.2.val
  let g (i : I) : ℝ → ℝ := Function.invFun (f i)
  have hf (i : I) : ContDiff ℝ ∞ (f i) :=
    hN.minusFlow_angular_contDiff hS hT hzold hsector i.1 i.2.property
  have hpos (i : I) (θ : ℝ) : 0 < deriv (f i) θ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le (hbounds i.1 i.2.val i.2.property θ).1
  have hinj (i : I) : Function.Injective (f i) :=
    (strictMono_of_deriv_pos (hpos i)).injective
  have hsurj (i : I) : Function.Surjective (f i) :=
    returnLift_surjective Real.pi_pos (hf i).continuous
      (hN.minusFlow_add_period hzold i.1 i.2.property)
  have hforward (k : ℕ) (hk : 1 ≤ k) :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ i θ, |iteratedDeriv k (f i) θ| ≤ A := by
    obtain ⟨A, hA, hbA⟩ :=
      hN.minusFlow_angular_iteratedDeriv_uniform_bound hS hT hzold hsector k hk
    exact ⟨A, hA, fun i θ => hbA i.1 i.2.val i.2.property θ⟩
  obtain ⟨A, hA, hbound⟩ := inverse_iteratedDeriv_uniform_bound f g hf
    (by norm_num : (0 : ℝ) < 1 / 2)
    (fun i θ => (hbounds i.1 i.2.val i.2.property θ).1)
    (fun i θ => Function.leftInverse_invFun (hinj i) θ)
    (fun i θ => Function.rightInverse_invFun (hsurj i) θ) hforward n hn
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  refine ⟨A, hA, ?_, ?_⟩
  · intro m r hr θ
    exact hbound ⟨m, ⟨r, hr⟩⟩ θ
  · intro m θ
    let i : I := ⟨m, ⟨C.right m, ⟨(hcontrol.1 m).2.1.le, le_rfl⟩⟩⟩
    have heq : C.minusReturnInverse z m = g i := by
      funext t
      have h := Function.leftInverse_invFun (hinj i) (C.minusReturnInverse z m t)
      change Function.invFun (C.minusFlow z m (C.right m))
        (C.minusFlow z m (C.right m) (C.minusReturnInverse z m t)) =
          C.minusReturnInverse z m t at h
      rw [(N01Properties.return_inverse_and_positive S C z m hN hzold hsector t).1] at h
      exact h.symm
    rw [heq]
    exact hbound i θ

end ContinuousFlexibility.Statements

