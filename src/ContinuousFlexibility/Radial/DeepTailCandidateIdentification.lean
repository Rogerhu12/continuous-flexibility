import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Radial.DeepTailShift
import ContinuousFlexibility.Radial.DeepTailEdgeUniqueness
import ContinuousFlexibility.Radial.DeepTailParameterContinuity

/-!
# Identifying a candidate from a positively shifted tail

A candidate need only be `C¹` at the original entrance.  On a positive
shift it is a genuine smooth natural solution, and the natural-line theorem
identifies it there.  Initial-value uniqueness transports that proportionality
back through the finite entrance segment.  The final representative is the
original smooth natural solution, normalized at its nonzero entrance value.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

private theorem candidate_contDiffAt_one {T : DeepTailData} {v : ℝ → ℝ}
    (ha : ContDiffAt ℝ 1 v T.entrance)
    (hs : ContDiffOn ℝ ∞ v (Ioo T.entrance T.endpoint))
    {x : ℝ} (hx : x ∈ Ico T.entrance T.endpoint) : ContDiffAt ℝ 1 v x := by
  rcases eq_or_lt_of_le hx.1 with heq | hlt
  · simpa only [← heq] using ha
  · exact (hs.contDiffAt (Ioo_mem_nhds hlt hx.2)).of_le (by simp)

private theorem candidate_hasFluxDerivAt {T : DeepTailData} {v : ℝ → ℝ}
    (hT : DeepTailHypotheses T)
    (hs : ContDiffOn ℝ ∞ v (Ioo T.entrance T.endpoint))
    (heq : ∀ x ∈ Ioo T.entrance T.endpoint,
      deriv (fun y => T.p y * deriv v y) x + T.Λ * T.p x * v x = 0)
    {x : ℝ} (hx : x ∈ Ioo T.entrance T.endpoint) :
    HasDerivAt (fun y => T.p y * deriv v y) (-(T.Λ * T.p x * v x)) x := by
  have hp := ((deepTail_contDiffOn hT).mono Ioo_subset_Ico_self).contDiffAt
    (isOpen_Ioo.mem_nhds hx)
  have hv := hs.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fun y => T.p y * deriv v y) x :=
    (hp.differentiableAt (by simp)).mul
      ((hv.derivWithin (m := 1) (by simp)).differentiableAt (by norm_num))
  apply hd.hasDerivAt.congr_deriv
  linarith only [heq x hx]

/-- Equality on a terminal open interval determines the solution all the
way back to the original entrance.  Both solutions only need `C¹` there. -/
theorem tailSolution_eqOn_of_terminal_eqOn {T : DeepTailData} {u v : ℝ → ℝ} {cut : ℝ}
    (hT : DeepTailHypotheses T)
    (hua : ContDiffAt ℝ 1 u T.entrance) (hva : ContDiffAt ℝ 1 v T.entrance)
    (hus : ContDiffOn ℝ ∞ u (Ioo T.entrance T.endpoint))
    (hvs : ContDiffOn ℝ ∞ v (Ioo T.entrance T.endpoint))
    (huode : ∀ x ∈ Ioo T.entrance T.endpoint,
      deriv (fun y => T.p y * deriv u y) x + T.Λ * T.p x * u x = 0)
    (hvode : ∀ x ∈ Ioo T.entrance T.endpoint,
      deriv (fun y => T.p y * deriv v y) x + T.Λ * T.p x * v x = 0)
    (hcut : T.entrance ≤ cut) (hcutend : cut < T.endpoint)
    (heq : EqOn u v (Ioo cut T.endpoint)) : EqOn u v (Ico T.entrance T.endpoint) := by
  obtain ⟨t, hct, hte⟩ := exists_between hcutend
  obtain ⟨b, htb, hbe⟩ := exists_between hte
  have hsub : Icc T.entrance b ⊆ Ico T.entrance T.endpoint :=
    fun x hx => ⟨hx.1, hx.2.trans_lt hbe⟩
  have hsubo : Ioo T.entrance b ⊆ Ioo T.entrance T.endpoint :=
    fun x hx => ⟨hx.1, hx.2.trans hbe⟩
  have huC : ContinuousOn u (Icc T.entrance b) :=
    fun x hx => (candidate_contDiffAt_one hua hus (hsub hx)).continuousAt.continuousWithinAt
  have hvC : ContinuousOn v (Icc T.entrance b) :=
    fun x hx => (candidate_contDiffAt_one hva hvs (hsub hx)).continuousAt.continuousWithinAt
  have hduC : ContinuousOn (deriv u) (Icc T.entrance b) :=
    fun x hx => ((candidate_contDiffAt_one hua hus (hsub hx)).derivWithin
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hdvC : ContinuousOn (deriv v) (Icc T.entrance b) :=
    fun x hx => ((candidate_contDiffAt_one hva hvs (hsub hx)).derivWithin
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hgerm : u =ᶠ[𝓝 t] v :=
    Filter.mem_of_superset (Ioo_mem_nhds hct hte) (fun _ hx => heq hx)
  have hfinite := tailEdge_solutions_eq_of_state_eq
    (show t ∈ Ioo T.entrance b from ⟨hcut.trans_lt hct, htb⟩)
    ((deepTail_contDiffOn hT).continuousOn.mono hsub)
    (fun x hx => deepTail_pos hT x (hsub hx)) huC hduC hvC hdvC
    (fun x hx => ((hus.contDiffAt (isOpen_Ioo.mem_nhds (hsubo hx))).differentiableAt
      (by simp)).hasDerivAt)
    (fun x hx => ((hvs.contDiffAt (isOpen_Ioo.mem_nhds (hsubo hx))).differentiableAt
      (by simp)).hasDerivAt)
    (fun _ hx => candidate_hasFluxDerivAt hT hus huode (hsubo hx))
    (fun _ hx => candidate_hasFluxDerivAt hT hvs hvode (hsubo hx))
    (heq ⟨hct, hte⟩) (congrArg (fun z => T.p t * z) hgerm.deriv_eq)
  intro x hx
  by_cases hxb : x ≤ b
  · exact hfinite ⟨hx.1, hxb⟩
  · exact heq ⟨hct.trans (htb.trans (lt_of_not_ge hxb)), hx.2⟩

/-- The candidate becomes a genuine natural solution after a positive
shift, using only the specified shifted square-integrability. -/
theorem tailCandidate_natural_shift {T : DeepTailData} {v : ℝ → ℝ} {k : ℕ}
    (hT : DeepTailHypotheses T) (hk : 0 < k)
    (hs : ContDiffOn ℝ ∞ v (Ioo T.entrance T.endpoint))
    (hm : MemLp v 2 (deepTailMeasure (deepTailShift T k)))
    (heq : ∀ x ∈ Ioo T.entrance T.endpoint,
      deriv (fun y => T.p y * deriv v y) x + T.Λ * T.p x * v x = 0) :
    TailNaturalEquation (deepTailShift T k) v := by
  have hkin : T.node k ∈ Ioo T.entrance T.endpoint :=
    ⟨hT.2.1.trans_lt (deepTail_node_strictMono hT hk), deepTail_node_lt_endpoint hT k⟩
  refine ⟨hs.contDiffAt (isOpen_Ioo.mem_nhds hkin),
    hs.mono (deepTailShift_interval_subset hT k), hm, ?_⟩
  intro x hx
  exact heq x (deepTailShift_interval_subset hT k hx)

/-- Every nonzero original natural solution is proportional to a shifted
candidate on the whole tail, including its entrance derivative. -/
theorem tailNatural_proportional_to_shift_candidate
    {T : DeepTailData} {u v : ℝ → ℝ} {k : ℕ}
    (hT : DeepTailHypotheses T) (hk : 0 < k)
    (hline : TailNaturalLineAndKernel (deepTailShift T k))
    (hu : TailNaturalEquation T u)
    (hune : ∃ x ∈ Ioo T.entrance T.endpoint, u x ≠ 0)
    (hva : ContDiffAt ℝ 1 v T.entrance)
    (hvs : ContDiffOn ℝ ∞ v (Ioo T.entrance T.endpoint))
    (hvm : MemLp v 2 (deepTailMeasure (deepTailShift T k)))
    (hvode : ∀ x ∈ Ioo T.entrance T.endpoint,
      deriv (fun y => T.p y * deriv v y) x + T.Λ * T.p x * v x = 0)
    (hvne : ∃ x ∈ Ioo (T.node k) T.endpoint, v x ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧ EqOn u (fun x => c * v x) (Ico T.entrance T.endpoint) ∧
      deriv u T.entrance = c * deriv v T.entrance := by
  have hvshift := tailCandidate_natural_shift hT hk hvs hvm hvode
  have hushift := tailNaturalEquation_shift hT hu hk
  obtain ⟨c, hc⟩ := tailNaturalLine_span_of_nonzero hline hvshift hushift hvne
  have hcEq : ∀ x ∈ Ioo T.entrance T.endpoint,
      deriv (fun y => T.p y * deriv (fun z => c * v z) y) x +
        T.Λ * T.p x * (c * v x) = 0 := by
    have hf : (fun y => T.p y * deriv (fun z => c * v z) y) =
        fun y => c * (T.p y * deriv v y) := by
      funext y
      rw [deriv_const_mul_field]
      ring
    intro x hx
    rw [hf, deriv_const_mul_field]
    calc
      c * deriv (fun y => T.p y * deriv v y) x + T.Λ * T.p x * (c * v x) =
          c * (deriv (fun y => T.p y * deriv v y) x + T.Λ * T.p x * v x) := by ring
      _ = 0 := by rw [hvode x hx, mul_zero]
  have hglobal := tailSolution_eqOn_of_terminal_eqOn hT
    (hu.1.of_le (by simp)) (contDiffAt_const.mul hva) hu.2.1
    (contDiffOn_const.mul hvs) hu.2.2.2 hcEq
    (deepTail_entrance_le_node hT k) (deepTail_node_lt_endpoint hT k) hc
  have hc₀ : c ≠ 0 := by
    intro hc₀
    obtain ⟨x, hx, hux⟩ := hune
    apply hux
    simpa only [hc₀, zero_mul] using hglobal (Ioo_subset_Ico_self hx)
  have hder := tailEntrance_deriv_eq_of_eqOn hT.1
    (hu.1.differentiableAt (by simp)) ((hva.differentiableAt (by norm_num)).const_mul c)
    (hglobal.mono Ioo_subset_Ico_self)
  rw [deriv_const_mul_field] at hder
  exact ⟨c, hc₀, hglobal, hder⟩

/-- A nonzero candidate entrance value forces the actual natural entrance
value to be nonzero and determines the normalized slope there. -/
theorem tailNatural_entrance_of_shift_candidate
    {T : DeepTailData} {u v : ℝ → ℝ} {k : ℕ}
    (hT : DeepTailHypotheses T) (hk : 0 < k)
    (hline : TailNaturalLineAndKernel (deepTailShift T k))
    (hu : TailNaturalEquation T u)
    (hune : ∃ x ∈ Ioo T.entrance T.endpoint, u x ≠ 0)
    (hva : ContDiffAt ℝ 1 v T.entrance)
    (hvs : ContDiffOn ℝ ∞ v (Ioo T.entrance T.endpoint))
    (hvm : MemLp v 2 (deepTailMeasure (deepTailShift T k)))
    (hvode : ∀ x ∈ Ioo T.entrance T.endpoint,
      deriv (fun y => T.p y * deriv v y) x + T.Λ * T.p x * v x = 0)
    (hvne : ∃ x ∈ Ioo (T.node k) T.endpoint, v x ≠ 0)
    (hv₀ : v T.entrance ≠ 0) :
    u T.entrance ≠ 0 ∧ deriv u T.entrance / u T.entrance =
      deriv v T.entrance / v T.entrance := by
  obtain ⟨c, hc, heq, hder⟩ := tailNatural_proportional_to_shift_candidate
    hT hk hline hu hune hva hvs hvm hvode hvne
  have ha : u T.entrance = c * v T.entrance := heq ⟨le_rfl, hT.1⟩
  refine ⟨by rw [ha]; exact mul_ne_zero hc hv₀, ?_⟩
  rw [hder, ha]
  field_simp [hc, hv₀] <;> ring

/-- Normalize the original smooth natural representative; the candidate
itself need not have an all-order smooth extension at the old entrance. -/
theorem exists_tailNatural_normalized_of_shift_candidate
    {T : DeepTailData} {v : ℝ → ℝ} {k : ℕ}
    (hT : DeepTailHypotheses T) (hk : 0 < k)
    (hline : TailNaturalLineAndKernel T)
    (hshiftline : TailNaturalLineAndKernel (deepTailShift T k))
    (hva : ContDiffAt ℝ 1 v T.entrance)
    (hvs : ContDiffOn ℝ ∞ v (Ioo T.entrance T.endpoint))
    (hvm : MemLp v 2 (deepTailMeasure (deepTailShift T k)))
    (hvode : ∀ x ∈ Ioo T.entrance T.endpoint,
      deriv (fun y => T.p y * deriv v y) x + T.Λ * T.p x * v x = 0)
    (hvne : ∃ x ∈ Ioo (T.node k) T.endpoint, v x ≠ 0)
    (hv₀ : v T.entrance ≠ 0) :
    ∃ u : ℝ → ℝ, TailNaturalEquation T u ∧ u T.entrance = 1 ∧
      deriv u T.entrance = deriv v T.entrance / v T.entrance := by
  obtain ⟨u, hu, hune, _, _⟩ := hline
  obtain ⟨h₀, hslope⟩ := tailNatural_entrance_of_shift_candidate
    hT hk hshiftline hu hune hva hvs hvm hvode hvne hv₀
  refine ⟨tailEntranceNormalize T u, tailNaturalEquation_normalize hu,
    tailEntranceNormalize_entrance h₀, ?_⟩
  rw [deriv_tailEntranceNormalize, mul_comm, ← div_eq_mul_inv]
  exact hslope

theorem r06Full_tailNaturalLine {C η₀ K₀ : ℝ}
    (hfull : ContinuousFlexibility.Blueprint.R06Full C η₀ K₀)
    {T : DeepTailData} (hT : DeepTailHypotheses T) (hη : T.η ≤ η₀) (hK : K₀ ≤ T.K) :
    TailNaturalLineAndKernel T := by
  obtain ⟨G, _, _, _, _, hline, _⟩ := (hfull T hT hη hK).2.2
  exact hline

/-- The full deep-tail theorem supplies both natural lines needed by the
candidate identification, with unchanged deep-tail constants. -/
theorem exists_tailNatural_normalized_of_r06Full_candidate
    {C η₀ K₀ : ℝ} (hfull : ContinuousFlexibility.Blueprint.R06Full C η₀ K₀)
    {T : DeepTailData} {v : ℝ → ℝ} {k : ℕ}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ η₀) (hK : K₀ ≤ T.K) (hk : 0 < k)
    (hva : ContDiffAt ℝ 1 v T.entrance)
    (hvs : ContDiffOn ℝ ∞ v (Ioo T.entrance T.endpoint))
    (hvm : MemLp v 2 (deepTailMeasure (deepTailShift T k)))
    (hvode : ∀ x ∈ Ioo T.entrance T.endpoint,
      deriv (fun y => T.p y * deriv v y) x + T.Λ * T.p x * v x = 0)
    (hvne : ∃ x ∈ Ioo (T.node k) T.endpoint, v x ≠ 0)
    (hv₀ : v T.entrance ≠ 0) :
    ∃ u : ℝ → ℝ, TailNaturalEquation T u ∧ u T.entrance = 1 ∧
      deriv u T.entrance = deriv v T.entrance / v T.entrance :=
  exists_tailNatural_normalized_of_shift_candidate hT hk
    (r06Full_tailNaturalLine hfull hT hη hK)
    (r06Full_tailNaturalLine hfull (deepTailHypotheses_shift hT k) hη hK)
    hva hvs hvm hvode hvne hv₀

end ContinuousFlexibility.Radial
