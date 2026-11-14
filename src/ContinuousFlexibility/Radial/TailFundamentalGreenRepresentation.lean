module

public import ContinuousFlexibility.Radial.TailResolventEntranceTrace
public import ContinuousFlexibility.Radial.TailFundamentalGreenKernel
public import ContinuousFlexibility.Radial.TailKernelTestExtension
public import ContinuousFlexibility.Analysis.OneSidedSmoothExtension

/-!
# Identifying the actual fundamental Green kernel with the resolvent

The graph solution and the kernel solution have the same source and entrance
trace. Their difference is an actual homogeneous weighted `L²` solution.
Regularity at the entrance is recovered from its first-order equations, so
natural-line uniqueness applies without an extra smoothness assumption on
the graph solution.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

/-- A continuous derivative on the included side of an interval recovers
the one-sided derivative at its entrance. -/
theorem tail_hasDerivWithinAt_Ico_of_continuous {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a < b) (hf : ContinuousOn f (Ico a b)) (hg : ContinuousOn g (Ico a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) :
    ∀ x ∈ Ico a b, HasDerivWithinAt f (g x) (Ico a b) x := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with heq | hlt
  · subst x
    have hgc := hg a ⟨le_rfl, hab⟩
    rw [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsGE hab] at hgc
    have hglim : Tendsto g (𝓝[>] a) (𝓝 (g a)) :=
      hgc.mono_left (nhdsWithin_mono a Ioi_subset_Ici_self)
    have hderlim : Tendsto (deriv f) (𝓝[>] a) (𝓝 (g a)) := by
      apply hglim.congr'
      filter_upwards [Ioo_mem_nhdsGT hab] with y hy
      exact (hd y hy).deriv.symm
    have hright := hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
      ((hf a ⟨le_rfl, hab⟩).mono Ioo_subset_Ico_self) (Ioo_mem_nhdsGT hab) hderlim
    exact hright.mono (fun y hy => hy.1)
  · exact (hd x ⟨hlt, hx.2⟩).hasDerivWithinAt

/-- A homogeneous state continuous up to the entrance satisfies the
one-sided system there as well as throughout the interior. -/
theorem tailFirstOrderSystemWithin_of_continuous_Ico
    {a b Λ : ℝ} {p U Q : ℝ → ℝ} (hab : a < b)
    (hp : ContinuousOn p (Ico a b)) (hp₀ : ∀ x ∈ Ico a b, p x ≠ 0)
    (hU : ContinuousOn U (Ico a b)) (hQ : ContinuousOn Q (Ico a b))
    (h : TailFirstOrderSystem p Λ U Q (Ioo a b)) :
    TailFirstOrderSystemWithin p Λ U Q (Ico a b) := by
  have hDu : ContinuousOn (fun x => Q x / p x) (Ico a b) := hQ.div hp hp₀
  have hDq : ContinuousOn (fun x => -Λ * p x * U x) (Ico a b) :=
    (continuousOn_const.fun_mul hp).fun_mul hU
  have hu := tail_hasDerivWithinAt_Ico_of_continuous hab hU hDu (fun x hx => (h x hx).1)
  have hq := tail_hasDerivWithinAt_Ico_of_continuous hab hQ hDq (fun x hx => (h x hx).2)
  exact fun x hx => ⟨hu x hx, hq x hx⟩

/-- A continuous homogeneous weighted `L²` state has a representative
satisfying the exact frozen natural equation, including genuine smoothness
across the entrance. Its original entrance and all interior values remain
the same. -/
theorem exists_tailNaturalEquation_of_continuous_state {T : DeepTailData}
    (hT : DeepTailHypotheses T) {U Q : ℝ → ℝ}
    (hU : ContinuousOn U (Ico T.entrance T.endpoint))
    (hLp : MemLp U 2 (deepTailMeasure T))
    (h : TailFirstOrderSystem T.p T.Λ U Q (Ioo T.entrance T.endpoint)) :
    ∃ V : ℝ → ℝ, TailNaturalEquation T V ∧ EqOn V U (Ico T.entrance T.endpoint) := by
  rcases hT with ⟨hab, _, _, _, _, _, _, hp, hpos, _, _⟩
  let c : ℝ := (T.entrance + T.endpoint) / 2
  have hac : T.entrance < c := by dsimp only [c]; linarith
  have hcb : c < T.endpoint := by dsimp only [c]; linarith
  have hsub : Icc T.entrance c ⊆ Ico T.entrance T.endpoint :=
    fun x hx => ⟨hx.1, hx.2.trans_lt hcb⟩
  have hRcont : ContinuousOn (fun x => -T.Λ * T.p x * U x)
      (Ico T.entrance T.endpoint) :=
    (continuousOn_const.fun_mul hp.continuousOn).fun_mul hU
  have hRint : IntervalIntegrable (fun x => -T.Λ * T.p x * U x) volume T.entrance c :=
    (hRcont.mono hsub).intervalIntegrable_of_Icc hac.le
  have hQopen : ContinuousOn Q (Ioo T.entrance T.endpoint) :=
    fun x hx => (h x hx).2.continuousAt.continuousWithinAt
  obtain ⟨E, hEQ, hE⟩ := exists_interval_left_continuous_extension hac hcb hQopen
    (fun x hx => (h x hx).2) hRint
  have hUE : TailFirstOrderSystem T.p T.Λ U E (Ioo T.entrance T.endpoint) := by
    intro x hx
    constructor
    · rw [hEQ hx]
      exact (h x hx).1
    · apply (h x hx).2.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hEQ hy
  have hWithin := tailFirstOrderSystemWithin_of_continuous_Ico hab hp.continuousOn
    (fun x hx => (hpos x hx).ne') hU hE hUE
  have hSmooth := tailFirstOrderSystemWithin_contDiffOn
    (uniqueDiffOn_Ico T.entrance T.endpoint) hp (fun x hx => (hpos x hx).ne') hWithin
  obtain ⟨V, hVU, hVa, hVopen⟩ := exists_contDiffAt_extension_of_Ico hab hSmooth.1
  have hpOpen := hp.mono Ioo_subset_Ico_self
  have hposOpen : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x :=
    fun x hx => hpos x (Ioo_subset_Ico_self hx)
  have hUVae : U =ᵐ[deepTailMeasure T] V :=
    (tail_ae_eq_iff_volume hpOpen hposOpen).mpr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hVU (Ioo_subset_Ico_self hx)).symm)
  have hVLp : MemLp V 2 (deepTailMeasure T) := (memLp_congr_ae hUVae).mp hLp
  have hVE : TailFirstOrderSystem T.p T.Λ V E (Ioo T.entrance T.endpoint) := by
    intro x hx
    constructor
    · apply (hUE x hx).1.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hVU (Ioo_subset_Ico_self hy)
    · rw [hVU (Ioo_subset_Ico_self hx)]
      exact (hUE x hx).2
  exact ⟨V, ⟨hVa, hVopen, hVLp,
    tailFirstOrderSystem_equation isOpen_Ioo (fun x hx => (hposOpen x hx).ne') hVE⟩, hVU⟩

/-- Natural-line uniqueness and a nonzero natural entrance value exclude
every homogeneous `L²` state with zero Dirichlet entrance value. -/
theorem tail_state_zero_of_natural_unique {T : DeepTailData}
    (hT : DeepTailHypotheses T) {u U Q : ℝ → ℝ}
    (hu : TailNaturalEquation T u) (hua : u T.entrance ≠ 0)
    (hUnique : ∀ v, TailNaturalEquation T v → ∃ c : ℝ,
      ∀ x ∈ Ioo T.entrance T.endpoint, v x = c * u x)
    (hU : ContinuousOn U (Ico T.entrance T.endpoint))
    (hLp : MemLp U 2 (deepTailMeasure T))
    (h : TailFirstOrderSystem T.p T.Λ U Q (Ioo T.entrance T.endpoint))
    (hUa : U T.entrance = 0) : ∀ x ∈ Ioo T.entrance T.endpoint, U x = 0 := by
  obtain ⟨V, hV, hVU⟩ := exists_tailNaturalEquation_of_continuous_state hT hU hLp h
  obtain ⟨c, hc⟩ := hUnique V hV
  have hVlim : Tendsto V (𝓝[>] T.entrance) (𝓝 (V T.entrance)) :=
    hV.1.continuousAt.mono_left nhdsWithin_le_nhds
  have hulim : Tendsto (fun x => c * u x) (𝓝[>] T.entrance) (𝓝 (c * u T.entrance)) :=
    (hu.1.continuousAt.mono_left nhdsWithin_le_nhds).const_mul c
  have heq : (fun x => c * u x) =ᶠ[𝓝[>] T.entrance] V := by
    filter_upwards [Ioo_mem_nhdsGT hT.1] with x hx
    exact (hc x hx).symm
  have hVa : V T.entrance = 0 := (hVU ⟨le_rfl, hT.1⟩).trans hUa
  have hca : 0 = c * u T.entrance := hVa.symm.trans
    (tendsto_nhds_unique hVlim (hulim.congr' heq))
  have hc0 : c = 0 := (mul_eq_zero.mp hca.symm).resolve_right hua
  intro x hx
  calc
    U x = V x := (hVU (Ioo_subset_Ico_self hx)).symm
    _ = c * u x := hc x hx
    _ = 0 := by rw [hc0, zero_mul]

private theorem tail_natural_continuous_Ico {T : DeepTailData} {u : ℝ → ℝ}
    (hu : TailNaturalEquation T u) : ContinuousOn u (Ico T.entrance T.endpoint) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with heq | hlt
  · subst x
    exact hu.1.continuousAt.continuousWithinAt
  · exact (hu.2.1.contDiffAt (isOpen_Ioo.mem_nhds ⟨hlt, hx.2⟩)).continuousAt.continuousWithinAt

/-- The graph solution is the actual fundamental-kernel solution for every
compact-interior source. The comparison uses the frozen natural uniqueness
statement only after recovering all of its regularity assumptions. -/
theorem tailFundamentalGreen_compact_representation {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hI : TailFormIdentification T T.endpoint)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T)
    (hG : ∀ f, TailFriedrichsGraph T T.endpoint (G f) (f + T.Λ • G f))
    {u q w z : ℝ → ℝ}
    (hu : TailNaturalEquation T u) (hua : u T.entrance ≠ 0)
    (hUnique : ∀ v, TailNaturalEquation T v → ∃ c : ℝ,
      ∀ x ∈ Ioo T.entrance T.endpoint, v x = c * u x)
    (hwc : ContinuousOn w (Ico T.entrance T.endpoint))
    (hus : TailFirstOrderSystem T.p T.Λ u q (Ico T.entrance T.endpoint))
    (hws : TailFirstOrderSystem T.p T.Λ w z (Ico T.entrance T.endpoint))
    (hwa : w T.entrance = 0)
    (hW : ∀ x ∈ Ico T.entrance T.endpoint, z x * u x - w x * q x = 1) :
    ∀ f : DeepTailL2 T, ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo T.entrance T.endpoint →
      (f : ℝ → ℝ) =ᵐ[deepTailMeasure T] ψ →
      (G f : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun x => ∫ y,
        tailFundamentalGreenKernel T.entrance T.endpoint w u 1 x y * ψ y
          ∂deepTailMeasure T := by
  intro f ψ hψ hc hs hf
  obtain ⟨d, U, Q, hud, hUc, hQc, hUa, hUae, hQae, hUd, hQd⟩ :=
    exists_tailResolvent_classical_rep_with_entrance hT hI hψ.continuous.continuousOn hf (hG f)
  have hTcopy := hT
  rcases hTcopy with ⟨hab, _, _, _, _, _, _, hp, hpos, _, _⟩
  obtain ⟨V, R, hVeq, hVLp, hVc, hVa, hVR⟩ :=
    exists_tailFundamentalGreen_compact_solution (W := 1) hab hp hpos hwc
      (tail_natural_continuous_Ico hu) (hws.mono Ioo_subset_Ico_self)
      (hus.mono Ioo_subset_Ico_self) hwa one_ne_zero
      (fun x hx => hW x (Ioo_subset_Ico_self hx)) hu.2.2.1 hψ.continuous hc hs
  have hULp : MemLp U 2 (deepTailMeasure T) := (memLp_congr_ae hUae).mp (Lp.memLp (G f))
  let D : ℝ → ℝ := fun x => U x - V x
  let S : ℝ → ℝ := fun x => Q x - R x
  have hDc : ContinuousOn D (Ico T.entrance T.endpoint) := hUc.fun_sub hVc
  have hDLp : MemLp D 2 (deepTailMeasure T) := hULp.sub hVLp
  have hDa : D T.entrance = 0 := by simp only [D, hUa, hVa, sub_self]
  have hDS : TailFirstOrderSystem T.p T.Λ D S (Ioo T.entrance T.endpoint) := by
    intro x hx
    constructor
    · change HasDerivAt (fun y => U y - V y) ((Q x - R x) / T.p x) x
      exact ((hUd x hx).fun_sub (hVR x hx).1).congr_deriv (by ring)
    · change HasDerivAt (fun y => Q y - R y) (-T.Λ * T.p x * (U x - V x)) x
      exact ((hQd x hx).fun_sub (hVR x hx).2).congr_deriv (by ring)
  have hDzero := tail_state_zero_of_natural_unique hT hu hua hUnique hDc hDLp hDS hDa
  apply hUae.trans
  apply (tail_ae_eq_iff_volume (hp.mono Ioo_subset_Ico_self)
    (fun x hx => hpos x (Ioo_subset_Ico_self hx))).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have heq : U x = V x := sub_eq_zero.mp (hDzero x hx)
  exact heq.trans (hVeq hx)

/-- The same kernel represents the resolvent for the frozen ordinary
support test class. The cutoff extension keeps the kernel unchanged. -/
theorem tailFundamentalGreen_representation {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hI : TailFormIdentification T T.endpoint)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T)
    (hG : ∀ f, TailFriedrichsGraph T T.endpoint (G f) (f + T.Λ • G f))
    {u q w z : ℝ → ℝ}
    (hu : TailNaturalEquation T u) (hua : u T.entrance ≠ 0)
    (hUnique : ∀ v, TailNaturalEquation T v → ∃ c : ℝ,
      ∀ x ∈ Ioo T.entrance T.endpoint, v x = c * u x)
    (huInt : Integrable u (deepTailMeasure T))
    (hwc : ContinuousOn w (Ico T.entrance T.endpoint))
    (hus : TailFirstOrderSystem T.p T.Λ u q (Ico T.entrance T.endpoint))
    (hws : TailFirstOrderSystem T.p T.Λ w z (Ico T.entrance T.endpoint))
    (hwa : w T.entrance = 0)
    (hW : ∀ x ∈ Ico T.entrance T.endpoint, z x * u x - w x * q x = 1) :
    ∀ f : DeepTailL2 T, ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Function.support ψ ⊆ Ioo T.entrance T.endpoint →
      (f : ℝ → ℝ) =ᵐ[deepTailMeasure T] ψ →
      (G f : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun x => ∫ y,
        tailFundamentalGreenKernel T.entrance T.endpoint w u 1 x y * ψ y
          ∂deepTailMeasure T := by
  apply tailKernel_representation_of_interior G
    (tailFundamentalGreenKernel T.entrance T.endpoint w u 1)
    (tailFundamentalGreen_compact_representation hT hI G hG hu hua hUnique hwc hus hws hwa hW)
  intro ψ hψ hc hs
  have hTcopy := hT
  rcases hTcopy with ⟨_, _, _, _, _, _, _, hp, hpos, _, _⟩
  exact Eventually.of_forall fun x => tailFundamentalGreenKernel_mul_integrable_test
    hp.continuousOn (fun y hy => (hpos y hy).le) hwc huInt hψ.continuous hc x

end ContinuousFlexibility.Radial
