import ContinuousFlexibility.Radial.MorseWeylExclusion

/-!
# Inverting the actual Morse graph below the Weyl threshold

At a subthreshold energy with trivial kernel, the shifted graph has dense
range by graph adjointness. A normalized residual sequence is then weakly
null and would contradict Weyl exclusion. The resulting lower bound and
graph closedness give surjectivity and a continuous linear inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

private def morseGraphShift (E : ℝ) : (MorseL2 × MorseL2) →L[ℝ] (MorseL2 × MorseL2) :=
  (ContinuousLinearMap.fst ℝ MorseL2 MorseL2).prod
    (ContinuousLinearMap.snd ℝ MorseL2 MorseL2 + E • ContinuousLinearMap.fst ℝ MorseL2 MorseL2)

private def morseGraphAtEnergy (α w b E : ℝ) : Submodule ℝ (MorseL2 × MorseL2) :=
  (morseAssociatedGraph α w b).comap (morseGraphShift E).toLinearMap

private theorem morseGraphAtEnergy_mem {α w b E : ℝ} {u f : MorseL2} :
    (u, f) ∈ morseGraphAtEnergy α w b E ↔ (u, f + E • u) ∈ morseAssociatedGraph α w b := Iff.rfl

private theorem morseGraphAtEnergy_isClosed (α b E : ℝ) {w : ℝ} (hw : 0 < w) :
    IsClosed (morseGraphAtEnergy α w b E : Set (MorseL2 × MorseL2)) :=
  (morseAssociatedGraph_isClosed α b hw).preimage (morseGraphShift E).continuous

private theorem morseGraphAtEnergy_symmetric {α w b E : ℝ} {u f v g : MorseL2}
    (hu : (u, f) ∈ morseGraphAtEnergy α w b E) (hv : (v, g) ∈ morseGraphAtEnergy α w b E) :
    ⟪f, v⟫_ℝ = ⟪u, g⟫_ℝ := by
  have h := morseAssociatedGraph_symmetric α w b _ _
    (morseGraphAtEnergy_mem.mp hu) (morseGraphAtEnergy_mem.mp hv)
  change ⟪f + E • u, v⟫_ℝ = ⟪u, g + E • v⟫_ℝ at h
  rw [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right] at h
  linarith only [h]

private def morseGraphRange (α w b E : ℝ) : Submodule ℝ MorseL2 :=
  (morseGraphAtEnergy α w b E).map (LinearMap.snd ℝ MorseL2 MorseL2)

private theorem mem_morseGraphRange {α w b E : ℝ} {f : MorseL2} :
    f ∈ morseGraphRange α w b E ↔ ∃ u : MorseL2, (u, f) ∈ morseGraphAtEnergy α w b E := by
  constructor
  · rintro ⟨p, hp, hpf⟩
    change p.2 = f at hpf
    refine ⟨p.1, ?_⟩
    rw [← hpf]
    exact hp
  · rintro ⟨u, hu⟩
    exact ⟨(u, f), hu, rfl⟩

private theorem morseGraphRange_dense (α b E : ℝ) {w : ℝ} (hw : 0 < w)
    (hker : ∀ u : MorseL2, (u, E • u) ∈ morseAssociatedGraph α w b → u = 0) :
    Dense (morseGraphRange α w b E : Set MorseL2) := by
  let R := morseGraphRange α w b E
  have ho : Rᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro u hu
    rw [Submodule.mem_bot]
    apply hker u
    rw [morseAssociatedGraph_eq_adjoint α b hw]
    intro q hq
    have hr : q.2 - E • q.1 ∈ R := by
      apply mem_morseGraphRange.mpr
      refine ⟨q.1, morseGraphAtEnergy_mem.mpr ?_⟩
      rw [sub_add_cancel]
      exact hq
    have h := (Submodule.mem_orthogonal R u).mp hu _ hr
    rw [← real_inner_comm (q.2 - E • q.1) u, inner_sub_right, real_inner_smul_right] at h
    change ⟪E • u, q.1⟫_ℝ = ⟪u, q.2⟫_ℝ
    rw [real_inner_smul_left]
    linarith only [h]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (R.topologicalClosure_eq_top_iff.mpr ho)

private theorem morseGraph_unit_residual_weak_zero {α w b E : ℝ}
    (hd : Dense (morseGraphRange α w b E : Set MorseL2)) (u f : ℕ → MorseL2)
    (hu : ∀ n, ‖u n‖ = 1) (hg : ∀ n, (u n, f n) ∈ morseGraphAtEnergy α w b E)
    (hf : Tendsto (fun n => ‖f n‖) atTop (𝓝 0)) (h : MorseL2) :
    Tendsto (fun n => ⟪u n, h⟫_ℝ) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy, hyε⟩ := hd.exists_dist_lt h (by positivity : 0 < ε / 2)
  obtain ⟨v, hv⟩ := mem_morseGraphRange.mp hy
  have hlim : Tendsto (fun n => ‖f n‖ * ‖v‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using hf.mul_const ‖v‖
  have hy0 : Tendsto (fun n => ⟪u n, y⟫_ℝ) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    rw [← morseGraphAtEnergy_symmetric (hg n) hv]
    exact norm_inner_le_norm (𝕜 := ℝ) _ _
  filter_upwards [(Metric.tendsto_nhds.mp hy0) (ε / 2) (by positivity)] with n hn
  have hn' : |⟪u n, y⟫_ℝ| < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero] using hn
  have hbound : |⟪u n, h - y⟫_ℝ| ≤ dist h y := by
    simpa only [Real.norm_eq_abs, hu n, one_mul, dist_eq_norm] using
      norm_inner_le_norm (𝕜 := ℝ) (u n) (h - y)
  rw [Real.dist_eq, sub_zero]
  calc
    _ = |⟪u n, h - y⟫_ℝ + ⟪u n, y⟫_ℝ| := by rw [← inner_add_right, sub_add_cancel]
    _ ≤ _ := abs_add_le _ _
    _ < ε := by linarith

private theorem morseGraphAtEnergy_boundedBelow {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B E : ℝ) (hE : E < j ^ 2 * B)
    (hno : ¬ Statements.ActualEigenvalue (Statements.morsePotential j A B) E) :
    let w := j * sqrt A
    let α := (w - 1) / 2
    let b := j ^ 2 * B
    ∃ c : ℝ, 0 < c ∧ ∀ u f : MorseL2, (u, f) ∈ morseGraphAtEnergy α w b E →
      c * ‖u‖ ≤ ‖f‖ := by
  intro w α b
  have hw : 0 < w := mul_pos hj (sqrt_pos.mpr hA)
  have hker (u : MorseL2) (hu : (u, E • u) ∈ morseAssociatedGraph α w b) : u = 0 := by
    by_contra h
    exact hno ⟨u, h, (morsePublicWeakGraph_iff_associated hj hA B u (E • u)).mpr hu⟩
  have hd := morseGraphRange_dense α b E hw hker
  by_contra! h
  let ε (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hx (n : ℕ) : ∃ u f : MorseL2, (u, f) ∈ morseGraphAtEnergy α w b E ∧ ‖u‖ = 1 ∧ ‖f‖ < ε n := by
    obtain ⟨u, f, hg, hh⟩ := h (ε n) (hε n)
    have hu : 0 < ‖u‖ := by
      by_contra! hz
      have hz' : ‖u‖ = 0 := le_antisymm hz (norm_nonneg _)
      rw [hz', mul_zero] at hh
      exact not_lt_of_ge (norm_nonneg _) hh
    refine ⟨‖u‖⁻¹ • u, ‖u‖⁻¹ • f, (morseGraphAtEnergy α w b E).smul_mem _ hg, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu), inv_mul_cancel₀ hu.ne']
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu), ← div_eq_inv_mul, div_lt_iff₀ hu]
      exact hh
  choose u f hg hu hf using hx
  have hε₀ : Tendsto ε atTop (𝓝 0) := tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hf₀ : Tendsto (fun n => ‖f n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => (hf n).le) hε₀
  have hwSequence : Statements.EssentialWeylValue (Statements.morsePotential j A B) E := by
    refine ⟨u, fun n => f n + E • u n, fun n => ⟨hu n, ?_⟩,
      morseGraph_unit_residual_weak_zero hd u f hu hg hf₀, ?_⟩
    · exact (morsePublicWeakGraph_iff_associated hj hA B _ _).mpr (morseGraphAtEnergy_mem.mp (hg n))
    · simpa only [add_sub_cancel_right] using hf₀
  exact (not_le.mpr hE) (morseThreshold_le_of_essentialWeylValue hj hA B E hwSequence)

/-- There is a uniform positive lower bound for the actual weak graph at a
subthreshold energy without an eigenvector. -/
theorem morseWeakGraph_boundedBelow_of_noEigen {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B E : ℝ) (hE : E < j ^ 2 * B)
    (hno : ¬ Statements.ActualEigenvalue (Statements.morsePotential j A B) E) :
    ∃ c : ℝ, 0 < c ∧ ∀ u f : MorseL2,
      Statements.WeakSchrodingerGraph (Statements.morsePotential j A B) u (f + E • u) → c * ‖u‖ ≤ ‖f‖ := by
  obtain ⟨c, hc, hbound⟩ := morseGraphAtEnergy_boundedBelow hj hA B E hE hno
  refine ⟨c, hc, ?_⟩
  intro u f h
  exact hbound u f (morseGraphAtEnergy_mem.mpr ((morsePublicWeakGraph_iff_associated hj hA B _ _).mp h))

private theorem morseGraphRange_isClosed (α b E : ℝ) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hbound : ∀ u f : MorseL2, (u, f) ∈ morseGraphAtEnergy α w b E → c * ‖u‖ ≤ ‖f‖) :
    IsClosed (morseGraphRange α w b E : Set MorseL2) := by
  apply isClosed_of_closure_subset
  intro f hf
  obtain ⟨F, hF, hlim⟩ := mem_closure_iff_seq_limit.mp hf
  have hg (n : ℕ) : ∃ u : MorseL2, (u, F n) ∈ morseGraphAtEnergy α w b E :=
    mem_morseGraphRange.mp (hF n)
  choose u hu using hg
  have hCauchy : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq (c * ε) (mul_pos hc hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hd := hN m hm n hn
    rw [dist_eq_norm] at hd ⊢
    have hmn : (u m - u n, F m - F n) ∈ morseGraphAtEnergy α w b E :=
      (morseGraphAtEnergy α w b E).sub_mem (hu m) (hu n)
    exact lt_of_mul_lt_mul_left ((hbound _ _ hmn).trans_lt hd) hc.le
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hgraph : (v, f) ∈ morseGraphAtEnergy α w b E :=
    (morseGraphAtEnergy_isClosed α b E hw).mem_of_tendsto (hv.prodMk_nhds hlim) (Eventually.of_forall hu)
  exact mem_morseGraphRange.mpr ⟨v, hgraph⟩

private theorem morse_eq_zero_of_mul_norm_le_zero {c : ℝ} (hc : 0 < c) {u : MorseL2}
    (h : c * ‖u‖ ≤ 0) : u = 0 := by
  by_contra hu
  exact (not_le.mpr (mul_pos hc (norm_pos_iff.mpr hu))) h

/-- The inverse is a genuine bounded linear map on all of `L²`, obtained
from the actual closed graph at the target energy. -/
theorem morseWeakResolventBound_of_noEigen {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B E : ℝ) (hE : E < j ^ 2 * B)
    (hno : ¬ Statements.ActualEigenvalue (Statements.morsePotential j A B) E) :
    ∃ C : ℝ, 0 < C ∧ Statements.WeakResolventBound (Statements.morsePotential j A B) E C := by
  let w := j * sqrt A
  let α := (w - 1) / 2
  let b := j ^ 2 * B
  have hw : 0 < w := mul_pos hj (sqrt_pos.mpr hA)
  let K := morseGraphAtEnergy α w b E
  let R := morseGraphRange α w b E
  have hker (u : MorseL2) (hu : (u, E • u) ∈ morseAssociatedGraph α w b) : u = 0 := by
    by_contra h
    exact hno ⟨u, h, (morsePublicWeakGraph_iff_associated hj hA B u (E • u)).mpr hu⟩
  obtain ⟨c, hc, hbound⟩ := morseGraphAtEnergy_boundedBelow hj hA B E hE hno
  have hDense : Dense (R : Set MorseL2) := morseGraphRange_dense α b E hw hker
  have hClosed : IsClosed (R : Set MorseL2) := morseGraphRange_isClosed α b E hw hc hbound
  have hRange (f : MorseL2) : f ∈ R := by
    have h := hDense f
    rwa [hClosed.closure_eq] at h
  let snd : K →ₗ[ℝ] MorseL2 := (LinearMap.snd ℝ MorseL2 MorseL2).comp K.subtype
  have hsurj : Function.Surjective snd := by
    intro f
    obtain ⟨u, hu⟩ := mem_morseGraphRange.mp (hRange f)
    exact ⟨⟨(u, f), hu⟩, rfl⟩
  have hinj : Function.Injective snd := by
    intro p q h
    have h₂ : p.val.2 = q.val.2 := h
    have hpq : (p.val.1 - q.val.1, p.val.2 - q.val.2) ∈ K := K.sub_mem p.property q.property
    have hq := hbound _ _ hpq
    rw [h₂, sub_self, norm_zero] at hq
    exact Subtype.ext (Prod.ext (sub_eq_zero.mp (morse_eq_zero_of_mul_norm_le_zero hc hq)) h₂)
  let inv := (LinearEquiv.ofBijective snd ⟨hinj, hsurj⟩).symm
  let g := (LinearMap.fst ℝ MorseL2 MorseL2).comp (K.subtype.comp inv.toLinearMap)
  have hgraph (f : MorseL2) : (g f, f) ∈ K := by
    have he : (inv f).val.2 = f := (LinearEquiv.ofBijective snd ⟨hinj, hsurj⟩).apply_symm_apply f
    have hp := (inv f).property
    change (g f, (inv f).val.2) ∈ K at hp
    rwa [he] at hp
  have hg (f : MorseL2) : ‖g f‖ ≤ (1 / c) * ‖f‖ := by
    have hb := hbound _ _ (hgraph f)
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc]
    exact (mul_comm ‖g f‖ c).trans_le hb
  let G := g.mkContinuous (1 / c) hg
  refine ⟨1 / c, one_div_pos.mpr hc, G, g.mkContinuous_norm_le (one_div_nonneg.mpr hc.le) hg, ?_, ?_⟩
  · intro f
    exact (morsePublicWeakGraph_iff_associated hj hA B _ _).mpr (morseGraphAtEnergy_mem.mp (hgraph f))
  · intro u f hu
    have hU : (u, f) ∈ K := morseGraphAtEnergy_mem.mpr
      ((morsePublicWeakGraph_iff_associated hj hA B _ _).mp hu)
    have hdiff : (g f - u, f - f) ∈ K := K.sub_mem (hgraph f) hU
    have hb := hbound _ _ hdiff
    rw [sub_self, norm_zero] at hb
    exact sub_eq_zero.mp (morse_eq_zero_of_mul_norm_le_zero hc hb)

end ContinuousFlexibility.Radial
