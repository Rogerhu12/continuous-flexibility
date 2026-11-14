module

public import ContinuousFlexibility.Radial.TailRegularIntervalState
public import ContinuousFlexibility.Radial.TailNaturalEntrance
public import ContinuousFlexibility.Radial.OuterNaturalNorm

/-!
# The quantitative initial resistance gap

The natural solution may enter a deep tail through a resistance interval.
The actual Poisson coupling bounds give a lower bound for its entrance
value in terms of the outgoing mass flux, and a uniform bound throughout
that initial interval after normalizing at the entrance.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- On a small regular interval, a right-end value of one and a large
positive outgoing flux force a quantitatively large negative entrance
value. The whole interval is bounded by that entrance value. -/
theorem tailRegularInterval_rightState_norm_bounds {p f g : ℝ → ℝ} {a b Λ : ℝ}
    (hab : a < b) (hp : ContinuousOn p (Icc a b))
    (hp₀ : ∀ x ∈ Icc a b, 0 < p x) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (∫ x in a..b, p x) * (∫ x in a..b, (p x)⁻¹) ≤ 1 / 2)
    (hactual : TailFirstOrderSystem p Λ f g (Icc a b))
    (hub : f b = 1) (hLargeFlux : 4 ≤ (∫ x in a..b, (p x)⁻¹) * g b) :
    (∫ x in a..b, (p x)⁻¹) * g b / 4 ≤ |f a| ∧ 1 ≤ |f a| ∧
      ∀ x ∈ Icc a b, |f x| ≤ 4 * |f a| := by
  let A : ℝ := 1
  let B : ℝ := g b
  let p₀ : ℝ → ℝ := tailClampedDensity p a b hab.le
  let φ : ℝ → ℝ := tailResistanceChart p₀ a
  let ρ : ℝ → ℝ := tailResistanceDensity p₀ a
  let L : ℝ := φ b
  have hp₀c : Continuous p₀ := tailClampedDensity_continuous hab.le hp
  have hp₀pos : ∀ x, 0 < p₀ x := tailClampedDensity_pos hab.le hp₀
  have hφa : φ a = 0 := by simp only [φ, tailResistanceChart, intervalIntegral.integral_same]
  have hφmono : StrictMono φ := tailResistanceChart_strictMono hp₀c hp₀pos a
  have hL : 0 < L := by simpa only [hφa] using hφmono hab
  have hLR : L = ∫ x in a..b, (p x)⁻¹ :=
    tailClampedResistanceChart_eq hab.le ⟨hab.le, le_rfl⟩
  have hρc : ContinuousOn ρ (Icc 0 L) := by
    have h := tailClampedResistanceDensity_continuousOn hab.le hp hp₀
    change ContinuousOn ρ (Icc (φ a) (φ b)) at h
    simpa only [hφa] using h
  have hρpos (s : ℝ) : 0 < ρ s := tailClampedResistanceDensity_pos hab.le hp₀ s
  have hφmem {x : ℝ} (hx : x ∈ Icc a b) : φ x ∈ Icc 0 L := by
    exact ⟨by simpa only [hφa] using hφmono.monotone hx.1, hφmono.monotone hx.2⟩
  have hmass : (∫ s in 0..L, ρ s) = ∫ x in a..b, p x := by
    have h := tailClampedResistance_mass_change (p := p) (V := fun _ => 1)
      hab.le hp hp₀ continuous_const ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩
    change (∫ s in φ a..L, ρ s * 1) = ∫ x in a..b, p x * 1 at h
    simpa only [hφa, mul_one] using h
  let q : TailEdgeContinuous 0 L :=
    ⟨fun s => Λ * ρ s, continuous_const.mul hρc.domRestrict⟩
  have hq (s : Icc 0 L) : 0 ≤ q s := mul_nonneg hΛ (hρpos s).le
  have hδeq : tailEdgeDiagonalSize hL q =
      Λ * ∫ s in 0..L, ρ s * tailEdgeGreen 0 L s s := by
    rw [tailEdgeDiagonalSize, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hL.le]
    intro s hs
    dsimp only
    rw [IccExtend_of_mem hL.le q hs]
    change tailEdgeGreen 0 L s s * (Λ * ρ s) = Λ * (ρ s * tailEdgeGreen 0 L s s)
    ring
  have hδhalf : tailEdgeDiagonalSize hL q ≤ 1 / 2 := by
    have h := tailEdge_green_diagonal_le_mass_resistance (c := 0)
      hL le_rfl hL.le hΛ hρc (fun s _ => (hρpos s).le)
    simp only [sub_zero, sub_self, intervalIntegral.integral_same, zero_mul,
      zero_add, hmass] at h
    rw [hδeq]
    apply h.trans
    simpa only [← hLR, mul_assoc, mul_left_comm, mul_comm] using hsmall
  have hδ : tailEdgeDiagonalSize hL q < 1 := hδhalf.trans_lt (by norm_num)
  obtain ⟨V₀, V₁, hV₀, hV₁, hV₀a, hV₀b, hV₁a, hV₁b, hODE, hbnd, hflux⟩ :=
    exists_tailEdgeFluxMatrix hL hq hδ
  let c : ℝ := 1 / L + ∫ s in 0..L,
    tailEdgeLeftHeight 0 L s * IccExtend hL.le q s * V₁ s
  let d : ℝ := 1 / L - ∫ s in 0..L,
    tailEdgeRightHeight 0 L s * IccExtend hL.le q s * V₁ s
  have hc : 0 < c := by
    have h := (tailEdge_flux_coupling_bounds hL hq hδ hV₁.continuous
      (fun s hs => (hbnd s hs).2)).1
    simp only [sub_zero, ← one_div] at h
    exact (one_div_pos.mpr hL).trans_le h
  have hcupper : c ≤ 2 / L := by
    have h := tailEdge_flux_coupling_le_two hL hq hδhalf hV₁.continuous
      (fun s hs => (hbnd s hs).2)
    simpa only [c, sub_zero, one_div] using h
  have hd : d ≤ 1 / L := by
    apply sub_le_self
    apply intervalIntegral.integral_nonneg hL.le
    intro s hs
    exact mul_nonneg
      (mul_nonneg (tailEdgeRightHeight_nonneg hL hs)
        (by rw [IccExtend_of_mem hL.le q hs]; exact hq ⟨s, hs⟩))
      ((tailEdgeRightHeight_nonneg hL hs).trans (hbnd s hs).2.1)
  let α : ℝ := (d * A - B) / c
  let V : ℝ → ℝ := fun s => α * V₀ s + A * V₁ s
  let Q : ℝ → ℝ := fun s => α * deriv V₀ s + A * deriv V₁ s
  have hV (s : ℝ) : HasDerivAt V (Q s) s :=
    ((hV₀ s).hasDerivAt.const_mul α).fun_add ((hV₁ s).hasDerivAt.const_mul A)
  have hdV : deriv V = Q := funext (fun s => (hV s).deriv)
  have hQ (s : ℝ) (hs : s ∈ Icc 0 L) :
      HasDerivAt Q (-(q ⟨s, hs⟩ * V s)) s := by
    apply (((hODE s hs).1.const_mul α).fun_add ((hODE s hs).2.const_mul A)).congr_deriv
    dsimp only [V]
    ring
  let u : ℝ → ℝ := V ∘ φ
  let v : ℝ → ℝ := Q ∘ φ
  have hstate : TailFirstOrderSystem p Λ u v (Icc a b) := by
    intro x hx
    have hφ : HasDerivAt φ (p x)⁻¹ x := hasDerivAt_tailClampedResistanceChart hab.le hp hp₀ hx
    have hρ : ρ (φ x) = p x ^ 2 := tailClampedResistanceDensity_chart hab.le hp hp₀ hx
    constructor
    · simpa only [u, v, Function.comp_apply, div_eq_mul_inv] using (hV (φ x)).comp x hφ
    · apply ((hQ (φ x) (hφmem hx)).comp x hφ).congr_deriv
      change -(Λ * ρ (φ x) * V (φ x)) * (p x)⁻¹ = -Λ * p x * V (φ x)
      rw [hρ]
      field_simp [(hp₀ x hx).ne'] <;> ring
  have hright : v b = B := by
    have h := (hflux α A).2
    simp only [sub_zero] at h
    change deriv V L = -c * α + d * A at h
    rw [hdV] at h
    change Q L = B
    rw [h]
    dsimp only [α]
    field_simp [hc.ne']
    ring
  have hUb : u b = A := by
    change α * V₀ L + A * V₁ L = A
    rw [hV₀b, hV₁b, mul_zero, mul_one, zero_add]
  have hUa : u a = α := by
    change α * V₀ (φ a) + A * V₁ (φ a) = α
    rw [hφa, hV₀a, hV₁a, mul_one, mul_zero, add_zero]
  have hfb : f b = u b := by simpa only [A] using hub.trans hUb.symm
  have hgb : g b = v b := by simpa only [B] using hright.symm
  have heq (x : ℝ) (hx : x ∈ Icc a b) : f x = u x :=
    (tailFirstOrderSystem_eqOn_Icc (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
      hp (fun y hy => (hp₀ y hy).ne') hactual hstate hfb hgb x hx).1
  have hfa : f a = α := (heq a ⟨le_rfl, hab.le⟩).trans hUa
  have hBR : 4 ≤ L * B := by simpa only [B, hLR] using hLargeFlux
  have hBfree : 1 / L < B := (div_lt_iff₀ hL).mpr (by nlinarith only [hBR])
  have hαneg : α < 0 := by
    apply div_neg_of_neg_of_pos _ hc
    dsimp only [A]
    linarith only [hd, hBfree]
  have hαeq : c * α = d - B := by
    dsimp only [α, A]
    field_simp [hc.ne'] <;> ring
  have hcL : c * L ≤ 2 := (le_div_iff₀ hL).mp hcupper
  have hdL : d * L ≤ 1 := (le_div_iff₀ hL).mp hd
  have hαlower : L * B / 4 ≤ |α| := by
    rw [abs_of_neg hαneg]
    have hm := mul_le_mul_of_nonneg_left hcL (neg_nonneg.mpr hαneg.le)
    have he := congrArg (fun z : ℝ => z * L) hαeq
    nlinarith only [hBR, hdL, hm, he]
  have hαone : 1 ≤ |α| := by linarith only [hαlower, hBR]
  have hden : 0 < 1 - tailEdgeDiagonalSize hL q := sub_pos.mpr hδ
  have hdenbound : 1 / (1 - tailEdgeDiagonalSize hL q) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith only [hδhalf]
  have hUbound (x : ℝ) (hx : x ∈ Icc a b) : |u x| ≤ 2 * |α| + 2 := by
    have hs := hφmem hx
    have hheight₀ : tailEdgeLeftHeight 0 L (φ x) ≤ 1 := by
      dsimp only [tailEdgeLeftHeight]
      rw [sub_zero, div_le_one hL]
      linarith only [hs.1]
    have hheight₁ : tailEdgeRightHeight 0 L (φ x) ≤ 1 := by
      dsimp only [tailEdgeRightHeight]
      rw [sub_zero, sub_zero, div_le_one hL]
      exact hs.2
    have hV₀bounds : 0 ≤ V₀ (φ x) ∧ V₀ (φ x) ≤ 2 :=
      ⟨(tailEdgeLeftHeight_nonneg hL hs).trans (hbnd _ hs).1.1,
        (hbnd _ hs).1.2.trans
          ((div_le_div_of_nonneg_right hheight₀ hden.le).trans hdenbound)⟩
    have hV₁bounds : 0 ≤ V₁ (φ x) ∧ V₁ (φ x) ≤ 2 :=
      ⟨(tailEdgeRightHeight_nonneg hL hs).trans (hbnd _ hs).2.1,
        (hbnd _ hs).2.2.trans
          ((div_le_div_of_nonneg_right hheight₁ hden.le).trans hdenbound)⟩
    change |α * V₀ (φ x) + A * V₁ (φ x)| ≤ _
    simp only [A, one_mul]
    calc
      _ ≤ |α * V₀ (φ x)| + |V₁ (φ x)| := abs_add_le _ _
      _ = |α| * V₀ (φ x) + V₁ (φ x) := by
        rw [abs_mul, abs_of_nonneg hV₀bounds.1, abs_of_nonneg hV₁bounds.1]
      _ ≤ |α| * 2 + 2 := add_le_add
        (mul_le_mul_of_nonneg_left hV₀bounds.2 (abs_nonneg _)) hV₁bounds.2
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · simpa only [B, hLR, hfa] using hαlower
  · simpa only [hfa] using hαone
  · intro x hx
    rw [heq x hx, hfa]
    exact (hUbound x hx).trans (by linarith only [hαone])

/-- The large first mass flux gives the missing quantitative estimate on
the initial resistance interval. This uses the original density and the
actual first-order solution on that interval. -/
theorem tailActualState_initialGap_norm_bounds {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {u v : ℝ → ℝ} (hsys : TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint))
    (hu₀ : u (T.node 0) = 1) (hv₀ : T.Λ * tailMass T 0 / 2 ≤ v (T.node 0))
    (hgap : T.entrance < T.node 0) :
    1 ≤ |u T.entrance| ∧
      T.Λ * tailMass T 0 * tailInitialResistance T ≤ 8 * |u T.entrance| ∧
      ∀ x ∈ Icc T.entrance (T.node 0), |u x| ≤ 4 * |u T.entrance| := by
  rcases hT.2.2.2.1 with heq | hg
  · exfalso
    rw [heq] at hgap
    exact (lt_irrefl _) hgap
  · have hsub := deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0)
    have hp := (deepTail_contDiffOn hT).continuousOn.mono hsub
    have hp₀ := fun x hx => deepTail_pos hT x (hsub hx)
    have hR : 0 < tailInitialResistance T := deepTail_interval_resistance_pos hT
      le_rfl hgap (deepTail_node_lt_endpoint hT 0)
    have hsmall : T.Λ * (∫ x in T.entrance..T.node 0, T.p x) *
        (∫ x in T.entrance..T.node 0, (T.p x)⁻¹) ≤ 1 / 2 := by
      exact hg.2.1.trans (hη.trans (by norm_num))
    have hvscaled : T.Λ * tailMass T 0 * tailInitialResistance T / 2 ≤
        tailInitialResistance T * v (T.node 0) := by
      have h := mul_le_mul_of_nonneg_right hv₀ hR.le
      nlinarith only [h]
    have hflux : 4 ≤ (∫ x in T.entrance..T.node 0, (T.p x)⁻¹) * v (T.node 0) := by
      change 4 ≤ tailInitialResistance T * v (T.node 0)
      linarith only [hvscaled, hg.2.2.2, hK]
    obtain ⟨hlower, hone, hbound⟩ := tailRegularInterval_rightState_norm_bounds hgap hp hp₀
      hT.2.2.1.le hsmall (hsys.mono hsub) hu₀ hflux
    change tailInitialResistance T * v (T.node 0) / 4 ≤ |u T.entrance| at hlower
    exact ⟨hone, by nlinarith only [hlower, hvscaled], hbound⟩

/-- The same entrance lower bound covers a mass entrance and a separate
initial resistance gap, without splitting the natural solution object. -/
theorem tailActualState_entrance_abs_ge_one {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {u v : ℝ → ℝ} (hsys : TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint))
    (hu₀ : u (T.node 0) = 1) (hv₀ : T.Λ * tailMass T 0 / 2 ≤ v (T.node 0)) :
    1 ≤ |u T.entrance| := by
  rcases hT.2.2.2.1 with heq | hg
  · rw [← heq, hu₀, abs_one]
  · exact (tailActualState_initialGap_norm_bounds hT hη hK hsys hu₀ hv₀ hg.1).1

/-- The normalized initial-gap square integral is bounded by the first
mass. Integrability alone would not supply this scale. -/
theorem tailActualState_initial_sq_integral_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {u v : ℝ → ℝ} (hsys : TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint))
    (hu₀ : u (T.node 0) = 1) (hv₀ : T.Λ * tailMass T 0 / 2 ≤ v (T.node 0)) :
    (∫ x in T.entrance..T.node 0, T.p x * u x ^ 2) ≤ tailMass T 0 * u T.entrance ^ 2 := by
  rcases hT.2.2.2.1 with heq | hg
  · rw [heq, intervalIntegral.integral_same]
    exact mul_nonneg (tailMass_pos hT 0).le (sq_nonneg _)
  · have hsub := deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0)
    have hp := (deepTail_contDiffOn hT).continuousOn.mono hsub
    have huc : ContinuousOn u (Icc T.entrance (T.node 0)) :=
      HasDerivAt.continuousOn (fun x hx => (hsys x (hsub hx)).1)
    have hbound := (tailActualState_initialGap_norm_bounds hT hη hK hsys hu₀ hv₀ hg.1).2.2
    have hpoint (x : ℝ) (hx : x ∈ Icc T.entrance (T.node 0)) :
        T.p x * u x ^ 2 ≤ (16 * u T.entrance ^ 2) * T.p x := by
      have hu2 : u x ^ 2 ≤ 16 * u T.entrance ^ 2 := by
        calc
          _ = |u x| ^ 2 := (sq_abs _).symm
          _ ≤ (4 * |u T.entrance|) ^ 2 :=
            (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (hbound x hx)
          _ = _ := by rw [mul_pow, sq_abs]; norm_num
      calc
        _ ≤ T.p x * (16 * u T.entrance ^ 2) :=
          mul_le_mul_of_nonneg_left hu2 (deepTail_pos hT x (hsub hx)).le
        _ = _ := mul_comm _ _
    have hi := intervalIntegral.integral_mono_on hg.1.le
      ((hp.mul (huc.pow 2)).intervalIntegrable_of_Icc (μ := volume) hg.1.le)
      ((continuousOn_const.mul hp).intervalIntegrable_of_Icc (μ := volume) hg.1.le) hpoint
    change (∫ x in T.entrance..T.node 0, T.p x * u x ^ 2) ≤
      ∫ x in T.entrance..T.node 0, (16 * u T.entrance ^ 2) * T.p x at hi
    rw [intervalIntegral.integral_const_mul] at hi
    change (∫ x in T.entrance..T.node 0, T.p x * u x ^ 2) ≤
      (16 * u T.entrance ^ 2) * tailInitialGapMass T at hi
    have hmass : 16 * tailInitialGapMass T ≤ tailMass T 0 := by
      have h₁ := mul_le_mul_of_nonneg_left hg.2.2.1 (by norm_num : (0 : ℝ) ≤ 16)
      have h₂ := mul_le_mul_of_nonneg_right hη (tailMass_pos hT 0).le
      nlinarith only [h₁, h₂]
    have h := mul_le_mul_of_nonneg_right hmass (sq_nonneg (u T.entrance))
    nlinarith only [hi, h]

/-- The first mass value of the entrance-normalized solution has the
extra inverse mass--resistance factor when an initial gap is present. -/
theorem tailActualState_initialGap_normalized_first_node_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {u v : ℝ → ℝ} (hsys : TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint))
    (hu₀ : u (T.node 0) = 1) (hv₀ : T.Λ * tailMass T 0 / 2 ≤ v (T.node 0))
    (hgap : T.entrance < T.node 0) :
    |u (T.node 0) / u T.entrance| ≤
      8 / (T.Λ * tailMass T 0 * tailInitialResistance T) := by
  obtain ⟨hone, hlarge, _⟩ := tailActualState_initialGap_norm_bounds hT hη hK hsys hu₀ hv₀ hgap
  have huabs : 0 < |u T.entrance| := lt_of_lt_of_le (by norm_num) hone
  have hR : 0 < tailInitialResistance T := deepTail_interval_resistance_pos hT
    le_rfl hgap (deepTail_node_lt_endpoint hT 0)
  have hden : 0 < T.Λ * tailMass T 0 * tailInitialResistance T :=
    mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT 0)) hR
  rw [hu₀, abs_div, abs_one]
  apply (div_le_div_iff₀ huabs hden).mpr
  simpa only [one_mul] using hlarge

/-- The quantitative initial-gap estimate and the outward node sum
control the complete weighted norm by the entrance value, in both
allowed entrance geometries. -/
theorem tailNaturalEquation_full_sq_integral_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {u v : ℝ → ℝ} (hu : TailNaturalEquation T u)
    (hsys : TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint))
    (hu₀ : u (T.node 0) = 1) (hv₀ : T.Λ * tailMass T 0 / 2 ≤ v (T.node 0))
    (hstep : ∀ n, |u (T.node (n + 1))| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |u (T.node n)|) :
    (∫ x, u x ^ 2 ∂deepTailMeasure T) ≤ 33 * tailMass T 0 * u T.entrance ^ 2 := by
  let f : ℝ → ℝ := fun x => T.p x * u x ^ 2
  have hwhole : IntegrableOn f (Ioo T.entrance T.endpoint) :=
    (tail_integrable_density_iff ((deepTail_contDiffOn hT).mono Ioo_subset_Ico_self)
      (fun x hx => deepTail_pos hT x ⟨hx.1.le, hx.2⟩) _).mp hu.2.2.1.integrable_sq
  have hi : IntegrableOn f (Ioc T.entrance (T.node 0)) :=
    hwhole.mono_set (fun _ hx => ⟨hx.1, hx.2.trans_lt (deepTail_node_lt_endpoint hT 0)⟩)
  have ho : IntegrableOn f (Ioo (T.node 0) T.endpoint) :=
    hwhole.mono_set (fun _ hx => ⟨hT.2.1.trans_lt hx.1, hx.2⟩)
  have hcover : Ioo T.entrance T.endpoint =
      Ioc T.entrance (T.node 0) ∪ Ioo (T.node 0) T.endpoint := by
    ext x
    constructor
    · intro hx
      by_cases hxnode : x ≤ T.node 0
      · exact Or.inl ⟨hx.1, hxnode⟩
      · exact Or.inr ⟨lt_of_not_ge hxnode, hx.2⟩
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hx.1, hx.2.trans_lt (deepTail_node_lt_endpoint hT 0)⟩
      · exact ⟨hT.2.1.trans_lt hx.1, hx.2⟩
  have hdis : Disjoint (Ioc T.entrance (T.node 0)) (Ioo (T.node 0) T.endpoint) :=
    Set.disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hx.2) hy.1)
  have hsplit : (∫ x in Ioo T.entrance T.endpoint, f x) =
      (∫ x in T.entrance..T.node 0, f x) + ∫ x in Ico (T.node 0) T.endpoint, f x := by
    rw [hcover, setIntegral_union hdis measurableSet_Ioo hi ho,
      ← intervalIntegral.integral_of_le hT.2.1, ← integral_Ico_eq_integral_Ioo]
  have hinitial := tailActualState_initial_sq_integral_le hT hη hK hsys hu₀ hv₀
  have hout := tailNaturalEquation_outward_sq_integral_le hT hη hK hu hstep
  rw [hu₀, one_pow, mul_one] at hout
  have hone := tailActualState_entrance_abs_ge_one hT hη hK hsys hu₀ hv₀
  have hsq : 1 ≤ u T.entrance ^ 2 := by
    have h := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hone
    simpa only [one_mul, ← pow_two, sq_abs, one_pow] using h
  have hscale := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) (tailMass_pos hT 0).le)
  rw [tail_integral_density ((deepTail_contDiffOn hT).mono Ioo_subset_Ico_self)
    (fun x hx => deepTail_pos hT x ⟨hx.1.le, hx.2⟩)]
  change (∫ x in Ioo T.entrance T.endpoint, f x) ≤ _
  rw [hsplit]
  dsimp only [f]
  nlinarith only [hinitial, hout, hscale]

/-- The complete natural solution, normalized at the actual entrance,
has squared weighted norm at most thirty-three first masses. -/
theorem tailNaturalEquation_normalized_sq_integral_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {u v : ℝ → ℝ} (hu : TailNaturalEquation T u)
    (hsys : TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint))
    (hu₀ : u (T.node 0) = 1) (hv₀ : T.Λ * tailMass T 0 / 2 ≤ v (T.node 0))
    (hstep : ∀ n, |u (T.node (n + 1))| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |u (T.node n)|) :
    (∫ x, (u x / u T.entrance) ^ 2 ∂deepTailMeasure T) ≤ 33 * tailMass T 0 := by
  have hone := tailActualState_entrance_abs_ge_one hT hη hK hsys hu₀ hv₀
  have hune : u T.entrance ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hone
    norm_num at hone
  simp_rw [div_pow]
  rw [integral_div]
  apply (div_le_iff₀ (sq_pos_of_ne_zero hune)).mpr
  exact tailNaturalEquation_full_sq_integral_le hT hη hK hu hsys hu₀ hv₀ hstep

end ContinuousFlexibility.Radial
