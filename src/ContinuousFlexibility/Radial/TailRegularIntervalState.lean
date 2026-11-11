import ContinuousFlexibility.Radial.TailClampedResistance
import ContinuousFlexibility.Radial.TailEdgeFluxBounds
import ContinuousFlexibility.Radial.TailClassicalRegularity

/-!
# An actual state on a regular resistance interval

A small mass--resistance product supplies the Poisson pair on a compact
physical interval. Its nonzero off-diagonal flux permits any prescribed
value and flux at the right end. This includes the separate initial gap
of a deep tail and uses the original density throughout the closed interval.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

/-- Extend any right-end state through a small regular interval. The last
clause records the entrance sign when the outgoing flux exceeds the free
right-end impedance; it will exclude a Dirichlet natural solution. -/
theorem exists_tailRegularInterval_state {p : ℝ → ℝ} {a b Λ : ℝ}
    (hab : a < b) (hp : ContinuousOn p (Icc a b))
    (hp₀ : ∀ x ∈ Icc a b, 0 < p x) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (∫ x in a..b, p x) * (∫ x in a..b, (p x)⁻¹) < 1)
    (A B : ℝ) :
    ∃ u v : ℝ → ℝ,
      TailFirstOrderSystem p Λ u v (Icc a b) ∧ u b = A ∧ v b = B ∧
      (0 ≤ A → A / (∫ x in a..b, (p x)⁻¹) < B → u a < 0) := by
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
  have hδ : tailEdgeDiagonalSize hL q < 1 := by
    have h := tailEdge_green_diagonal_le_mass_resistance (c := 0)
      hL le_rfl hL.le hΛ hρc (fun s _ => (hρpos s).le)
    simp only [sub_zero, sub_self, intervalIntegral.integral_same, zero_mul,
      zero_add, hmass] at h
    rw [hδeq]
    apply h.trans_lt
    simpa only [← hLR, mul_assoc, mul_left_comm, mul_comm] using hsmall
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
  refine ⟨u, v, hstate, ?_, hright, ?_⟩
  · change α * V₀ L + A * V₁ L = A
    rw [hV₀b, hV₁b, mul_zero, mul_one, zero_add]
  · intro hA hB
    have hα : α < 0 := by
      apply div_neg_of_neg_of_pos _ hc
      have hdA := mul_le_mul_of_nonneg_right hd hA
      rw [← hLR] at hB
      have heq : 1 / L * A = A / L := by ring
      rw [heq] at hdA
      exact sub_neg.mpr (hdA.trans_lt hB)
    change α * V₀ (φ a) + A * V₁ (φ a) < 0
    simpa only [hφa, hV₀a, hV₁a, mul_one, mul_zero, add_zero] using hα

end ContinuousFlexibility.Radial
