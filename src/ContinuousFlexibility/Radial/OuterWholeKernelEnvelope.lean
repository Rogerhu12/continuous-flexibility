import ContinuousFlexibility.Radial.OuterWholeKernelBounds

/-!
# Full cubic localization for the whole normalized Green pair

The actual block identity combines with coefficient bounds and the two
natural decays from the same entrance. The action factor remains squared,
and the exponent between the two position labels remains unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem OuterFundamentalStatePair.kernel_point_envelope
    {a c b : ℝ} {alpha beta P ZP Q ZQ : ℝ → ℝ}
    (F : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    {lam K H L x y : ℝ} {N p q : ℕ}
    (hlam : 0 < lam) (hK : 1 ≤ K) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hN : 1 ≤ N) (hp : N ≤ p) (hq : N ≤ q)
    (hac : a ≤ c) (hcb : c < b) (hPc : P c = 1) (hQc : Q c = 0)
    (hflux : ZQ c = 1 / lam)
    (hU : ∀ t ∈ Icc a c, |F.U t| ≤ K) (hV : ∀ t ∈ Icc a c, |F.V t| ≤ K)
    (hscale : lam⁻¹ ≤ radialE N ^ H)
    (hx : (p = N ∧ x ∈ Icc a c) ∨
      (x ∈ Ico c b ∧ |P x| ≤ radialE p ^ L * exp (-|radialS p - radialS N|)))
    (hy : (q = N ∧ y ∈ Icc a c) ∨
      (y ∈ Ico c b ∧ |P y| ≤ radialE q ^ L * exp (-|radialS q - radialS N|)))
    (hdirichlet : x ∈ Ico c b → y ∈ Ico c b →
      |Q (min x y) * P (max x y)| ≤
        radialE p ^ L * radialE q ^ L * exp (-|radialS p - radialS q|)) :
    |outerGreenKernel lam F.U F.V x y| ≤
      radialE p ^ (2 + H + 2 * L) * radialE q ^ (2 + H + 2 * L) *
        K ^ 2 * exp (-|radialS p - radialS q|) := by
  let ex := radialE p ^ L * exp (-|radialS p - radialS N|)
  let ey := radialE q ^ L * exp (-|radialS q - radialS N|)
  let d := radialE p ^ L * radialE q ^ L * exp (-|radialS p - radialS q|)
  have he (k : ℕ) : 0 ≤ radialE k ^ L :=
    rpow_nonneg (show 0 ≤ radialE k from (exp_pos _).le) _
  have hex : 0 ≤ ex := mul_nonneg (he p) (exp_pos _).le
  have hey : 0 ≤ ey := mul_nonneg (he q) (exp_pos _).le
  have hd : 0 ≤ d := mul_nonneg (mul_nonneg (he p) (he q)) (exp_pos _).le
  have hx' : (x ∈ Icc a c ∧ 1 ≤ ex) ∨ (x ∈ Ico c b ∧ |P x| ≤ ex) := by
    rcases hx with ⟨rfl, hx⟩ | hx
    · refine Or.inl ⟨hx, ?_⟩
      simpa only [ex, sub_self, abs_zero, neg_zero, exp_zero, mul_one] using
        outer_envelope_one_le N hL
    · exact Or.inr hx
  have hy' : (y ∈ Icc a c ∧ 1 ≤ ey) ∨ (y ∈ Ico c b ∧ |P y| ≤ ey) := by
    rcases hy with ⟨rfl, hy⟩ | hy
    · refine Or.inl ⟨hy, ?_⟩
      simpa only [ey, sub_self, abs_zero, neg_zero, exp_zero, mul_one] using
        outer_envelope_one_le N hL
    · exact Or.inr hy
  exact outer_rank_one_envelope hN hp hq hH hL hlam hK hscale
    (F.kernel_blocks_abs_le hlam (zero_le_one.trans hK) hac hcb hPc hQc hflux
      hU hV hex hey hd hx' hy' hdirichlet)

end ContinuousFlexibility.Radial
