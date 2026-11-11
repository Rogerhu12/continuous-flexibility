import ContinuousFlexibility.Analysis.RadialPlateauHeight
import ContinuousFlexibility.Analysis.MaterialPlateauWeights

/-!
# Common actual jet bounds for a complete plateau

All physical jets vanish outside the expanded support. Inside that
support, the endpoint band transfers the exact inverse height weight
and a fixed material order to the sample of the actual containing cell.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

theorem weightedPhysicalJet_radialPlateauHeight_zero_off_support
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (γ : ℝ) (h : ℝ → ℝ) {l r δ : ℝ} (hδ : 0 < δ)
    (a b c : ℕ) (p : PolarPoint)
    (hp : T.radius p.1 ∉ Icc (l - δ) (r + δ)) :
    weightedPhysicalJet T γ a b c (radialPlateauHeight h l r δ) p = 0 := by
  by_cases hb : b = 0
  · subst b
    obtain ⟨_, _, _, _, _, _, hradius, _⟩ := hT
    have hnear : ∀ᶠ x : ℝ in 𝓝 p.1, T.radius x ∉ Icc (l - δ) (r + δ) :=
      hradius.continuous.continuousAt.eventually (isClosed_Icc.isOpen_compl.mem_nhds hp)
    have heq : materialPlateauPullback T γ h l r δ =ᶠ[𝓝 p.1] (0 : ℝ → ℝ) := by
      filter_upwards [hnear] with x hx
      have hx' : T.radius x ∉ Ioo (l - δ) (r + δ) :=
        fun hh => hx ⟨hh.1.le, hh.2.le⟩
      simp only [materialPlateauPullback, radialPlateauProduct,
        radialPlateauCutoff_zero hδ hx', zero_mul, mul_zero, Pi.zero_apply]
    have hd : iteratedDeriv a (materialPlateauPullback T γ h l r δ) p.1 = 0 := by
      simpa only [iteratedDeriv_const_zero, Pi.zero_apply] using heq.iteratedDeriv_eq a
    rw [weightedPhysicalJet_radialPlateauHeight_zero_angle, hd, mul_zero]
  · exact weightedPhysicalJet_radialPlateauHeight_positive_angle T γ h l r δ a b c
      (Nat.pos_of_ne_zero hb) p

/-- A single finite-order bound applies to every jet in the physical
norm, on the full cylinder and for the actual plateau field. -/
theorem referencePlateau_common_weightedJet_bound
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j →
      ∀ a b c : ℕ, a ≤ n → c ≤ n → ∀ p : PolarPoint,
        |weightedPhysicalJet T β a b c
          (radialPlateauHeight (referenceRadialPrimitive D)
            l r (endpointPlateauWidth D l r)) p| ≤
          K * (endpointPlateauWidth D l r)⁻¹ ^ n *
            T.H (T.sample j) ^ (-β) * T.E0 (T.sample j) ^ A *
              T.M (T.sample j) ^ (n + 1) := by
  classical
  have hgeom : RadialProfileGeometry D := (Classical.choose_spec hD).1
  have hcoeff (a : Fin (n + 1)) :=
    referencePlateau_weightedPhysicalJet_bound hgeom hT β a.val
  choose Ka hKa hKab using hcoeff
  let K₀ : ℝ := 1 + ∑ a : Fin (n + 1), Ka a
  have hK₀ : 0 < K₀ :=
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun a _ => hKa a))
  have hKale (a : Fin (n + 1)) : Ka a ≤ K₀ :=
    (Finset.single_le_sum (fun i _ => hKa i) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_left zero_le_one)
  obtain ⟨Kw, A, hKw, hA, hweight⟩ := materialPlateau_sample_weight_bound hT hD
    hβ (Nat.cast_nonneg (R := ℝ) n) (by norm_num : (0 : ℝ) < 1)
  have hpos := hT.2.1
  have hinside := hT.2.2.2.2.2.2.2.1
  have hsamp : ∀ j, T.sample j ∈ Ioo D.a D.b := by
    obtain ⟨_, hdata⟩ := hD
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsamp, _⟩ := hT
    exact fun j => hdata.2.1.2.2.2.1 j (hsamp j)
  refine ⟨K₀ * Kw, A, mul_pos hK₀ hKw, hA, ?_⟩
  intro j l r hl hlr hr hcell a b c ha hc p
  have hδ : 0 < endpointPlateauWidth D l r := endpointPlateauWidth_pos hl hr
  have hδ1 := endpointPlateauWidth_le_one D l r
  have hsampleH : 0 < T.H (T.sample j) := (hpos _ (hsamp j)).2.1
  have hsampleE : 0 < T.E0 (T.sample j) := (hpos _ (hsamp j)).2.2.1
  have hsampleM : 0 < T.M (T.sample j) := zero_lt_one.trans_le (hpos _ (hsamp j)).2.2.2
  by_cases hp : T.radius p.1 ∈
      Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r)
  · let ai : Fin (n + 1) := ⟨a, Nat.lt_succ_of_le ha⟩
    have hM : 1 ≤ T.M (T.radius p.1) := (hpos _ (hinside p.1).1).2.2.2
    have hH : 0 ≤ T.H (T.radius p.1) ^ (-β) :=
      Real.rpow_nonneg (hpos _ (hinside p.1).1).2.1.le _
    have hδa : 0 ≤ (endpointPlateauWidth D l r)⁻¹ ^ a := by positivity
    have hδn : 0 ≤ (endpointPlateauWidth D l r)⁻¹ ^ n := by positivity
    have hMcn : T.M (T.radius p.1) ^ c ≤ T.M (T.radius p.1) ^ n :=
      pow_le_pow_right₀ hM hc
    have hb := hKab ai b c l r _ hδ hδ1 p
    have hlocal : Ka ai * (endpointPlateauWidth D l r)⁻¹ ^ a *
        T.H (T.radius p.1) ^ (-β) * T.M (T.radius p.1) ^ c ≤
        K₀ * (endpointPlateauWidth D l r)⁻¹ ^ n *
          (T.H (T.radius p.1) ^ (-β) * T.M (T.radius p.1) ^ n) := by
      have hfirst := mul_le_mul (hKale ai)
        (inv_pow_le_inv_pow_of_le_one hδ hδ1 ha) hδa hK₀.le
      have hsecond := mul_le_mul_of_nonneg_left hMcn hH
      have hh := mul_le_mul hfirst hsecond
        (mul_nonneg hH (pow_nonneg (zero_le_one.trans hM) c))
        (mul_nonneg hK₀.le hδn)
      simpa only [mul_assoc] using hh
    have hw : T.H (T.radius p.1) ^ (-β) * T.M (T.radius p.1) ^ n ≤
        Kw * T.H (T.sample j) ^ (-β) * T.E0 (T.sample j) ^ A *
          T.M (T.sample j) ^ (n + 1) := by
      simpa only [Real.rpow_natCast, Nat.cast_add, Nat.cast_one] using
        hweight j l r hl hlr hr hcell (T.radius p.1) hp
    calc
      _ ≤ K₀ * (endpointPlateauWidth D l r)⁻¹ ^ n *
          (T.H (T.radius p.1) ^ (-β) * T.M (T.radius p.1) ^ n) := hb.trans hlocal
      _ ≤ K₀ * (endpointPlateauWidth D l r)⁻¹ ^ n *
          (Kw * T.H (T.sample j) ^ (-β) * T.E0 (T.sample j) ^ A *
            T.M (T.sample j) ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hK₀.le hδn)
      _ = _ := by ring
  · rw [weightedPhysicalJet_radialPlateauHeight_zero_off_support
      hT β _ hδ a b c p hp, abs_zero]
    positivity

end ContinuousFlexibility.Statements
