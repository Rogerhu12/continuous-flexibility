import ContinuousFlexibility.Analysis.N08ProfileJetBounds
import ContinuousFlexibility.Analysis.N08ControlSpatialBounds

/-!
# Actual decay of the scalar profile direction

The true-border cutoff has support in the open radial core, but its closed
support need not lie in a compact subset of that core. Its weighted decay
is therefore extracted from the actual N01 coefficient jets, just as for
the control directions. No stronger support condition is imposed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem n08_scalarCoordinate_grading {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (s : ℕ) (a : ℝ) :
    pairGrading p (pairGrading realGrading q) s (0, a, 0) = ‖a‖ := by
  simp [pairGrading, realGrading]

theorem n08_nuDirection_grading (S : PhysicalSpacesData) (s : ℕ) (a : ℝ) :
    stateGrading S s (0, a, 0, 0) = ‖a‖ :=
  n08_scalarCoordinate_grading (heightPairGrading S)
    (pairGrading (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading) s a

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08_weightedChi_point_jet_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (fun t => D.w t * (a * D.chi t)) r| ≤
        K * T.H r ^ (3 / 64 : ℝ) * ‖a‖ := by
  obtain ⟨B, hB, hBb⟩ := n08_logProfile_reference_jet_bound hT hS hN s
  obtain ⟨K, hK, hKb⟩ := n08_materialSample_point_weight_bound hN.1.1 hT
    (γ := (3 / 4 : ℝ)) (by norm_num) B
  refine ⟨2 * B * K, by positivity, fun a r hr => ?_⟩
  obtain ⟨A, hA⟩ := hN.1.1
  obtain ⟨m, hrm⟩ := hA.2.1.exists_cell hr
  have hb : |iteratedDeriv s (fun t => D.w t * (a * D.chi t)) r| ≤
      B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
        (‖a‖ + ‖a‖) := by
    simpa only [n08_stateLogProfile_nuDirection, n08_nuDirection_grading]
      using hBb m r hrm (0, a, 0, 0)
  calc
    _ ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
        (‖a‖ + ‖a‖) := hb
    _ = (2 * B) * (T.H (T.sample m) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample m) ^ B) * ‖a‖ := by ring
    _ ≤ (2 * B) * (K * T.H r ^ ((3 / 4 : ℝ) / 16)) * ‖a‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hKb m r hrm) (by positivity)) (norm_nonneg a)
    _ = _ := by
      simp only [show (3 / 4 : ℝ) / 16 = 3 / 64 by norm_num]
      ring

private theorem n08_chi_radialJet_eq_iteratedDeriv (s : ℕ) (f : ℝ → ℝ) :
    radialJet s f = iteratedDeriv s f := by
  induction s with
  | zero => rfl
  | succ s ih => rw [radialJet, ih, iteratedDeriv_succ]

theorem n08_chi_point_jet_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (fun t => a * D.chi t) r| ≤
        K * T.M r * T.H r ^ (3 / 64 : ℝ) * ‖a‖ := by
  obtain ⟨A, hA⟩ := hN.1.1
  have hw : ContDiff ℝ ∞ D.w := hA.1.2.2.1.1
  have hwp : ∀ r ∈ Ioo D.a D.b, 0 < D.w r := hA.1.2.2.2.2.1
  have hchi : ContDiff ℝ ∞ D.chi := hN.1.2.2.2.1.1
  have hbF (j : ℕ) (_ : j ≤ s) : ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv j (fun t => (D.w t)⁻¹) r| ≤ K * T.M r := by
    obtain ⟨K, hK, hKb⟩ := referenceInverseJet_le_materialM ⟨A, hA⟩ hT j
    exact ⟨K, hK.le, fun r hr => by
      simpa only [n08_chi_radialJet_eq_iteratedDeriv] using hKb r hr⟩
  obtain ⟨K, hK, hKb⟩ := n08_product_jet_majorant
    (f := fun r => (D.w r)⁻¹) (g := fun a r => D.w r * (a * D.chi r))
    (W := T.M) (V := fun r => T.H r ^ (3 / 64 : ℝ)) (P := fun a : ℝ => ‖a‖)
    isOpen_Ioo (hw.contDiffOn.inv (fun r hr => (hwp r hr).ne'))
    (fun a => (hw.mul (contDiff_const.mul hchi)).contDiffOn)
    (fun r hr => zero_le_one.trans (hT.2.1 r hr).2.2.2)
    (fun r hr => Real.rpow_nonneg (hT.2.1 r hr).2.1.le _) norm_nonneg
    s hbF (fun j _ => n08_weightedChi_point_jet_bound hT hS hN j)
  refine ⟨K, hK, fun a r hr => ?_⟩
  have heq : (fun t => (D.w t)⁻¹ * (D.w t * (a * D.chi t))) =ᶠ[𝓝 r]
      (fun t => a * D.chi t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact inv_mul_cancel_left₀ (hwp t ht).ne' _
  rw [← heq.iteratedDeriv_eq s]
  exact hKb a r hr

/-- All ordinary jets of the scalar cutoff direction satisfy the same
positive physical gain used to realize weak control profiles. -/
theorem n08_chi_decay_jet_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : ℝ, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (fun t => a * D.chi t) r| ≤
        K * ‖a‖ * T.H r ^ (3 / 128 : ℝ) * T.M r := by
  obtain ⟨K, hK, hKb⟩ := n08_chi_point_jet_bound hT hS hN s
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, henv, _⟩ := hdata
  obtain ⟨A, hA, hAb, _, _⟩ := henv 0 (3 / 128) (by norm_num)
  refine ⟨K * A, mul_nonneg hK hA.le, fun a r hr => ?_⟩
  have hH := (hT.2.1 r hr).2.1
  have hM : 0 ≤ T.M r := zero_le_one.trans (hT.2.1 r hr).2.2.2
  have hb : T.H r ^ (3 / 128 : ℝ) ≤ A := by
    simpa only [Real.rpow_zero, mul_one] using hAb r hr
  have hs : T.H r ^ (3 / 64 : ℝ) =
      T.H r ^ (3 / 128 : ℝ) * T.H r ^ (3 / 128 : ℝ) := by
    rw [← Real.rpow_add hH]
    norm_num
  calc
    _ ≤ K * T.M r * T.H r ^ (3 / 64 : ℝ) * ‖a‖ := hKb a r hr
    _ = (K * ‖a‖ * T.H r ^ (3 / 128 : ℝ) * T.M r) *
        T.H r ^ (3 / 128 : ℝ) := by rw [hs]; ring
    _ ≤ (K * ‖a‖ * T.H r ^ (3 / 128 : ℝ) * T.M r) * A :=
      mul_le_mul_of_nonneg_left hb
        (mul_nonneg (mul_nonneg (mul_nonneg hK (norm_nonneg a))
          (Real.rpow_nonneg hH.le _)) hM)
    _ = _ := by ring

end ContinuousFlexibility.Statements
