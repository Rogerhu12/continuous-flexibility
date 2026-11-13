import ContinuousFlexibility.Analysis.MaterialOrdinaryJets
import ContinuousFlexibility.Analysis.MaterialEnvelopeLogJets

/-!
# Physical powers from genuine scalar logarithmic jets

One scalar argument applies to every positive weight with bounded positive
material derivatives of its logarithm. The actual E0 model supplies those
logarithmic bounds; no E0 floor or extra envelope hypothesis is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

/-- Material-coordinate differentiation retains the original real power
of any positive scalar weight with the displayed genuine log-jet bound. -/
theorem iteratedDeriv_materialWeight_rpow_bound_of_log_jets
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {w : ℝ → ℝ} (hw : ContDiffOn ℝ ∞ w (Ioo D.a D.b))
    (hpos : ∀ r ∈ Ioo D.a D.b, 0 < w r)
    (hlog : ∀ k : ℕ, 0 < k → ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioo D.a D.b,
      |materialDerivativeIterate T k (fun t => Real.log (w t)) r| ≤ C)
    (γ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv n (fun t => w (T.radius t) ^ γ) x| ≤ C * w (T.radius x) ^ γ := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, hradius, hinside, _⟩ := hdata
  have hlogw : ContDiffOn ℝ ∞ (fun r => Real.log (w r)) (Ioo D.a D.b) :=
    hw.log (fun r hr => (hpos r hr).ne')
  have hbase : ContDiff ℝ ∞ (fun x => Real.log (w (T.radius x))) :=
    hlogw.comp_contDiff hradius (fun x => (hinside x).1)
  let L : ℝ → ℝ := fun x => Real.log (w (T.radius x)) * γ
  have hL : ContDiff ℝ ∞ L := hbase.mul contDiff_const
  have hLb (k : ℕ) (hk : 0 < k) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv k L x| ≤ C := by
    obtain ⟨C, hC, hb⟩ := hlog k hk
    refine ⟨C * |γ|, mul_nonneg hC (abs_nonneg _), fun x => ?_⟩
    change |iteratedDeriv k (fun t => Real.log (w (T.radius t)) * γ) x| ≤ _
    rw [iteratedDeriv_mul_const_field, iteratedDeriv_comp_materialRadius hT hlogw, abs_mul]
    exact mul_le_mul_of_nonneg_right (hb (T.radius x) (hinside x).1) (abs_nonneg _)
  have hpow : (fun x => w (T.radius x) ^ γ) = (fun x => Real.exp (L x)) := by
    funext x
    exact Real.rpow_def_of_pos (hpos _ (hinside x).1) γ
  obtain ⟨C, hC, hb⟩ := iteratedDeriv_exp_majorant hL hLb n
  refine ⟨C, hC, fun x => ?_⟩
  rw [hpow, congrFun hpow x]
  exact hb x

/-- The actual radial expansion converts scalar material power estimates
to physical derivatives while retaining the weight and paying only E0^A. -/
theorem materialWeight_rpow_physical_jet_bound_of_log_jets
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {w : ℝ → ℝ} (hw : ContDiffOn ℝ ∞ w (Ioo D.a D.b))
    (hpos : ∀ r ∈ Ioo D.a D.b, 0 < w r)
    (hlog : ∀ k : ℕ, 0 < k → ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioo D.a D.b,
      |materialDerivativeIterate T k (fun t => Real.log (w t)) r| ≤ C)
    (γ : ℝ) (n : ℕ) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv n (fun t => w t ^ γ) r| ≤ B * w r ^ γ * T.E0 r ^ A := by
  let f : ℝ → ℝ := fun r => w r ^ γ
  have hf : ContDiffOn ℝ ∞ f (Ioo D.a D.b) :=
    hw.rpow_const_of_ne (fun r hr => (hpos r hr).ne')
  have hmaterial (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |iteratedDeriv j (fun t => f (T.radius t)) x| ≤ B * w (T.radius x) ^ γ :=
    iteratedDeriv_materialWeight_rpow_bound_of_log_jets hT hw hpos hlog γ j
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, hinverse, _, _, _, _, _, hexpansion, _⟩ := hdata
  obtain ⟨c, _, ⟨C, A, hC, hA, hc⟩, hformula⟩ := hexpansion n
  choose B hB hbound using fun j : Fin (n + 1) => hmaterial j.val
  let K : ℝ := ∑ j : Fin (n + 1), C * B j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => mul_nonneg hC (hB j))
  refine ⟨K, A, hK, hA, ?_⟩
  intro r hr
  have hmat (j : Fin (n + 1)) :
      |materialDerivativeIterate T j.val f r| ≤ B j * w r ^ γ := by
    have h := hbound j (T.rho r)
    rw [iteratedDeriv_comp_materialRadius hT hf, hinverse r hr] at h
    exact h
  change |iteratedDeriv n f r| ≤ K * w r ^ γ * T.E0 r ^ A
  rw [hformula f hf r hr]
  calc
    _ ≤ ∑ j : Fin (n + 1), |c j r * materialDerivativeIterate T j.val f r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (n + 1), (C * B j) * w r ^ γ * T.E0 r ^ A := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact (mul_le_mul (hc j r hr) (hmat j) (abs_nonneg _)
        (mul_nonneg hC (Real.rpow_nonneg (hT.2.1 r hr).2.2.1.le _))).trans_eq (by ring)
    _ = K * w r ^ γ * T.E0 r ^ A := by
      rw [Finset.sum_mul, Finset.sum_mul]

/-- The actual envelope and its reciprocal have genuine ordinary jets.
This conclusion follows from IsMaterialData itself for every real power. -/
theorem materialE0_rpow_physical_jet_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (γ : ℝ) (n : ℕ) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv n (fun t => T.E0 t ^ γ) r| ≤ B * T.E0 r ^ γ * T.E0 r ^ A := by
  exact materialWeight_rpow_physical_jet_bound_of_log_jets hT
    (hT.1 T.E0 (by simp)) (fun r hr => (hT.2.1 r hr).2.2.1)
    (fun _ hn => materialE0_log_material_jet_bound hT hn) γ n

end ContinuousFlexibility.Statements
