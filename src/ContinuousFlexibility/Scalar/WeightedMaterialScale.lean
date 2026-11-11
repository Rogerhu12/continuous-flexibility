import ContinuousFlexibility.Scalar.WeightedCoefficientAlgebra

/-!
# The actual material-coordinate scale and logarithmic coefficients

The first radial expansion is tested on the constant function and the
identity. This identifies its leading coefficient with the actual inverse
material scale. Bounded positive logarithmic jets then control every
derivative of that inverse scale. All these coefficients grow by
arbitrarily small powers of the given material envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

variable {D : ReferenceData} {T : MaterialData}

/-- The first universal radial expansion forces the reciprocal scale to
have its asserted envelope. -/
theorem materialEll_inv_le_E0 (hT : IsMaterialData D T) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ r ∈ Ioo D.a D.b,
      (T.ell r)⁻¹ ≤ C * T.E0 r ^ A := by
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, _, _, _, _, _, _, _, hexpansion, _⟩ := hdata
  obtain ⟨c, _, ⟨C, A, hC, hA, hbound⟩, hformula⟩ := hexpansion 1
  refine ⟨C, A, hC, hA, fun r hr => ?_⟩
  have hzero : c 0 r = 0 := by
    have h := hformula (fun _ : ℝ => (1 : ℝ)) contDiffOn_const r hr
    simpa [Fin.sum_univ_two, materialDerivativeIterate, materialDerivative] using h.symm
  have hproduct : c 1 r * T.ell r = 1 := by
    have h := hformula (fun t : ℝ => t) contDiffOn_id r hr
    simpa [Fin.sum_univ_two, materialDerivativeIterate, materialDerivative, hzero] using h.symm
  have hell : 0 < T.ell r := (hpos r hr).1
  have hleading : c 1 r = (T.ell r)⁻¹ := by
    calc
      c 1 r = (c 1 r * T.ell r) * (T.ell r)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hell.ne', mul_one]
      _ = (T.ell r)⁻¹ := by rw [hproduct, one_mul]
  have hb := hbound (1 : Fin 2) r hr
  rwa [hleading, abs_of_pos (inv_pos.mpr hell)] at hb

theorem contDiff_materialLog_pullback (hT : IsMaterialData D T) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo D.a D.b))
    (hpos : ∀ r ∈ Ioo D.a D.b, 0 < f r) :
    ContDiff ℝ ∞ (fun x => Real.log (f (T.radius x))) := by
  obtain ⟨_, _, _, _, _, _, hradius, hinside, _⟩ := hT
  exact (hf.log (fun r hr => (hpos r hr).ne')).comp_contDiff hradius
    (fun x => (hinside x).1)

/-- The assumed material logarithmic bounds become bounds on the actual
ordinary jets after pulling back by the given radius map. -/
theorem iteratedDeriv_materialLogs_bound (hT : IsMaterialData D T)
    (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv n (fun t => Real.log (T.H (T.radius t))) x| ≤ C ∧
      |iteratedDeriv n (fun t => Real.log (T.M (T.radius t))) x| ≤ C ∧
      |iteratedDeriv n (fun t => Real.log (T.ell (T.radius t))) x| ≤ C := by
  have hdata := hT
  obtain ⟨hcont, hpos, _, _, _, _, _, hinside, _, _, _, _, _, hlog, _⟩ := hdata
  have hH : ContDiffOn ℝ ∞ (fun r => Real.log (T.H r)) (Ioo D.a D.b) :=
    (hcont T.H (by simp)).log (fun r hr => (hpos r hr).2.1.ne')
  have hM : ContDiffOn ℝ ∞ (fun r => Real.log (T.M r)) (Ioo D.a D.b) :=
    (hcont T.M (by simp)).log
      (fun r hr => (zero_lt_one.trans_le (hpos r hr).2.2.2).ne')
  have hell : ContDiffOn ℝ ∞ (fun r => Real.log (T.ell r)) (Ioo D.a D.b) :=
    (hcont T.ell (by simp)).log (fun r hr => (hpos r hr).1.ne')
  obtain ⟨C, hC, hb⟩ := hlog n hn
  refine ⟨C, hC, fun x => ?_⟩
  rw [iteratedDeriv_comp_materialRadius hT hH,
    iteratedDeriv_comp_materialRadius hT hM, iteratedDeriv_comp_materialRadius hT hell]
  exact hb (T.radius x) (hinside x).1

/-- Every material-coordinate derivative of the reciprocal scale retains
one factor of that same reciprocal scale. -/
theorem iteratedDeriv_materialEll_inv_bound (hT : IsMaterialData D T) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv n (fun t => (T.ell (T.radius t))⁻¹) x| ≤
        C * (T.ell (T.radius x))⁻¹ := by
  have hell : ContDiffOn ℝ ∞ T.ell (Ioo D.a D.b) := hT.1 T.ell (by simp)
  have hpos : ∀ r ∈ Ioo D.a D.b, 0 < T.ell r := fun r hr => (hT.2.1 r hr).1
  have hinside := hT.2.2.2.2.2.2.2.1
  let L : ℝ → ℝ := fun x => -Real.log (T.ell (T.radius x))
  have hL : ContDiff ℝ ∞ L := (contDiff_materialLog_pullback hT hell hpos).neg
  have hLb (k : ℕ) (hk : 0 < k) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv k L x| ≤ C := by
    obtain ⟨C, hC, hb⟩ := iteratedDeriv_materialLogs_bound hT k hk
    refine ⟨C, hC, fun x => ?_⟩
    simpa only [L, iteratedDeriv_fun_neg, abs_neg] using (hb x).2.2
  have hrepr : (fun x => (T.ell (T.radius x))⁻¹) = fun x => Real.exp (L x) := by
    funext x
    dsimp only [L]
    rw [Real.exp_neg, Real.exp_log (hpos _ (hinside x).1)]
  obtain ⟨C, hC, hb⟩ := iteratedDeriv_exp_majorant hL hLb n
  refine ⟨C, hC, fun x => ?_⟩
  rw [hrepr, congrFun hrepr x]
  exact hb x

theorem materialEll_inv_subpower (hT : IsMaterialData D T) :
    MaterialSubpower T (fun x => (T.ell (T.radius x))⁻¹) := by
  have hdata := hT
  obtain ⟨hcont, hpos, _, _, _, _, hradius, hinside, _⟩ := hdata
  have hell : ContDiff ℝ ∞ (fun x => T.ell (T.radius x)) :=
    (hcont T.ell (by simp)).comp_contDiff hradius (fun x => (hinside x).1)
  obtain ⟨C, A, hC, _, hCb⟩ := materialEll_inv_le_E0 hT
  refine ⟨hell.inv (fun x => (hpos _ (hinside x).1).1.ne'), fun n ε hε => ?_⟩
  obtain ⟨J, hJ, hJb⟩ := iteratedDeriv_materialEll_inv_bound hT n
  obtain ⟨K, hK, hKb⟩ := materialE0_rpow_le_subpowerM hT A hε
  refine ⟨J * C * K, mul_nonneg (mul_nonneg hJ hC) hK.le, fun x => ?_⟩
  calc
    _ ≤ J * (T.ell (T.radius x))⁻¹ := hJb x
    _ ≤ J * (C * T.E0 (T.radius x) ^ A) :=
      mul_le_mul_of_nonneg_left (hCb _ (hinside x).1) hJ
    _ ≤ J * (C * (K * T.M (T.radius x) ^ ε)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hKb _ (hinside x).1) hC) hJ
    _ = (J * C * K) * T.M (T.radius x) ^ ε := by ring

/-- Uniformly bounded ordinary jets are material subpower coefficients
because the actual envelope is at least one. -/
theorem materialSubpower_of_bounded_jets (hT : IsMaterialData D T) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n f x| ≤ C) :
    MaterialSubpower T f := by
  refine ⟨hf, fun n ε hε => ?_⟩
  obtain ⟨C, hC, hCb⟩ := hb n
  refine ⟨C, hC, fun x => ?_⟩
  have hM : 1 ≤ T.M (T.radius x) :=
    (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 x).1).2.2.2
  calc
    _ ≤ C := hCb x
    _ = C * 1 := (mul_one C).symm
    _ ≤ C * T.M (T.radius x) ^ ε :=
      mul_le_mul_of_nonneg_left (Real.one_le_rpow hM hε.le) hC

theorem iteratedDeriv_materialLogH_deriv_bound (hT : IsMaterialData D T) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv n (deriv (fun t => Real.log (T.H (T.radius t)))) x| ≤ C := by
  obtain ⟨C, hC, hb⟩ := iteratedDeriv_materialLogs_bound hT (n + 1) (Nat.succ_pos n)
  exact ⟨C, hC, fun x => by rw [← iteratedDeriv_succ']; exact (hb x).1⟩

theorem materialLogH_deriv_subpower (hT : IsMaterialData D T) :
    MaterialSubpower T (deriv (fun x => Real.log (T.H (T.radius x)))) := by
  have hlog : ContDiff ℝ ∞ (fun x => Real.log (T.H (T.radius x))) :=
    contDiff_materialLog_pullback hT (hT.1 T.H (by simp))
      (fun r hr => (hT.2.1 r hr).2.1)
  exact materialSubpower_of_bounded_jets hT (contDiff_infty_iff_deriv.mp hlog).2
    (iteratedDeriv_materialLogH_deriv_bound hT)

end ContinuousFlexibility.Statements
