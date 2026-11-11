import ContinuousFlexibility.Statements.Radial
import ContinuousFlexibility.Radial.OscillatorPotentialEnergy
import ContinuousFlexibility.Radial.CentralRadialHilbert
import ContinuousFlexibility.Radial.CentralLeftAsymptotics
import ContinuousFlexibility.Radial.CentralRightAsymptotics
import ContinuousFlexibility.Radial.CentralTurningPoints

/-!
# Exact bridges to the frozen central-model statement

The independently specified product energy domain is identified with the
actual absolute-potential domain. All domain, core and distribution clauses
are retained. The final R03 conjunction is assembled only after every clause
has been proved for its stated test class.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

theorem centralPotential_statement_eq (j : ℝ) :
    Statements.centralPotential j = centralPotentialValue j := by
  funext x
  unfold Statements.centralPotential centralPotentialValue centralPotentialConstant
  ring

theorem centralWeakRadialDerivative_iff (u d : HermiteL2) :
    Statements.WeakRadialDerivative u d ↔ HasWeakDerivativeL2 u d := by
  constructor <;> intro h φ hs hc <;> have hh := h φ hs hc <;> linarith only [hh]

/-- Coordinate regrouping is a homeomorphism. The max product norm is
not identified with the Hilbert sum norm. -/
def centralStatementEnergyHomeomorph :
    (HermiteL2 × HermiteL2 × HermiteL2) ≃ₜ PhysicalEnergyTriple where
  toFun p := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => HermiteL2)).symm
    ![p.1, p.2.1, p.2.2]
  invFun z := (z 0, z 1, z 2)
  left_inv _ := rfl
  right_inv z := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  continuous_toFun :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => HermiteL2)).symm.continuous.comp
      (by
        apply continuous_pi
        intro i
        fin_cases i <;> fun_prop)
  continuous_invFun :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => HermiteL2) 0).continuous).prodMk
      (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => HermiteL2) 1).continuous).prodMk
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => HermiteL2) 2).continuous)

@[simp] theorem centralStatementEnergyHomeomorph_zero
    (p : HermiteL2 × HermiteL2 × HermiteL2) :
    centralStatementEnergyHomeomorph p 0 = p.1 := rfl

@[simp] theorem centralStatementEnergyHomeomorph_one
    (p : HermiteL2 × HermiteL2 × HermiteL2) :
    centralStatementEnergyHomeomorph p 1 = p.2.1 := rfl

@[simp] theorem centralStatementEnergyHomeomorph_two
    (p : HermiteL2 × HermiteL2 × HermiteL2) :
    centralStatementEnergyHomeomorph p 2 = p.2.2 := rfl

theorem centralStatementEnergyLift_eq_preimage (j : ℝ) :
    Statements.SchrodingerEnergyLift (Statements.centralPotential j) =
      centralStatementEnergyHomeomorph ⁻¹'
        (potentialEnergyGraph j : Set PhysicalEnergyTriple) := by
  ext p
  change (Statements.WeakRadialDerivative p.1 p.2.1 ∧ _) ↔
    (HasWeakDerivativeL2 p.1 p.2.1 ∧ _)
  rw [centralWeakRadialDerivative_iff]
  simp only [potentialEnergyWeight, ← centralPotential_statement_eq,
    centralStatementEnergyHomeomorph_zero, centralStatementEnergyHomeomorph_two]

theorem centralStatementEnergyCore_eq_preimage (j : ℝ) :
    Statements.SchrodingerEnergyCore (Statements.centralPotential j) =
      centralStatementEnergyHomeomorph ⁻¹' potentialCompactSmoothCore j := by
  ext p
  change (∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    (p.1 : ℝ → ℝ) =ᵐ[volume] φ ∧
    (p.2.1 : ℝ → ℝ) =ᵐ[volume] deriv φ ∧ _) ↔ _
  simp only [Set.mem_preimage, potentialCompactSmoothCore, Set.mem_ofPred_eq,
    potentialEnergyWeight, ← centralPotential_statement_eq,
    centralStatementEnergyHomeomorph_zero, centralStatementEnergyHomeomorph_one,
    centralStatementEnergyHomeomorph_two]

theorem centralStatementEnergyLift_isClosed (j : ℝ) :
    IsClosed (Statements.SchrodingerEnergyLift (Statements.centralPotential j)) := by
  rw [centralStatementEnergyLift_eq_preimage]
  exact (potentialEnergyGraph_isClosed j).preimage centralStatementEnergyHomeomorph.continuous

theorem centralStatementEnergyCore_closure {j : ℝ} (hj : 0 < j) :
    closure (Statements.SchrodingerEnergyCore (Statements.centralPotential j)) =
      Statements.SchrodingerEnergyLift (Statements.centralPotential j) := by
  rw [centralStatementEnergyCore_eq_preimage,
    ← centralStatementEnergyHomeomorph.preimage_closure,
    potentialCompactSmoothCore_closure hj, centralStatementEnergyLift_eq_preimage]

theorem centralSchrodingerFormGraph_iff (j : ℝ) (u v : HermiteL2) :
    Statements.SchrodingerFormGraph (Statements.centralPotential j) u v ↔
      PotentialClosedFormEquation j u v := by
  constructor
  · rintro ⟨d, q, hmem, hform⟩
    let z : PotentialEnergySpace j := ⟨centralStatementEnergyHomeomorph (u, d, q),
      by
        change centralStatementEnergyHomeomorph (u, d, q) ∈ potentialEnergyGraph j
        rw [centralStatementEnergyLift_eq_preimage] at hmem
        exact hmem⟩
    refine ⟨z, rfl, ?_⟩
    intro w
    have hw : (w.val 0, w.val 1, w.val 2) ∈
        Statements.SchrodingerEnergyLift (Statements.centralPotential j) := by
      rw [centralStatementEnergyLift_eq_preimage]
      change centralStatementEnergyHomeomorph
        (centralStatementEnergyHomeomorph.symm w.val) ∈ potentialEnergyGraph j
      simpa only [centralStatementEnergyHomeomorph.apply_symm_apply] using w.property
    change Integrable (fun x => centralPotentialValue j x * u x * w.val 0 x) volume ∧
      ⟪v, w.val 0⟫_ℝ = ⟪d, w.val 1⟫_ℝ +
        ∫ x, centralPotentialValue j x * u x * w.val 0 x
    simpa only [centralPotential_statement_eq] using hform (w.val 0, w.val 1, w.val 2) hw
  · rintro ⟨z, hbase, hform⟩
    refine ⟨z.val 1, z.val 2, ?_, ?_⟩
    · rw [← hbase, centralStatementEnergyLift_eq_preimage]
      change centralStatementEnergyHomeomorph
        (centralStatementEnergyHomeomorph.symm z.val) ∈ potentialEnergyGraph j
      simpa only [centralStatementEnergyHomeomorph.apply_symm_apply] using z.property
    · intro p hp
      let w : PotentialEnergySpace j := ⟨centralStatementEnergyHomeomorph p,
        by
          change centralStatementEnergyHomeomorph p ∈ potentialEnergyGraph j
          rw [centralStatementEnergyLift_eq_preimage] at hp
          exact hp⟩
      have hh := hform w
      have hb : w.val 0 = p.1 := rfl
      have hd : w.val 1 = p.2.1 := rfl
      rw [hb, hd, hbase] at hh
      simpa only [centralPotential_statement_eq] using hh

theorem centralWeakSchrodingerGraph_iff {j : ℝ} (hj : 0 < j) (u v : HermiteL2) :
    Statements.WeakSchrodingerGraph (Statements.centralPotential j) u v ↔
      (u, v) ∈ centralClosedGraph hj := by
  rw [centralClosedGraph_iff_compact_weak]
  simp only [Statements.WeakSchrodingerGraph, CentralCompactWeakEquation,
    central_liouvilleSchrodinger, Statements.centralPotential]

theorem centralActualClosedFormRealization {j : ℝ} (hj : 0 < j) :
    Statements.ActualClosedFormRealization (Statements.centralPotential j) := by
  refine ⟨⟨|centralPotentialConstant j|, ?_⟩,
    centralStatementEnergyLift_isClosed j, centralStatementEnergyCore_closure hj, ?_⟩
  · intro x
    rw [centralPotential_statement_eq]
    exact centralPotentialValue_lower j x
  · intro u v
    rw [centralSchrodingerFormGraph_iff, centralWeakSchrodingerGraph_iff hj,
      potentialClosedFormEquation_iff_centralClosedGraph hj]

theorem centralFullDifferentialSpectrum_statement : Statements.CentralFullDifferentialSpectrum := by
  intro j hj
  refine ⟨centralActualClosedFormRealization hj, ?_⟩
  intro u v
  exact (centralWeakSchrodingerGraph_iff hj u v).trans (mem_centralClosedGraph_iff hj u v)

theorem centralReducedInverse_statement : Statements.CentralReducedInverse := by
  refine ⟨centralReducedHilbertInverse, centralReducedHilbertInverse_norm, ?_, ?_⟩
  · intro f
    exact (centralWeakSchrodingerGraph_iff (by norm_num) _ _).mpr
      (centralReducedHilbertInverse_graph_projected f)
  · intro u f h
    exact centralReducedHilbertInverse_left_projected u f
      ((centralWeakSchrodingerGraph_iff (by norm_num) u f).mp h)

theorem centralWeakResolventBound_statement (n : ℕ) (hn : 2 ≤ n) :
    Statements.WeakResolventBound (Statements.centralPotential (2 * n)) 0 (2 / centralGapDelta) := by
  have hj : (0 : ℝ) < 2 * (n : ℝ) := by exact_mod_cast (by omega : 0 < 2 * n)
  refine ⟨centralHilbertInverse n hn, centralHilbertInverse_norm_le n hn, ?_, ?_⟩
  · intro f
    simpa only [zero_smul, add_zero] using
      (centralWeakSchrodingerGraph_iff hj _ _).mpr (centralHilbertInverse_graph n hn f)
  · intro u f h
    apply centralHilbertInverse_left n hn u f
    apply (centralWeakSchrodingerGraph_iff hj u f).mp
    simpa only [zero_smul, add_zero] using h

theorem centralWeakKernel_statement (u : HermiteL2) :
    Statements.WeakSchrodingerGraph (Statements.centralPotential 2) u 0 ↔
      ∃ c : ℝ, u = c • hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0 := by
  exact (centralWeakSchrodingerGraph_iff (by norm_num) u 0).trans
    (centralClosedGraph_two_kernel_iff u)

theorem centralWeightedInverseBounds_statement : Statements.CentralWeightedInverseBounds := by
  have hC : 0 < centralRadialDoubleConstant := by
    unfold centralRadialDoubleConstant
    exact mul_pos
      (mul_pos (by norm_num) (sq_pos_of_pos centralRadiusWeightConstant_pos))
      (div_pos (by norm_num) centralGapDelta_pos)
  refine ⟨centralRadialDoubleConstant, hC, ?_⟩
  intro n hn ψ hs hc f hf
  have hψ := compactSmooth_energyDomain hs hc
  have hνψ := memLp_centralRadialWeight hψ.2.1 hψ.2.2.2
  let F : HermiteL2 := hνψ.toLp (fun x => centralRadiusLogDerivative x * ψ x)
  have hFν : (F : ℝ → ℝ) =ᵐ[volume]
      (fun x => centralRadiusLogDerivative x * ψ x) := hνψ.coeFn_toLp
  have hFs : (F : ℝ → ℝ) =ᵐ[volume]
      (fun x => Statements.centralUpsilon x * ψ x) := by
    simpa only [Statements.centralUpsilon, centralRadiusLogDerivative] using hFν
  have hw : HasCentralRadialWeightL2 f F := by
    filter_upwards [hFν, hf] with x hFx hfx
    rw [hFx, hfx]
  by_cases h1 : n = 1
  · subst n
    refine ⟨F, centralReducedHilbertInverse F, centralRadialReducedDoubleInverse f,
      hFs, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.cast_one, mul_one, ite_eq_left (rfl : (1 : ℕ) = 1), ite_true] using
        (centralWeakSchrodingerGraph_iff (by norm_num : (0 : ℝ) < 2) _ _).mpr
          (centralReducedHilbertInverse_graph_projected F)
    · intro _
      rw [centralGroundProjection_apply, centralReducedHilbertInverse_zero_coefficient,
        zero_smul]
    · simpa only [HasCentralRadialWeightL2, Statements.centralUpsilon,
        centralRadiusLogDerivative] using centralRadialReducedDoubleInverse_weighted f F hw
    · exact (centralRadialReducedDoubleInverse.le_opNorm f).trans
        (mul_le_mul_of_nonneg_right centralRadialReducedDoubleInverse_norm_le_uniform
          (norm_nonneg f))
  · have hn2 : 2 ≤ n := by omega
    have hj : (0 : ℝ) < 2 * (n : ℝ) := by
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    refine ⟨F, centralHilbertInverse n hn2 F, centralRadialDoubleInverse n hn2 f,
      hFs, ?_, ?_, ?_, ?_⟩
    · rw [ite_eq_right h1]
      exact (centralWeakSchrodingerGraph_iff hj _ _).mpr (centralHilbertInverse_graph n hn2 F)
    · intro h
      exact (h1 h).elim
    · simpa only [HasCentralRadialWeightL2, Statements.centralUpsilon,
        centralRadiusLogDerivative] using centralRadialDoubleInverse_weighted n hn2 f F hw
    · exact ((centralRadialDoubleInverse n hn2).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right (centralRadialDoubleInverse_norm_le n hn2) (norm_nonneg f))

theorem radialJet_eq_iteratedDeriv (s : ℕ) (f : ℝ → ℝ) :
    Statements.radialJet s f = iteratedDeriv s f := by
  induction s with
  | zero => exact (iteratedDeriv_zero).symm
  | succ s hs => rw [Statements.radialJet, hs, iteratedDeriv_succ]

theorem centralAllOrderAsymptotics_statement : Statements.CentralAllOrderAsymptotics := by
  intro s
  obtain ⟨Cl, hCl, hleft⟩ := centralRadiusLogDerivative_left_original_derivative_error s
  obtain ⟨Cr, hCr, hright⟩ := centralRadiusLogDerivative_right_derivative_error s
  refine ⟨max Cl Cr + 1, centralRadiusAlpha + 1,
    by linarith [le_max_left Cl Cr], by linarith [centralRadiusAlpha_gt_half], ?_, ?_⟩
  · intro x hx
    have hx1 : 1 ≤ x := by linarith [centralRadiusAlpha_gt_half]
    have hxpos : 0 < x := zero_lt_one.trans_le hx1
    have heq : (fun y : ℝ => centralRadiusLogDerivative y -
        (centralRadiusA + y + (centralRadiusAlpha - 1) / y)) =
        (fun y : ℝ => Statements.centralUpsilon y -
          (y + centralRadiusA + (centralRadiusAlpha - 1) / y)) := by
      funext y
      unfold Statements.centralUpsilon centralRadiusLogDerivative
      ring
    have hpow : x ^ (-3 - (s : ℝ)) = 1 / |x| ^ (3 + s) := by
      rw [abs_of_pos hxpos,
        show (-3 : ℝ) - (s : ℝ) = -((3 + s : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_neg hxpos.le, Real.rpow_natCast, one_div]
    rw [radialJet_eq_iteratedDeriv]
    have hh := hright x hx1
    rw [heq, Real.norm_eq_abs, hpow] at hh
    calc
      _ ≤ Cr / |x| ^ (3 + s) := by simpa only [mul_one_div] using hh
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith [le_max_right Cl Cr]) (by positivity)
  · intro x hx
    rw [radialJet_eq_iteratedDeriv]
    have hh := hleft x hx
    change |iteratedDeriv s (fun y => Statements.centralUpsilon y -
      (-y + centralRadiusA - centralRadiusAlpha / y)) x| ≤ _ at hh
    exact hh.trans (div_le_div_of_nonneg_right
      (by linarith [le_max_left Cl Cr]) (by positivity))

theorem centralKernelHeight_radial_logarithmic_derivative (x : ℝ) :
    centralRadius x * deriv centralKernelHeight (centralRadius x) /
      centralKernelHeight (centralRadius x) =
        (centralRadiusA - 2 * x) / Statements.centralUpsilon x := by
  have hh := ((contDiffAt_centralKernelHeight x).differentiableAt (by simp)).hasDerivAt
  have he : HasDerivAt exp (centralRadius x) (log (centralRadius x)) := by
    simpa only [exp_log (centralRadius_pos x)] using hasDerivAt_exp (log (centralRadius x))
  have hcomp := hh.comp_of_eq (log (centralRadius x)) he (exp_log (centralRadius_pos x)).symm
  change HasDerivAt (fun y : ℝ => centralKernelHeight (exp y)) _ _ at hcomp
  have hs := centralKernelHeight_logarithmic_derivative x
  rw [hcomp.deriv] at hs
  simpa only [Function.comp_apply, Statements.centralUpsilon,
    centralRadiusLogDerivative, mul_comm] using hs

theorem centralRadialProfile_radial_logarithmic_derivative (x : ℝ) :
    centralRadius x * deriv (centralRadialProfile 1) (centralRadius x) /
      centralRadialProfile 1 (centralRadius x) =
        (x ^ 2 - centralOscillatorA) / Statements.centralUpsilon x ^ 2 := by
  have hs := centralRadialProfile_deriv_scaled 1 x
  rw [centralRadialProfile_pullback]
  unfold Statements.centralUpsilon
  field_simp [(centralDensityRoot_pos x).ne', (centralRadius_pos x).ne',
    (deriv_centralRadius_pos x).ne']
  nlinarith only [hs]

theorem centralRadialContact_statement : Statements.CentralRadialContact := by
  refine ⟨range_centralRadius, ?_, ?_, centralKernelHeight_radial_logarithmic_derivative,
    centralRadialProfile_radial_logarithmic_derivative, ?_, ?_, ?_, ?_⟩
  · intro scale _ x
    exact centralRadialProfile_pullback scale x
  · intro scale r _ hr
    have hh := radialJacobi_centralKernel scale (centralModelCoordinate r)
    rwa [centralRadius_modelCoordinate hr] at hh
  · have hs := centralKernelHeight_left_logarithmic_slope_tendsto.comp tendsto_neg_atBot_atTop
    simpa only [centralKernelHeight_logarithmic_derivative, Function.comp_def, neg_neg,
      Statements.centralUpsilon, centralRadiusLogDerivative] using hs
  · simpa only [Statements.centralUpsilon, centralRadiusLogDerivative] using
      centralRightHeightSlope_tendsto
  · have hs := (centralRadialProfile_left_logarithmic_slope_tendsto
      (by norm_num : (0 : ℝ) < 1)).comp tendsto_neg_atBot_atTop
    simpa only [centralRadialProfile_logarithmic_derivative (by norm_num : (0 : ℝ) < 1),
      Function.comp_def, neg_neg,
      Statements.centralUpsilon, centralRadiusLogDerivative] using hs
  · simpa only [Statements.centralUpsilon, centralRadiusLogDerivative] using
      centralRightProfileSlope_tendsto

theorem centralRadialProfile_simple_turning {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hzero : deriv (centralRadialProfile c) r = 0) :
    deriv (deriv (centralRadialProfile c)) r ≠ 0 := by
  rcases (centralRadialProfile_critical_iff hc hr).mp hzero with h | h
  · rw [h]
    exact (centralRadialProfile_second_deriv_left_neg hc).ne
  · rw [h]
    exact (centralRadialProfile_second_deriv_right_pos hc).ne'

end ContinuousFlexibility.Radial
