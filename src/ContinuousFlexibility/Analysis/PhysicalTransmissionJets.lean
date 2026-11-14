module

public import ContinuousFlexibility.Analysis.PhysicalTransmissionOperator
public import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace
public import ContinuousFlexibility.Analysis.TransmissionJetAlgebra

/-!
# Matching all physical jets across a noncharacteristic interface

Tangential differentiation preserves equality of a normal trace. The
divergence equation then determines the next normal derivative because
its leading normal coefficient is nonzero. All identities concern the
actual mixed derivatives from the statement layer.

Source: the readable manuscript, §7, lines 1725–1755.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Analysis
open scoped ContDiff

private theorem transmission_slice_smooth {g : PolarPoint → ℝ}
    (hg : ContDiff ℝ ∞ g) (θ : ℝ) :
    ContDiff ℝ ∞ (fun r : ℝ => g (r, θ)) :=
  hg.comp (contDiff_id.prodMk contDiff_const)

private theorem transmission_mixed_radial {g : PolarPoint → ℝ}
    (hg : ContDiff ℝ ∞ g) (i j : ℕ) (p : PolarPoint) :
    mixedDerivative i j (radialPartial g) p = mixedDerivative (i + 1) j g p :=
  mixedDerivative_radialPartial isOpen_univ hg.contDiffOn i j (mem_univ p)

private theorem transmission_mixed_angular {g : PolarPoint → ℝ}
    (hg : ContDiff ℝ ∞ g) (i j : ℕ) (p : PolarPoint) :
    mixedDerivative i j (angularPartial g) p = mixedDerivative i (j + 1) g p :=
  mixedDerivative_angularPartial isOpen_univ hg.contDiffOn i j (mem_univ p)

private theorem transmission_mixed_radial_two {g : PolarPoint → ℝ}
    (hg : ContDiff ℝ ∞ g) (i j : ℕ) (p : PolarPoint) :
    mixedDerivative i j (radialPartial (radialPartial g)) p =
      mixedDerivative (i + 2) j g p := by
  simpa only [Nat.add_assoc] using
    (transmission_mixed_radial (contDiff_cylinder_radialPartial hg) i j p).trans
      (transmission_mixed_radial hg (i + 1) j p)

private theorem transmission_mixed_angular_radial {g : PolarPoint → ℝ}
    (hg : ContDiff ℝ ∞ g) (i j : ℕ) (p : PolarPoint) :
    mixedDerivative i j (angularPartial (radialPartial g)) p =
      mixedDerivative (i + 1) (j + 1) g p :=
  (transmission_mixed_angular (contDiff_cylinder_radialPartial hg) i j p).trans
    (transmission_mixed_radial hg i (j + 1) p)

private theorem transmission_mixed_angular_two {g : PolarPoint → ℝ}
    (hg : ContDiff ℝ ∞ g) (i j : ℕ) (p : PolarPoint) :
    mixedDerivative i j (angularPartial (angularPartial g)) p =
      mixedDerivative i (j + 2) g p := by
  simpa only [Nat.add_assoc] using
    (transmission_mixed_angular (contDiff_cylinder_angularPartial hg) i j p).trans
      (transmission_mixed_angular hg i (j + 1) p)

/-- A matching normal trace has matching derivatives in every tangential
order, with no further use of the equation. -/
theorem mixedDerivative_trace_eq_of_normal_trace {u v : PolarPoint → ℝ} {r0 : ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (i : ℕ)
    (htrace : ∀ θ, mixedDerivative i 0 u (r0, θ) = mixedDerivative i 0 v (r0, θ)) :
    ∀ j : ℕ, ∀ θ, mixedDerivative i j u (r0, θ) = mixedDerivative i j v (r0, θ) := by
  intro j
  induction j with
  | zero => exact htrace
  | succ j ih =>
      intro θ
      have he : (fun t => mixedDerivative i j u (r0, t)) =
          (fun t => mixedDerivative i j v (r0, t)) := funext ih
      calc
        mixedDerivative i (j + 1) u (r0, θ) =
            angularPartial (mixedDerivative i j u) (r0, θ) :=
          (congrFun (angularPartial_mixedDerivative hu i j) (r0, θ)).symm
        _ = deriv (fun t => mixedDerivative i j u (r0, t)) θ :=
          (deriv_cylinder_angular_slice
            ((contDiff_mixedDerivative hu i j).differentiable (by simp)) r0 θ).symm
        _ = deriv (fun t => mixedDerivative i j v (r0, t)) θ :=
          congrArg (fun g : ℝ → ℝ => deriv g θ) he
        _ = angularPartial (mixedDerivative i j v) (r0, θ) :=
          deriv_cylinder_angular_slice
            ((contDiff_mixedDerivative hv i j).differentiable (by simp)) r0 θ
        _ = mixedDerivative i (j + 1) v (r0, θ) :=
          congrFun (angularPartial_mixedDerivative hv i j) (r0, θ)

private theorem transmission_normal_add {g h : PolarPoint → ℝ}
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (n : ℕ) (p : PolarPoint) :
    mixedDerivative n 0 (fun q => g q + h q) p =
      mixedDerivative n 0 g p + mixedDerivative n 0 h p := by
  simpa only [mixedDerivative, iteratedDeriv_zero] using
    iteratedDeriv_fun_add (n := n) (x := p.1)
      ((transmission_slice_smooth hg p.2).contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      ((transmission_slice_smooth hh p.2).contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))

private theorem transmission_normal_add_congr {g₁ g₂ h₁ h₂ : PolarPoint → ℝ}
    (hg₁ : ContDiff ℝ ∞ g₁) (hg₂ : ContDiff ℝ ∞ g₂)
    (hh₁ : ContDiff ℝ ∞ h₁) (hh₂ : ContDiff ℝ ∞ h₂)
    {n : ℕ} {p : PolarPoint}
    (hg : mixedDerivative n 0 g₁ p = mixedDerivative n 0 g₂ p)
    (hh : mixedDerivative n 0 h₁ p = mixedDerivative n 0 h₂ p) :
    mixedDerivative n 0 (fun q => g₁ q + h₁ q) p =
      mixedDerivative n 0 (fun q => g₂ q + h₂ q) p := by
  rw [transmission_normal_add hg₁ hh₁, transmission_normal_add hg₂ hh₂, hg, hh]

private theorem transmission_normal_mul_congr {a f g : PolarPoint → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (p : PolarPoint)
    (hfg : ∀ i : ℕ, i ≤ n → mixedDerivative i 0 f p = mixedDerivative i 0 g p) :
    mixedDerivative n 0 (fun q => a q * f q) p =
      mixedDerivative n 0 (fun q => a q * g q) p := by
  have h := iteratedDeriv_mul_eq_of_jets
    (transmission_slice_smooth ha p.2) (transmission_slice_smooth hf p.2)
    (transmission_slice_smooth hg p.2) n (x := p.1) (by
      intro i hi
      simpa only [mixedDerivative, iteratedDeriv_zero] using hfg i hi)
  simpa only [mixedDerivative, iteratedDeriv_zero] using h

private theorem transmission_normal_mul_cancel {a f g : PolarPoint → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (p : PolarPoint) (ha0 : a p ≠ 0)
    (hfg : ∀ i : ℕ, i < n → mixedDerivative i 0 f p = mixedDerivative i 0 g p)
    (hprod : mixedDerivative n 0 (fun q => a q * f q) p =
      mixedDerivative n 0 (fun q => a q * g q) p) :
    mixedDerivative n 0 f p = mixedDerivative n 0 g p := by
  have h := iteratedDeriv_eq_of_mul_eq_of_lower_jets
    (transmission_slice_smooth ha p.2) (transmission_slice_smooth hf p.2)
    (transmission_slice_smooth hg p.2) n (x := p.1) ha0 (by
      intro i hi
      simpa only [mixedDerivative, iteratedDeriv_zero] using hfg i hi) (by
      simpa only [mixedDerivative, iteratedDeriv_zero] using hprod)
  simpa only [mixedDerivative, iteratedDeriv_zero] using h

private def transmissionLower (L : SymmetricCoefficients) (u : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ :=
  2 * L.b p * angularPartial (radialPartial u) p +
    L.c p * angularPartial (angularPartial u) p +
    (radialPartial L.a p + angularPartial L.b p) * radialPartial u p +
    (radialPartial L.b p + angularPartial L.c p) * angularPartial u p

private theorem transmissionLower_smooth {L : SymmetricCoefficients} {u : PolarPoint → ℝ}
    (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b) (hc : ContDiff ℝ ∞ L.c)
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (transmissionLower L u) := by
  have hur := contDiff_cylinder_radialPartial hu
  have hut := contDiff_cylinder_angularPartial hu
  exact ((((contDiff_const.mul hb).mul (contDiff_cylinder_angularPartial hur)).add
    (hc.mul (contDiff_cylinder_angularPartial hut))).add
      (((contDiff_cylinder_radialPartial ha).add (contDiff_cylinder_angularPartial hb)).mul hur)).add
    (((contDiff_cylinder_radialPartial hb).add (contDiff_cylinder_angularPartial hc)).mul hut)

private theorem divergenceOperator_eq_normal_add_lower {L : SymmetricCoefficients}
    {u : PolarPoint → ℝ} (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b)
    (hc : ContDiff ℝ ∞ L.c) (hu : ContDiff ℝ ∞ u) :
    divergenceOperator L u =
      fun p => L.a p * radialPartial (radialPartial u) p + transmissionLower L u p := by
  funext p
  rw [divergenceOperator_expansion ha hb hc hu p]
  unfold transmissionLower
  ring

private theorem transmissionLower_normal_congr {L : SymmetricCoefficients}
    {u v : PolarPoint → ℝ} (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b)
    (hc : ContDiff ℝ ∞ L.c) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (n : ℕ) (p : PolarPoint)
    (hjets : ∀ i : ℕ, i < n + 2 → ∀ j : ℕ,
      mixedDerivative i j u p = mixedDerivative i j v p) :
    mixedDerivative n 0 (transmissionLower L u) p =
      mixedDerivative n 0 (transmissionLower L v) p := by
  have hur := contDiff_cylinder_radialPartial hu
  have hvr := contDiff_cylinder_radialPartial hv
  have hut := contDiff_cylinder_angularPartial hu
  have hvt := contDiff_cylinder_angularPartial hv
  have hA : ContDiff ℝ ∞ (fun q => 2 * L.b q) := contDiff_const.mul hb
  have hB : ContDiff ℝ ∞ (fun q => radialPartial L.a q + angularPartial L.b q) :=
    (contDiff_cylinder_radialPartial ha).add (contDiff_cylinder_angularPartial hb)
  have hC : ContDiff ℝ ∞ (fun q => radialPartial L.b q + angularPartial L.c q) :=
    (contDiff_cylinder_radialPartial hb).add (contDiff_cylinder_angularPartial hc)
  have h₁ := transmission_normal_mul_congr hA
    (contDiff_cylinder_angularPartial hur) (contDiff_cylinder_angularPartial hvr) n p (by
      intro i hi
      rw [transmission_mixed_angular_radial hu, transmission_mixed_angular_radial hv]
      exact hjets (i + 1) (by omega) 1)
  have h₂ := transmission_normal_mul_congr hc
    (contDiff_cylinder_angularPartial hut) (contDiff_cylinder_angularPartial hvt) n p (by
      intro i hi
      rw [transmission_mixed_angular_two hu, transmission_mixed_angular_two hv]
      exact hjets i (by omega) 2)
  have h₃ := transmission_normal_mul_congr hB hur hvr n p (by
    intro i hi
    rw [transmission_mixed_radial hu, transmission_mixed_radial hv]
    exact hjets (i + 1) (by omega) 0)
  have h₄ := transmission_normal_mul_congr hC hut hvt n p (by
    intro i hi
    rw [transmission_mixed_angular hu, transmission_mixed_angular hv]
    exact hjets i (by omega) 1)
  have hu₁ := hA.mul (contDiff_cylinder_angularPartial hur)
  have hv₁ := hA.mul (contDiff_cylinder_angularPartial hvr)
  have hu₂ := hc.mul (contDiff_cylinder_angularPartial hut)
  have hv₂ := hc.mul (contDiff_cylinder_angularPartial hvt)
  have hu₃ := hB.mul hur
  have hv₃ := hB.mul hvr
  have hu₄ := hC.mul hut
  have hv₄ := hC.mul hvt
  have h₁₂ := transmission_normal_add_congr hu₁ hv₁ hu₂ hv₂ h₁ h₂
  have h₁₂₃ := transmission_normal_add_congr (hu₁.add hu₂) (hv₁.add hv₂) hu₃ hv₃ h₁₂ h₃
  exact transmission_normal_add_congr ((hu₁.add hu₂).add hu₃) ((hv₁.add hv₂).add hv₃)
    hu₄ hv₄ h₁₂₃ h₄

/-- At the next normal order the only unknown term is the highest
derivative multiplied by the nonzero normal coefficient. -/
private theorem transmission_normal_step {L : SymmetricCoefficients}
    {u v : PolarPoint → ℝ} (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b)
    (hc : ContDiff ℝ ∞ L.c) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (n : ℕ) (p : PolarPoint) (ha0 : L.a p ≠ 0)
    (hjets : ∀ i : ℕ, i < n + 2 → ∀ j : ℕ,
      mixedDerivative i j u p = mixedDerivative i j v p)
    (heq : mixedDerivative n 0 (divergenceOperator L u) p =
      mixedDerivative n 0 (divergenceOperator L v) p) :
    mixedDerivative (n + 2) 0 u p = mixedDerivative (n + 2) 0 v p := by
  have hurr := contDiff_cylinder_radialPartial (contDiff_cylinder_radialPartial hu)
  have hvrr := contDiff_cylinder_radialPartial (contDiff_cylinder_radialPartial hv)
  have hLower := transmissionLower_normal_congr ha hb hc hu hv n p hjets
  have hprod :
      mixedDerivative n 0 (fun q => L.a q * radialPartial (radialPartial u) q) p =
        mixedDerivative n 0 (fun q => L.a q * radialPartial (radialPartial v) q) p := by
    rw [divergenceOperator_eq_normal_add_lower ha hb hc hu,
      divergenceOperator_eq_normal_add_lower ha hb hc hv,
      transmission_normal_add (ha.mul hurr) (transmissionLower_smooth ha hb hc hu),
      transmission_normal_add (ha.mul hvrr) (transmissionLower_smooth ha hb hc hv),
      hLower] at heq
    exact add_right_cancel heq
  have htop := transmission_normal_mul_cancel ha hurr hvrr n p ha0 (by
    intro i hi
    rw [transmission_mixed_radial_two hu, transmission_mixed_radial_two hv]
    exact hjets (i + 2) (by omega) 0) hprod
  rw [transmission_mixed_radial_two hu, transmission_mixed_radial_two hv] at htop
  exact htop

/-- Smooth solutions on the two strips with common value and conormal
traces have every actual mixed physical jet equal at the interface. -/
theorem physicalTransmission_matching_jets
    (a r0 b : ℝ) (L : SymmetricCoefficients) (f u v : PolarPoint → ℝ)
    (har : a < r0) (hrb : r0 < b)
    (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b) (hc : ContDiff ℝ ∞ L.c)
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hpositive : ∀ p ∈ Ioo a b ×ˢ univ, 0 < L.a p)
    (hleft : ∀ p ∈ Ioo a r0 ×ˢ univ, divergenceOperator L u p = f p)
    (hright : ∀ p ∈ Ioo r0 b ×ˢ univ, divergenceOperator L v p = f p)
    (hvalue : ∀ θ, u (r0, θ) = v (r0, θ))
    (hconormal : ∀ θ,
      L.a (r0, θ) * radialPartial u (r0, θ) + L.b (r0, θ) * angularPartial u (r0, θ) =
        L.a (r0, θ) * radialPartial v (r0, θ) + L.b (r0, θ) * angularPartial v (r0, θ)) :
    ∀ i j : ℕ, ∀ θ, mixedDerivative i j u (r0, θ) = mixedDerivative i j v (r0, θ) := by
  have ha0 (θ : ℝ) : L.a (r0, θ) ≠ 0 :=
    (hpositive (r0, θ) ⟨⟨har, hrb⟩, mem_univ θ⟩).ne'
  have hfirst := radialPartial_eq_of_value_conormal hu hv ha0 hvalue hconormal
  have hEq (n : ℕ) (θ : ℝ) :
      mixedDerivative n 0 (divergenceOperator L u) (r0, θ) =
        mixedDerivative n 0 (divergenceOperator L v) (r0, θ) := by
    have hl := mixedDerivative_eqOn_closed_strip har
      (contDiff_divergenceOperator ha hb hc hu) hf hleft n 0
      (show (r0, θ) ∈ Icc a r0 ×ˢ (univ : Set ℝ) from
        ⟨⟨har.le, le_rfl⟩, mem_univ θ⟩)
    have hr := mixedDerivative_eqOn_closed_strip hrb
      (contDiff_divergenceOperator ha hb hc hv) hf hright n 0
      (show (r0, θ) ∈ Icc r0 b ×ˢ (univ : Set ℝ) from
        ⟨⟨le_rfl, hrb.le⟩, mem_univ θ⟩)
    exact hl.trans hr.symm
  have hNormal (n : ℕ) :
      ∀ θ, mixedDerivative n 0 u (r0, θ) = mixedDerivative n 0 v (r0, θ) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        cases n with
        | zero =>
            intro θ
            simpa only [mixedDerivative, iteratedDeriv_zero] using hvalue θ
        | succ n =>
            cases n with
            | zero =>
                intro θ
                have he := hfirst θ
                have hu0 : mixedDerivative 0 0 (radialPartial u) (r0, θ) =
                    radialPartial u (r0, θ) := by simp only [mixedDerivative, iteratedDeriv_zero]
                have hv0 : mixedDerivative 0 0 (radialPartial v) (r0, θ) =
                    radialPartial v (r0, θ) := by simp only [mixedDerivative, iteratedDeriv_zero]
                exact (transmission_mixed_radial hu 0 0 (r0, θ)).symm.trans
                  (hu0.trans (he.trans (hv0.symm.trans (transmission_mixed_radial hv 0 0 (r0, θ)))))
            | succ n =>
                intro θ
                apply transmission_normal_step ha hb hc hu hv n (r0, θ) (ha0 θ)
                · intro i hi j
                  exact mixedDerivative_trace_eq_of_normal_trace hu hv i (ih i hi) j θ
                · exact hEq n θ
  intro i j
  exact mixedDerivative_trace_eq_of_normal_trace hu hv i (hNormal i) j

end ContinuousFlexibility.Statements
