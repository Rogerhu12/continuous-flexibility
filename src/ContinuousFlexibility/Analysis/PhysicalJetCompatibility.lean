import ContinuousFlexibility.Analysis.SourceJetAssembly

/-!
# Physical source compatibility propagates to genuine jets

The zero-source functional is continuous in the supplied physical height
space. Weighted scalar derivatives with L2 second-variation envelopes
are genuine derivatives in that space. Differentiating the zero value
of the functional therefore proves compatibility of every jet from
compatibility of order zero alone.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {U : Set E}

theorem linearFunctional_vanishes_on_all_jets
    {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (Q : F →L[ℝ] ℝ) (hU : IsOpen U)
    (H : ∀ n : ℕ, E → (Fin n → E) → F)
    (hline : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => H n y v) (H (n + 1) x (Fin.cons w v)) x w)
    (hzero : ∀ x ∈ U, Q (H 0 x Fin.elim0) = 0) :
    ∀ n x, x ∈ U → ∀ v : Fin n → E, Q (H n x v) = 0 := by
  intro n
  induction n with
  | zero =>
    intro x hx v
    have hv : v = Fin.elim0 := funext (fun i => Fin.elim0 i)
    rw [hv]
    exact hzero x hx
  | succ n ih =>
    intro x hx v
    let w := v 0
    let vs := Fin.tail v
    have hd : HasDerivAt (fun t : ℝ => Q (H n (x + t • w) vs))
        (Q (H (n + 1) x (Fin.cons w vs))) 0 := by
      apply hasDerivAt_iff_tendsto_slope_zero.mpr
      simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
        zero_add, zero_smul, add_zero] using (hline n x hx vs w).clm_comp Q
    have hcurve : Tendsto (fun t : ℝ => x + t • w) (𝓝 (0 : ℝ)) (𝓝 x) := by
      have hc : Continuous (fun t : ℝ => x + t • w) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
    have heq : (fun t : ℝ => Q (H n (x + t • w) vs)) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hcurve.eventually (hU.mem_nhds hx)] with t ht
      exact ih _ ht vs
    have hz := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq heq
    simpa only [w, vs, Fin.cons_self_tail] using hd.unique hz

def heightScalarJetValue
    (hH : IsSobolevModel D T (3 / 4 : ℝ) (S.height (3 / 4 : ℝ)))
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, HeightMember D T (3 / 4 : ℝ) (A n x v))
    (n : ℕ) (x : E) (v : Fin n → E) : (S.height (3 / 4 : ℝ)).Space := by
  classical
  exact if hx : x ∈ U then heightRealize hH (A n x v) (hmember n x hx v) else 0

theorem heightScalarJetValue_decode
    (hH : IsSobolevModel D T (3 / 4 : ℝ) (S.height (3 / 4 : ℝ)))
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, HeightMember D T (3 / 4 : ℝ) (A n x v))
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    (S.height (3 / 4 : ℝ)).decode (heightScalarJetValue hH A hmember n x v) = A n x v := by
  classical
  simp only [heightScalarJetValue, dif_pos hx, heightRealize_decode]

theorem sourceJet_compatibility_of_zero_jet
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hU : IsOpen U)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, HeightMember D T (3 / 4 : ℝ) (A n x v))
    (hscalar : ∀ n (x w : E) (v : Fin n → E) (t : ℝ), x + t • w ∈ U → ∀ a b c p,
      HasDerivAt (fun u => weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (A n (x + u • w) v) p)
        (weightedPhysicalJet T (3 / 4 : ℝ) a b c
          (A (n + 1) (x + t • w) (Fin.cons w v)) p) t)
    (henergy : SourceJetSecondEnvelopes (T := T) (U := U) A)
    (hzero : ∀ x ∈ U, physicalSourceIntegral D (A 0 x Fin.elim0) = 0) :
    ∀ n x, x ∈ U → ∀ v, physicalSourceIntegral D (A n x v) = 0 := by
  let hH := hS.1 (3 / 4 : ℝ)
  let H := heightScalarJetValue hH A hmember
  have hdecode := heightScalarJetValue_decode hH A hmember
  have hline : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => H n y v) (H (n + 1) x (Fin.cons w v)) x w := by
    intro n x hx v w
    obtain ⟨δ, hδ, hmem, hb⟩ := henergy n x hx v w
    let J₁ : ℝ → ℕ → ℕ → ℕ → PolarPoint → ℝ := fun t a b c p =>
      weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (A (n + 1) (x + t • w) (Fin.cons w v)) p
    let J₂ : ℝ → ℕ → ℕ → ℕ → PolarPoint → ℝ := fun t a b c p =>
      weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (A (n + 2) (x + t • w) (Fin.cons w (Fin.cons w v))) p
    have hfirst (t : ℝ) (ht : |t| < δ) (a b c : ℕ) (p : PolarPoint) :
        HasDerivAt (fun u => weightedPhysicalJet T (3 / 4 : ℝ) a b c
          ((S.height (3 / 4 : ℝ)).decode (H n (x + u • w) v)) p)
          (J₁ t a b c p) t := by
      apply (hscalar n x w v t (hmem t ht) a b c p).congr_of_eventuallyEq
      have hm : ∀ᶠ u : ℝ in 𝓝 t, x + u • w ∈ U :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
          (hU.mem_nhds (hmem t ht))
      filter_upwards [hm] with u hu
      rw [hdecode n (x + u • w) hu v]
    have hsecond (t : ℝ) (ht : |t| < δ) (a b c : ℕ) (p : PolarPoint) :
        HasDerivAt (fun u => J₁ u a b c p) (J₂ t a b c p) t :=
      hscalar (n + 1) x w (Fin.cons w v) t (hmem t ht) a b c p
    have hvalue (a b c : ℕ) (p : PolarPoint) :
        J₁ 0 a b c p = weightedPhysicalJet T (3 / 4 : ℝ) a b c
          ((S.height (3 / 4 : ℝ)).decode (H (n + 1) x (Fin.cons w v))) p := by
      rw [hdecode (n + 1) x hx (Fin.cons w v)]
      simp only [J₁, zero_smul, add_zero]
    exact height_hasProjectiveCurveDerivAt_of_second_jet_envelopes hH hT
      (fun t : ℝ => H n (x + t • w) v) (H (n + 1) x (Fin.cons w v))
      J₁ J₂ hδ hfirst hsecond hvalue hb
  have hQ : ∀ u : (S.height (3 / 4 : ℝ)).Space,
      S.Q u = physicalSourceIntegral D ((S.height (3 / 4 : ℝ)).decode u) := by
    rcases hS with ⟨_, _, _, _, _, _, _, hQ, _⟩
    exact hQ
  have hQvalue (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
      S.Q (H n x v) = physicalSourceIntegral D (A n x v) := by
    rw [hQ, hdecode n x hx v]
  have hQzero : ∀ x ∈ U, S.Q (H 0 x Fin.elim0) = 0 := by
    intro x hx
    rw [hQvalue 0 x hx Fin.elim0]
    exact hzero x hx
  have hcompat := linearFunctional_vanishes_on_all_jets S.Q hU H hline hQzero
  intro n x hx v
  exact (hQvalue n x hx v).symm.trans (hcompat n x hx v)

end ContinuousFlexibility.Statements
