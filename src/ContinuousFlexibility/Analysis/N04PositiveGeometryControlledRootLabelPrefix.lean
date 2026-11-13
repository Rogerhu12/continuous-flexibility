import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootLabelDirections
import ContinuousFlexibility.Analysis.N04RealizationFixedBasePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootLabelSample

/-!
# Fixed-base normalized prefixes of the actual inverse-root slope

The low parameter order is selected before the parameter prefix. Five
intrinsic angular derivatives are included at that fixed low order; a
finite parameter prefix changes only its high-order shift. The resulting
bounds apply to every genuine tower of the literal inverse-label slope.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

local instance n04ControlledRootLabelPrefixStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The full inverse-label displacement, with five intrinsic angular
orders absorbed at a single low base before all parameter prefixes. -/
theorem n04PositiveGeometry_rootInverseDefect_fixedBase_prefix_of_flow
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
        ∀ k : ℕ, k ≤ K → ∀ u : ℕ, u ≤ s → ∀ b : ℕ, b ≤ u + 5 →
        ∀ side : Bool, ∀ m : ℕ, ∀ θ : ℝ,
        ∀ J : SmoothDirections (sectorNeighborhood S base ε ε) (fun x =>
          iteratedDeriv b (fun α =>
            Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m side) α - α) θ),
        ∀ x ∈ sectorNeighborhood S base ε ε,
          pairGrading (sectorGrading S) realGrading low x ≤ 1 →
        ∀ v : Fin k → (StateDirections S × ℝ),
          (∀ j, pairGrading (sectorGrading S) realGrading low (v j) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R →
          pairGrading (sectorGrading S) realGrading (low + s + shift * K + 1) x ≤ R →
          (∀ j, pairGrading (sectorGrading S) realGrading (low + s + shift * K + 1) (v j) ≤ R) →
          |J.D k x v| ≤ A * T.H (T.sample m) ^ (3 / 4 : ℝ) *
            R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  classical
  let p := pairGrading (sectorGrading S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone S
  have hI : HasInterpolation p := hasInterpolation_of_hasSmoothing hp
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
  obtain ⟨B, hB⟩ := n04PositiveGeometry_rootInverseDefect_fixedBase_oneHigh_of_flow
    hT hS hN hflow
  choose ell hell using hB
  let L : ℕ → ℕ := fun k => 5 + ell k
  obtain ⟨low, hlow, hprefix⟩ := n04Realization_fixedBase_prefix_power
    p hp hI (max base B) L
  have hbase : base ≤ low := (le_max_left _ _).trans hlow
  have hBlow : B ≤ low := (le_max_right _ _).trans hlow
  refine ⟨low, hbase, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  refine ⟨shift, fun s => ?_⟩
  obtain ⟨A₀, hA₀, hinterp⟩ := hshift s
  let I : Type := Fin (K + 1) × Fin (s + 1)
  choose c hc hcb using fun i : I => hell i.1.val 1 zero_le_one (i.2.val + 5)
  let C₀ : ℝ := 1 + ∑ i : I, c i
  have hC₀ : 1 ≤ C₀ := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun i _ => hc i))
  have hcC (i : I) : c i ≤ C₀ :=
    (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨C₀ * A₀, one_le_mul_of_one_le_of_one_le hC₀ hA₀, ?_⟩
  intro k hk u hu b hb side m θ J x hx hxlow v hvlow R hR hxR hvR
  let i : I := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨u, Nat.lt_succ_of_le hu⟩)
  have hxB : p B x ≤ 1 := (hp hBlow x).trans hxlow
  have hraw := hcb i b hb side m θ J x hx hxB v
  change |J.D k x v| ≤ c i * T.H (T.sample m) ^ (3 / 4 : ℝ) *
    oneHighVariationWeight p B (u + 5 + ell k) x v at hraw
  have hH : 0 ≤ T.H (T.sample m) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg ((material_circle_sample_weights_pos hT hN.1.1).2 m).le _
  have hweight : oneHighVariationWeight p B (u + 5 + ell k) x v ≤
      oneHighVariationWeight p low (u + L k) x v :=
    oneHighVariationWeight_mono hp hBlow (by dsimp only [L]; omega) x v
  have hpower := hinterp k hk u hu x hxlow v hvlow R hR hxR hvR
  calc
    _ ≤ (c i * T.H (T.sample m) ^ (3 / 4 : ℝ)) *
        oneHighVariationWeight p low (u + L k) x v := hraw.trans
      (mul_le_mul_of_nonneg_left hweight (mul_nonneg (hc i) hH))
    _ ≤ (c i * T.H (T.sample m) ^ (3 / 4 : ℝ)) *
        (A₀ * R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hpower (mul_nonneg (hc i) hH)
    _ ≤ (C₀ * T.H (T.sample m) ^ (3 / 4 : ℝ)) *
        (A₀ * R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hcC i) hH)
        (mul_nonneg (zero_le_one.trans hA₀) (Real.rpow_nonneg (zero_le_one.trans hR) _))
    _ = _ := by ac_rfl

/-- The literal inverse slope has the same fixed low base. Its zeroth
parameter order includes the reference slope; every positive parameter
order retains the complete circle sample height factor. -/
theorem n04PositiveGeometry_rootInverseDerivative_fixedBase_prefix_of_flow
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
        ∀ k : ℕ, k ≤ K → ∀ d : ℕ, d ≤ 4 → ∀ u : ℕ, u ≤ s →
        ∀ side : Bool, ∀ m : ℕ, ∀ θ : ℝ,
        ∀ J : SmoothDirections (sectorNeighborhood S base ε ε) (fun x =>
          iteratedDeriv (u + d)
            (deriv (Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m side))) θ),
        ∀ x ∈ sectorNeighborhood S base ε ε,
          pairGrading (sectorGrading S) realGrading low x ≤ 1 →
        ∀ v : Fin k → (StateDirections S × ℝ),
          (∀ j, pairGrading (sectorGrading S) realGrading low (v j) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R →
          pairGrading (sectorGrading S) realGrading (low + s + shift * K + 1) x ≤ R →
          (∀ j, pairGrading (sectorGrading S) realGrading (low + s + shift * K + 1) (v j) ≤ R) →
          |J.D k x v| ≤ A * parameterHeightWeight (T.H (T.sample m) ^ (3 / 4 : ℝ)) k *
            R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  obtain ⟨low, hlow, hprefix⟩ :=
    n04PositiveGeometry_rootInverseDefect_fixedBase_prefix_of_flow hT hS hN hflow
  obtain ⟨RH, hRH, hheight⟩ := materialHeight_E0_weight_bounded hT
    (by norm_num : (0 : ℝ) < 3 / 4) 0
  have hHbound (m : ℕ) : T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ RH := by
    simpa only [Real.rpow_zero, mul_one] using
      hheight _ (materialSample_mem_interval hN.1.1 hT m)
  refine ⟨low, hlow, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  refine ⟨shift, fun s => ?_⟩
  obtain ⟨A, hA, hbound⟩ := hshift s
  let C₁ : ℝ := A * (RH + 1) + 1
  have hC₁ : 1 ≤ C₁ := le_add_of_nonneg_left
    (mul_nonneg (zero_le_one.trans hA) (by positivity))
  have hAC₁ : A ≤ C₁ := by dsimp only [C₁]; nlinarith only [hA, hRH]
  have hAHC₁ : A * RH + 1 ≤ C₁ := by dsimp only [C₁]; nlinarith only [hA]
  refine ⟨C₁, hC₁, ?_⟩
  intro k hk d hd u hu side m θ J x hx hxlow v hvlow R hR hxR hvR
  let JD := n04PositiveGeometry_rootInverseDefect_angularDirections
    hT hS hN side m (u + d + 1) θ
  have hb := hbound k hk u hu (u + d + 1) (by omega)
    side m θ JD x hx hxlow v hvlow R hR hxR hvR
  let P : ℝ := R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))
  have hP : 0 ≤ P := Real.rpow_nonneg (zero_le_one.trans hR) _
  have hPone : 1 ≤ P := Real.one_le_rpow hR (div_nonneg (Nat.cast_nonneg _) (by positivity))
  have hH : 0 ≤ T.H (T.sample m) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg ((material_circle_sample_weights_pos hT hN.1.1).2 m).le _
  by_cases hkzero : k = 0
  · subst k
    have heq : J.D 0 x v = JD.D 0 x v + (if u + d = 0 then 1 else 0) :=
      (smoothDirections_D_zero_apply J hx v).trans
        ((n04PositiveGeometry_rootInverseDerivative_angular_eq hT hS hN hx side m (u + d) θ).trans
          (congrArg (fun t : ℝ => t + (if u + d = 0 then 1 else 0))
            (smoothDirections_D_zero_apply JD hx v).symm))
    have hconstant : |(if u + d = 0 then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    have hfinal : |J.D 0 x v| ≤ C₁ * P := calc
      _ ≤ |JD.D 0 x v| + |(if u + d = 0 then (1 : ℝ) else 0)| :=
        (congrArg abs heq).trans_le (abs_add_le _ _)
      _ ≤ A * T.H (T.sample m) ^ (3 / 4 : ℝ) * P + 1 := add_le_add hb hconstant
      _ ≤ A * RH * P + P := add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hHbound m) (zero_le_one.trans hA)) hP) hPone
      _ = (A * RH + 1) * P := by rw [add_mul, one_mul]
      _ ≤ C₁ * P := mul_le_mul_of_nonneg_right hAHC₁ hP
    simpa only [parameterHeightWeight, if_pos rfl, mul_one] using hfinal
  · have hjet := n04PositiveGeometry_rootInverseDerivative_positive_jet_eq
      hT hS hN side m (u + d) θ J JD (Nat.pos_of_ne_zero hkzero) hx v
    have hfinal : |J.D k x v| ≤ C₁ * T.H (T.sample m) ^ (3 / 4 : ℝ) * P :=
      ((congrArg abs hjet).trans_le hb).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC₁ hH) hP)
    simpa only [parameterHeightWeight, if_neg hkzero] using hfinal

/-- N01 chooses one common neighborhood before all parameter orders.
Both actual source slopes then satisfy the normalized finite intrinsic
prefix at the supplied positive midpoint sample, with its full `3/4`
height gain at every positive parameter order. -/
theorem n04PositiveGeometry_rootInverseDerivative_fixedBase_samplePrefix
    (W : N04RealizationStart) (X : N04RealizationChoice W) :
    ∃ newBase : ℕ, ∃ ε' : ℝ,
      W.base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ W.ε ∧
      ∃ low : ℕ, newBase ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
        ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
          ∀ k : ℕ, k ≤ K → ∀ d : ℕ, d ≤ 4 → ∀ u : ℕ, u ≤ s →
          ∀ i side m, (X.src i side).val = some m → ∀ θ : ℝ,
          ∀ J : SmoothDirections (sectorNeighborhood W.S newBase ε' ε') (fun x =>
            iteratedDeriv (u + d)
              (deriv (Function.invFun
                (n01RootLabel W.S W.C (liftSectorParameter W.S W.C x) m (!side)))) θ),
          ∀ x ∈ sectorNeighborhood W.S newBase ε' ε',
            pairGrading (sectorGrading W.S) realGrading low x ≤ 1 →
          ∀ v : Fin k → (StateDirections W.S × ℝ),
            (∀ j, pairGrading (sectorGrading W.S) realGrading low (v j) ≤ 1) →
          ∀ R : ℝ, 1 ≤ R →
            pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) x ≤ R →
            (∀ j, pairGrading (sectorGrading W.S) realGrading
              (low + s + shift * K + 1) (v j) ≤ R) →
            |J.D k x v| ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
              parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) k *
              R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  obtain ⟨newBase, ε', hb, hε, hεW, hflow⟩ :=
    exists_ordinaryFlowJacobianBounds_of_n01 W.hT W.through03.1.1
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  obtain ⟨low, hlow, hprefix⟩ :=
    n04PositiveGeometry_rootInverseDerivative_fixedBase_prefix_of_flow W.hT W.hS hN hflow
  refine ⟨newBase, ε', hb, hε, hεW, low, hlow, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  refine ⟨shift, fun s => ?_⟩
  obtain ⟨A, hA, hbound⟩ := hshift s
  obtain ⟨B, hB, hsample⟩ :=
    n04PositiveGeometry_positiveSource_circle_parameter_weight W X (3 / 4 : ℝ)
      (A := 0) (C := A) (by norm_num) (zero_le_one.trans hA)
  refine ⟨B, hB, ?_⟩
  intro k hk d hd u hu i side m hm θ J x hx hxlow v hvlow R hR hxR hvR
  have hj := hbound k hk d hd u hu (!side) m θ J x hx hxlow v hvlow R hR hxR hvR
  have hcost : A * parameterHeightWeight (W.T.H (W.T.sample m) ^ (3 / 4 : ℝ)) k ≤
      B * W.U.E0 (W.U.sample (X.cell i)) ^ B *
        parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) k := by
    simpa only [Real.rpow_zero, mul_one] using hsample i side m hm k
  exact hj.trans (mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg (zero_le_one.trans hR) _))

end ContinuousFlexibility.Analysis
