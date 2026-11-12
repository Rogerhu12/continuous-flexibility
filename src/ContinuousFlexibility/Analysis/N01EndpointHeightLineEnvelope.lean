import ContinuousFlexibility.Analysis.N01EndpointStateEnvelope
import ContinuousFlexibility.Analysis.SolveNormalization

/-!
# Fixed physical energies along an actual affine height line

The scalar derivative contains the full base height. Two fixed physical
localizations, one for the base height and one for the direction, give
a summable envelope for the whole parameter segment. No moving input
energy is substituted for a uniform envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointHeightLineEnvelopeStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators ContDiff

private theorem heightLine_linear_affine_apply
    {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] (ι → ℝ)) (u v : E) (t : ℝ) (i : ι) :
    L (u + t • v) i = L u i + t * L v i := by
  exact (congrArg (fun f : ι → ℝ => f i) (L.map_add u (t • v))).trans
    (congrArg (fun f : ι → ℝ => L u i + f i) (L.map_smul t v))

theorem heightPairField_affine_apply (S : PhysicalSpacesData)
    (ξ η : HeightPair S) (t : ℝ) (p : PolarPoint) :
    heightPairField S (ξ + t • η) p = heightPairField S ξ p + t * heightPairField S η p := by
  exact heightLine_linear_affine_apply (heightPairFieldLinear S) ξ η t p

theorem liftSectorParameter_height_field_line (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (x w : StateDirections S × ℝ) (t : ℝ) (p : PolarPoint) :
    stateU S (liftSectorParameter S C (x + t • w)).1 p =
      heightPairField S (liftSectorParameter S C x).1.1 p +
        t * heightPairField S w.1.val.1 p := by
  have heq : (liftSectorParameter S C (x + t • w)).1.1 =
      (liftSectorParameter S C x).1.1 + t • w.1.val.1 := by
    change C.referenceState.1 + (x.1.val.1 + t • w.1.val.1) =
      (C.referenceState.1 + x.1.val.1) + t • w.1.val.1
    exact (add_assoc _ _ _).symm
  exact (congrArg (fun ξ : HeightPair S => heightPairField S ξ p) heq).trans
    (heightPairField_affine_apply S (liftSectorParameter S C x).1.1 w.1.val.1 t p)

private theorem affine_additive_constants (u v a b t : ℝ) :
    (u + a) + t * (v + b) = (u + t * v) + (a + t * b) := by ring

private theorem heightLine_sqrt_scaled_energy (q : ℝ) (e : ℝ≥0∞) (hq : 0 ≤ q) :
    Real.sqrt (ENNReal.ofReal (q ^ 2) * e).toReal = q * Real.sqrt e.toReal := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg q),
    Real.sqrt_mul (sq_nonneg q), Real.sqrt_sq hq]

private theorem heightLine_factor_reorder (K q A u v : ℝ) :
    K * q * (A * u + v) = K * (A * (q * u) + q * v) := by ring

private theorem heightLine_finish_reorder (K A e : ℝ) :
    K * (A * (2 * e) + 2 * e) = (2 * K * (A + 1)) * e := by ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.endpointFlow_pure_scalar_line_energy_envelope
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n s : ℕ) (x w : StateDirections S × ℝ) :
    ∃ E : ℕ → ℝ≥0∞, ∃ K : ℝ, (∑' m, E m) < ⊤ ∧ 0 ≤ K ∧
      ∀ t : ℝ, |t| ≤ 1 → x + t • w ∈ sectorNeighborhood S base ε ε →
      ∀ m b c, b + c ≤ s → ∀ θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) (x + t • w)
          (fun _ => scalarParameterDirection S) m) θ| ≤ K * Real.sqrt (E m).toReal := by
  let ξ₀ : HeightPair S := (liftSectorParameter S C x).1.1
  let ξ₁ : HeightPair S := w.1.val.1
  let data₀ := hN.exists_height_pair_plateau_directions hS hT ξ₀
  let η₀ : ℕ → HeightPair S := data₀.choose
  have hlocal₀ := data₀.choose_spec.2.2.1
  have henergy₀ := data₀.choose_spec.2.2.2
  let data₁ := hN.exists_height_pair_plateau_directions hS hT ξ₁
  let η₁ : ℕ → HeightPair S := data₁.choose
  have hlocal₁ := data₁.choose_spec.2.2.1
  have henergy₁ := data₁.choose_spec.2.2.2
  let j : ℕ := max base (s + hN.ordinaryFlowLoss (n + 2))
  let p := pairGrading (sectorGrading S) realGrading
  let E₀ : ℕ → ℝ≥0∞ := fun m =>
    ENNReal.ofReal ((T.M (T.sample m) ^ (s + 1)) ^ 2) *
      physicalPlateauEnergy D T C (3 / 4 : ℝ) j ((S.height (3 / 4 : ℝ)).decode ξ₀.1) m
  let E₁ : ℕ → ℝ≥0∞ := fun m =>
    ENNReal.ofReal ((T.M (T.sample m) ^ (s + 1)) ^ 2) *
      physicalPlateauEnergy D T C (3 / 4 : ℝ) j ((S.height (3 / 4 : ℝ)).decode ξ₁.1) m
  let E : ℕ → ℝ≥0∞ := fun m => E₀ m + E₁ m
  have hE₀ : (∑' m, E₀ m) < ⊤ :=
    hN.physicalPlateauEnergy_weighted_tsum_lt_top hS hT (hS.1 (3 / 4 : ℝ)) ξ₀.1 j (s + 1)
  have hE₁ : (∑' m, E₁ m) < ⊤ :=
    hN.physicalPlateauEnergy_weighted_tsum_lt_top hS hT (hS.1 (3 / 4 : ℝ)) ξ₁.1 j (s + 1)
  have hE : (∑' m, E m) < ⊤ :=
    (ENNReal.tsum_add (f := E₀) (g := E₁)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hE₀, hE₁⟩)
  let pointData := hN.endpointFlow_pure_scalar_weighted_height_bound hS hT rsel hrsel n s
  let K : ℝ := pointData.choose
  have hK : 0 < K := pointData.choose_spec.1
  have hpoint := pointData.choose_spec.2
  let A : ℝ := (n : ℝ) + 2 + (p j x + p j w)
  have hA : 0 ≤ A := add_nonneg (by positivity)
    (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  refine ⟨E, 2 * K * (A + 1), hE,
    mul_nonneg (mul_nonneg (by norm_num) hK.le) (add_nonneg hA zero_le_one), ?_⟩
  intro t ht hz m b c hbc θ
  let η : HeightPair S := η₀ m + t • η₁ m
  have hlocal : ∃ a : ℝ, ∀ r ∈ Ioo (C.left m) (C.right m), ∀ ψ,
      heightPairField S η (r, ψ) = stateU S (liftSectorParameter S C (x + t • w)).1 (r, ψ) + a := by
    let localData₀ := hlocal₀ m
    let a₀ : ℝ := localData₀.choose
    let localData₁ := hlocal₁ m
    let a₁ : ℝ := localData₁.choose
    refine ⟨a₀ + t * a₁, ?_⟩
    intro r hr ψ
    have heq := heightPairField_affine_apply S (η₀ m) (η₁ m) t (r, ψ)
    have hsum := congrArg₂ (fun a b : ℝ => a + t * b)
      (localData₀.choose_spec r hr ψ) (localData₁.choose_spec r hr ψ)
    have halg := affine_additive_constants
      (heightPairField S ξ₀ (r, ψ)) (heightPairField S ξ₁ (r, ψ)) a₀ a₁ t
    exact heq.trans (hsum.trans (halg.trans
      (congrArg (fun a : ℝ => a + (a₀ + t * a₁))
        (liftSectorParameter_height_field_line S C x w t (r, ψ)).symm)))
  have hM : 1 ≤ T.M (T.sample m) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m)).2.2.2
  have hM0 : 0 ≤ T.M (T.sample m) := zero_le_one.trans hM
  have hefinite : E m < ⊤ := (ENNReal.le_tsum (f := E) m).trans_lt hE
  have he₀ : Real.sqrt (E₀ m).toReal ≤ Real.sqrt (E m).toReal :=
    Real.sqrt_le_sqrt (ENNReal.toReal_mono hefinite.ne (le_add_of_nonneg_right zero_le))
  have he₁ : Real.sqrt (E₁ m).toReal ≤ Real.sqrt (E m).toReal :=
    Real.sqrt_le_sqrt (ENNReal.toReal_mono hefinite.ne (le_add_of_nonneg_left zero_le))
  have hsqrt₀ : Real.sqrt (E₀ m).toReal = T.M (T.sample m) ^ (s + 1) *
      Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) j
        ((S.height (3 / 4 : ℝ)).decode ξ₀.1) m).toReal :=
    heightLine_sqrt_scaled_energy (T.M (T.sample m) ^ (s + 1))
      (physicalPlateauEnergy D T C (3 / 4 : ℝ) j
        ((S.height (3 / 4 : ℝ)).decode ξ₀.1) m) (pow_nonneg hM0 _)
  have hsqrt₁ : Real.sqrt (E₁ m).toReal = T.M (T.sample m) ^ (s + 1) *
      Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) j
        ((S.height (3 / 4 : ℝ)).decode ξ₁.1) m).toReal :=
    heightLine_sqrt_scaled_energy (T.M (T.sample m) ^ (s + 1))
      (physicalPlateauEnergy D T C (3 / 4 : ℝ) j
        ((S.height (3 / 4 : ℝ)).decode ξ₁.1) m) (pow_nonneg hM0 _)
  have hmono : Monotone (heightPairGrading S) := pairGrading_monotone
    (gradedSeminorm_monotone (fun a => (S.height (3 / 4 : ℝ)).level a)
      (S.height (3 / 4 : ℝ)).bond) (fun _ _ _ _ => le_rfl)
  have hheight (a : ℕ) (ha : a ≤ j) :
      T.M (T.sample m) ^ (c + 1) * heightPairGrading S a η ≤
        2 * Real.sqrt (E m).toReal := by
    have hnorm : heightPairGrading S a η ≤
        Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) j
          ((S.height (3 / 4 : ℝ)).decode ξ₀.1) m).toReal +
        Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) j
          ((S.height (3 / 4 : ℝ)).decode ξ₁.1) m).toReal :=
      (seminorm_line_le_of_abs_le_one (heightPairGrading S a) (η₀ m) (η₁ m) ht).trans
        (add_le_add ((hmono ha (η₀ m)).trans ((henergy₀ j).2 m))
          ((hmono ha (η₁ m)).trans ((henergy₁ j).2 m)))
    calc
      _ ≤ T.M (T.sample m) ^ (s + 1) * heightPairGrading S a η :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM (by omega)) (apply_nonneg _ _)
      _ ≤ T.M (T.sample m) ^ (s + 1) *
          (Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) j
            ((S.height (3 / 4 : ℝ)).decode ξ₀.1) m).toReal +
          Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) j
            ((S.height (3 / 4 : ℝ)).decode ξ₁.1) m).toReal) :=
        mul_le_mul_of_nonneg_left hnorm (pow_nonneg hM0 _)
      _ = Real.sqrt (E₀ m).toReal + Real.sqrt (E₁ m).toReal :=
        (mul_add _ _ _).trans (congrArg₂ (fun u v : ℝ => u + v) hsqrt₀.symm hsqrt₁.symm)
      _ ≤ 2 * Real.sqrt (E m).toReal :=
        (add_le_add he₀ he₁).trans_eq (two_mul (Real.sqrt (E m).toReal)).symm
  have hbase := hheight base (le_max_left _ _)
  have hhigh := hheight (s + hN.ordinaryFlowLoss (n + 2)) (le_max_right _ _)
  have hgrade : p (s + hN.ordinaryFlowLoss (n + 2)) (x + t • w) ≤ p j x + p j w :=
    (sectorPairGrading_monotone S (show s + hN.ordinaryFlowLoss (n + 2) ≤ j from le_max_right _ _) (x + t • w)).trans
      (seminorm_line_le_of_abs_le_one (p j) x w ht)
  have hcoeff : (n : ℝ) + 2 + p (s + hN.ordinaryFlowLoss (n + 2)) (x + t • w) ≤ A :=
    add_le_add (le_refl _) hgrade
  have hp := hpoint m b c θ (by omega) (x + t • w) hz η hlocal
  calc
    _ ≤ K * T.M (T.sample m) ^ (c + 1) *
        (((n : ℝ) + 2 + p (s + hN.ordinaryFlowLoss (n + 2)) (x + t • w)) * heightPairGrading S base η +
          heightPairGrading S (s + hN.ordinaryFlowLoss (n + 2)) η) := hp
    _ ≤ K * T.M (T.sample m) ^ (c + 1) *
        (A * heightPairGrading S base η + heightPairGrading S (s + hN.ordinaryFlowLoss (n + 2)) η) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right hcoeff (apply_nonneg _ _)) (le_refl _))
        (mul_nonneg hK.le (pow_nonneg hM0 _))
    _ = K * (A * (T.M (T.sample m) ^ (c + 1) * heightPairGrading S base η) +
        T.M (T.sample m) ^ (c + 1) * heightPairGrading S (s + hN.ordinaryFlowLoss (n + 2)) η) :=
      heightLine_factor_reorder K (T.M (T.sample m) ^ (c + 1)) A
        (heightPairGrading S base η) (heightPairGrading S (s + hN.ordinaryFlowLoss (n + 2)) η)
    _ ≤ K * (A * (2 * Real.sqrt (E m).toReal) + 2 * Real.sqrt (E m).toReal) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hbase hA) hhigh) hK.le
    _ = _ := heightLine_finish_reorder K A (Real.sqrt (E m).toReal)

end ContinuousFlexibility.Statements
