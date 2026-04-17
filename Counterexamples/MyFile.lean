import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Positive
import Counterexamples.SingularValueDecomposition

open scoped BigOperators

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
-- variable [CompleteSpace E]
variable (U V : Submodule ℂ E)

variable (ι : Type*) [Fintype ι] (BU : OrthonormalBasis ι ℂ U)

#check BU.orthogonalProjection_apply_eq_sum
#check U.orthogonalProjection
#check U.subtypeL

open InnerProductSpace

noncomputable abbrev proj (U : Submodule ℂ E) := U.starProjection

noncomputable abbrev SubspaceSimilarity (U V : Submodule ℂ E) : ℝ :=
 (LinearMap.trace ℂ E ((proj U).comp (proj V))).re

local notation "⟪" U "; " V "⟫" => SubspaceSimilarity U V
local notation "⟪" x ", " y "⟫" => inner ℂ x y

lemma proj_to_linearmap :
 (proj U).toLinearMap = U.subtype.comp U.orthogonalProjection.toLinearMap := rfl

lemma proj_isSymmetricProjection (U : Submodule ℂ E) : (proj U).IsSymmetricProjection := by
  exact Submodule.isSymmetricProjection_starProjection U

lemma proj_apply_of_basis {ι : Type*} [Fintype ι] {U : Submodule ℂ E}
 (B : OrthonormalBasis ι ℂ U) (v : E) :
    proj U v = ∑ i, ⟪(B i : E), v⟫ • B i := by
  simp only [proj, Submodule.starProjection, ContinuousLinearMap.coe_comp', Submodule.coe_subtypeL',
    Submodule.coe_subtype, Function.comp_apply, B.orthogonalProjection_apply_eq_sum v,
    AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]

lemma proj_of_basis {ι : Type*} [Fintype ι] {U : Submodule ℂ E}
 (B : OrthonormalBasis ι ℂ U) :
    proj U = ∑ i, InnerProductSpace.rankOne ℂ (B i : E) (B i : E) := by
  ext x
  simp only [proj_apply_of_basis B _, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, InnerProductSpace.rankOne_apply]

lemma SubspaceSimilarity_symm (U V : Submodule ℂ E) : ⟪U; V⟫ = ⟪V; U⟫ := by
  rw [SubspaceSimilarity, SubspaceSimilarity, ContinuousLinearMap.coe_comp,
   ContinuousLinearMap.coe_comp, LinearMap.trace_comp_comm']

omit [FiniteDimensional ℂ E] in
lemma comp_sum {ι : Type*} [Fintype ι] (f : E →L[ℂ] E) (g : ι → E →L[ℂ] E) :
    f.comp (∑ i, g i) = ∑ i, f.comp (g i) := by
  ext x
  simp only [ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_sum', Function.comp_apply,
    Finset.sum_apply, map_sum]

omit [FiniteDimensional ℂ E] in
lemma sum_comp {ι : Type*} [Fintype ι] (f : E →L[ℂ] E) (g : ι → E →L[ℂ] E) :
    (∑ i, g i).comp f = ∑ i, (g i).comp f := by
  ext x
  simp only [ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_sum', Function.comp_apply,
    Finset.sum_apply]

lemma proj_comp_proj_of_bases {ι κ : Type*} [Fintype ι] [Fintype κ] {U V : Submodule ℂ E}
  (BU : OrthonormalBasis ι ℂ U) (BV : OrthonormalBasis κ ℂ V) :
    (proj U).comp (proj V) = ∑ i, ∑ j, ⟪(BU j : E), BV i⟫ • rankOne ℂ (BU j : E) (BV i : E) := by
  simp only [proj_of_basis BU, proj_of_basis BV, comp_sum, sum_comp, rankOne_comp_rankOne]

example {u v : E} (U : Submodule ℂ E) :
    (proj U).comp (rankOne ℂ u v) = rankOne ℂ (proj U u) v := comp_rankOne u v (proj U)

lemma inner_proj_eq_of_mem_left (u v : E) (hu : u ∈ U) : ⟪u, v⟫ = ⟪u, proj U v⟫ := by
  change ⟪u, v⟫ = inner ℂ ⟨u, hu⟩ (U.orthogonalProjection v)
  rw [Submodule.inner_orthogonalProjection_eq_of_mem_left]

lemma SubspaceSimilarity_of_basis' {κ : Type*} [Fintype κ] {U V : Submodule ℂ E}
 (BV : OrthonormalBasis κ ℂ V) :
    LinearMap.trace ℂ E ((proj U).comp (proj V)) = ∑ i, ‖proj U (BV i)‖^2 := by
  rw [proj_of_basis BV, comp_sum, ContinuousLinearMap.coe_sum]
  simp only [comp_rankOne, map_sum, trace_rankOne]
  push_cast
  refine Fintype.sum_congr _ _ fun i ↦ ?_
  rw [← Submodule.inner_starProjection_left_eq_right,
   inner_proj_eq_of_mem_left U _ _ (Submodule.starProjection_apply_mem U ↑(BV i))]
  simp only [inner_self_eq_norm_sq_to_K, Complex.coe_algebraMap]

lemma SubspaceSimilarity_of_basis {κ : Type*} [Fintype κ] {U V : Submodule ℂ E}
  (BV : OrthonormalBasis κ ℂ V) : ⟪U; V⟫ = ∑ i, ‖proj U (BV i)‖^2 := by
  rw [SubspaceSimilarity, SubspaceSimilarity_of_basis' BV, Complex.ofReal_re]

lemma SubspaceSimilarity_of_bases {ι κ : Type*} [Fintype ι] [Fintype κ] {U V : Submodule ℂ E}
  (BU : OrthonormalBasis ι ℂ U) (BV : OrthonormalBasis κ ℂ V) :
    ⟪U; V⟫ = ∑ i, ∑ j, ‖⟪(BU j : E), BV i⟫‖^2 := by
  rw [SubspaceSimilarity_of_basis BV]
  refine Fintype.sum_congr _ _ fun i ↦ ?_
  change ‖U.orthogonalProjection (BV i)‖ ^ 2 = ∑ j, ‖⟪(BU j : E), BV i⟫‖ ^ 2
  simp only [← BU.sum_sq_norm_inner_right, Submodule.inner_orthogonalProjection_eq_of_mem_left]

-- #check InnerProductSpace.gramSchmidtOrthonormalBasis

-- lemma B1_basisAux_helper {u₁ u₂ : E} (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1) (h : ‖⟪u₁, u₂⟫‖ < 1) :
--     Module.finrank ℂ (Submodule.span ℂ {u₁, u₂}) = Fintype.card (Fin 2) := by
--   sorry

-- noncomputable def B1_basisAux {u₁ u₂ : E} (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1) (h : ‖⟪u₁, u₂⟫‖ < 1) :
--     OrthonormalBasis (Fin 2) ℂ (Submodule.span ℂ {u₁, u₂}) := by
--   refine _root_.Module.Basis.toOrthonormalBasis ?_ ?_
--   · apply?
--   refine InnerProductSpace.gramSchmidtOrthonormalBasis (B1_basisAux_helper hu₁ hu₂ h)
--    (![⟨u₁, Submodule.mem_span_of_mem (by simp)⟩, ⟨u₂, Submodule.mem_span_of_mem (by simp)⟩])

-- lemma B1_basisAux_def {u₁ u₂ : E} (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1) (h : ‖⟪u₁, u₂⟫‖ < 1) :
--     B1_basisAux hu₁ hu₂ h 0 = u₁ := by
--   simp [B1_basisAux, InnerProductSpace.gramSchmidtOrthonormalBasis, InnerProductSpace.gramSchmidtNormed]

lemma B1 (V : Submodule ℂ E) (u₁ u₂ : E) (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1) (h : ‖⟪u₁, u₂⟫‖ < 1) :
    ⟪Submodule.span ℂ {u₁, u₂}; V⟫ = (‖proj V u₁‖^2 + ‖proj V u₂‖^2
     - 2 * (⟪u₁, u₂⟫ * ⟪proj V u₁, proj V u₂⟫).re) / (1 - ‖⟪u₁, u₂⟫‖^2) := by
  sorry


noncomputable abbrev SubspaceFlag {n : ℕ} {U : Submodule ℂ E}
  (B : OrthonormalBasis (Fin n) ℂ U) (k : ℕ) : Submodule ℂ E :=
    Submodule.span ℂ ({i | i.val < k}.image (U.subtype ∘ ⇑B))

noncomputable abbrev SubspaceFlag' {n : ℕ} (B : OrthonormalBasis (Fin n) ℂ E) (k : ℕ) :
  Submodule ℂ E := Submodule.span ℂ ({i | i.val < k}.image B)

-- noncomputable def EigenFlag_basis {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (k : ℕ) :=
-- (SubspaceFlag (hT.eigenvectorBasis rfl) )


noncomputable def principal_map (U V : Submodule ℂ E) : U →L[ℂ] V :=
  V.orthogonalProjection ∘L U.subtypeL

#check principal_map U V

noncomputable abbrev principal_vectors_left {n : ℕ} (U V : Submodule ℂ E) (hU : IsClosed (U : Set E))
    (hn : Module.finrank ℂ U = n) : OrthonormalBasis (Fin n) ℂ U := by
  exact SVD_basis_left hn (principal_map U V)

noncomputable def principal_vectors_right {n m : ℕ} (U V : Submodule ℂ E)
    (h : Module.finrank ℂ U = n) (h : Module.finrank ℂ V = m) : OrthonormalBasis (Fin n) ℂ V :=
  SVD_basis_right hn hm (principal_map U V)

-- noncomputable abbrev principal_spaces {n : ℕ} (U V : Submodule ℂ E)
--     (h : Module.finrank ℂ V = n) : OrthonormalBasis (Fin n) ℂ V :=
--   (principal_map_symmteric U V).eigenvectorBasis h

noncomputable abbrev principal_vectors_left {n : ℕ} (U V : Submodule ℂ E)
    (h : Module.finrank ℂ U = n) : OrthonormalBasis (Fin n) ℂ U := by
  sorry


lemma test_angles {n : ℕ} (U V : Submodule ℂ E) (h : Module.finrank ℂ V = n) :
  Pairwise (fun i j ↦ ⟪(U.starProjection ∘L V.subtypeL) (principal_vectors_right U V h i),
  (U.starProjection ∘L V.subtypeL) (principal_vectors_right U V h j)⟫ = 0) := by
  intro i j hij
  simp only [ContinuousLinearMap.coe_comp', Submodule.coe_subtypeL', Submodule.coe_subtype,
    Function.comp_apply, Submodule.inner_starProjection_left_eq_right]
  change ⟪↑(principal_vectors_right U V h i), ((U.starProjection ∘L U.starProjection) ∘L V.subtypeL)
   (principal_vectors_right U V h j)⟫ = 0
  rw [Submodule.starProjection_comp_starProjection_of_le fun _ a ↦ a,
   ← V.inner_orthogonalProjection_eq_of_mem_left]
  change ⟪principal_vectors_right U V h i,
   (principal_map U V).toLinearMap (principal_vectors_right U V h j)⟫ = 0
  rw [(principal_map_symmteric U V).apply_eigenvectorBasis, inner_smul_right]
  simp only [Complex.coe_algebraMap, Submodule.coe_inner, mul_eq_zero, Complex.ofReal_eq_zero]
  right
  exact (principal_vectors_right U V h).inner_eq_zero  hij

noncomputable abbrev X_op (U V : Submodule ℂ E) (a b : ℝ) : E →L[ℂ] E := a • (proj U) + b • (proj V)

lemma X_op_symm (U V : Submodule ℂ E) (a b : ℝ) : (X_op U V a b).IsSymmetric := by
  sorry

noncomputable abbrev Z (a b : ℝ) {N : ℕ} (hN : Module.finrank ℂ E = N) :=
 fun k ↦ SubspaceFlag' ((X_op_symm U V a b).eigenvectorBasis hN) k

noncomputable abbrev EV (a b : ℝ) {N : ℕ} (hN : Module.finrank ℂ E = N) := ((X_op_symm U V a b).eigenvalues hN)

theorem B3 (U V W : Submodule ℂ E) (dU dV dWU dWV k N : ℕ) (a b ε : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hN : Module.finrank ℂ E = N)
  (hε : ε > 0) (hk : k ≤ dU ⊓ dV) (hW : W = (W ⊓ U) ⊔ (W ⊓ V)) (hdU : dU = Module.finrank ℂ U) (hdV : dV = Module.finrank ℂ V)
  (hdWU : Module.finrank ℂ (W ⊓ U) = dWU) (hdWV : dWV = Module.finrank ℂ (W ⊓ V))
  (hEV : EV U V a b hN ⟨k, sorry⟩ - a ≥ (dWU ⊔ dWV)/(2 * ε) * ‖a-b‖) :
    ⟪W; Z U V a b k⟫ + ⟪W; Z U V a b (dU + dV - k)⟫ ≥ dWU + dWV - ε := by
