import Mathmatica.SATDecimation

/-!
# 命题归结反驳完备性定理与 2-SAT 实空间重整化封闭性

本模块基于 [SATDecimation.lean] 中的实空间重整化算子 `decimateVar`，形式化并证明两个
Mathlib 当前空白的核心定理：
1. **Davis-Putnam 归结反驳完备性定理**（`dp_refutation_complete`）：
   将所有 `n` 个变量依次重整化抽取后得到 `decimateAll n φ`，则：
   $$\neg \mathrm{Satisfiable}\,\varphi \iff [] \in \mathrm{decimateAll}\,n\,\varphi$$
   （即原公式不可满足，当且仅当重整化流最终归结出空子句 `[]`）。
2. **2-SAT 实空间重整化封闭性定理**（`decimateVar_preserves_2sat`）：
   若 `φ` 是 2-SAT 公式（所有子句宽度 `≤ 2`），则对任意变量 `v` 执行 `decimateVar v φ` 后，
   所得有效公式依然是 2-SAT 公式（所有子句宽度 `≤ 2`）。
-/

namespace Mathmatica.ResolutionCompleteness

open Mathmatica.SAT
open Mathmatica.SATDecimation

/-! ## 第一部分：变量消除性质与反驳完备性定理 -/

/-- 辅助引理：若 `c ∈ decimateVar v φ`，则 `c` 中不再包含变量 `v`。 -/
lemma decimateVar_no_var {n : ℕ} (v : Fin n) (φ : CNF n) :
    ∀ c ∈ decimateVar v φ, ∀ l ∈ c, l.var ≠ v := by
  intro c hc l hl hvar
  unfold decimateVar at hc
  rw [List.mem_append] at hc
  rcases hc with hrest | hres
  · unfold restClauses at hrest
    rw [List.mem_filter] at hrest
    have hcond := hrest.2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    cases hp : l.pol
    · have hhas : hasLit c v false = true := by
        unfold hasLit; rw [List.any_eq_true]; exact ⟨l, hl, by simp [hvar, hp]⟩
      rw [hhas] at hcond
      exact Bool.false_ne_true hcond.2.symm
    · have hhas : hasLit c v true = true := by
        unfold hasLit; rw [List.any_eq_true]; exact ⟨l, hl, by simp [hvar, hp]⟩
      rw [hhas] at hcond
      exact Bool.false_ne_true hcond.1.symm
  · unfold resolvents at hres
    rw [List.mem_flatMap] at hres
    rcases hres with ⟨p, hp, hqmem⟩
    rw [List.mem_map] at hqmem
    rcases hqmem with ⟨q, hq, rfl⟩
    rw [List.mem_append] at hl
    rcases hl with hlp | hlq
    · unfold posClauses at hp
      rw [List.mem_map] at hp
      rcases hp with ⟨c1, _, rfl⟩
      unfold stripVar at hlp
      rw [List.mem_filter] at hlp
      exact (bne_iff_ne.mp hlp.2) hvar
    · unfold negClauses at hq
      rw [List.mem_map] at hq
      rcases hq with ⟨c2, _, rfl⟩
      unfold stripVar at hlq
      rw [List.mem_filter] at hlq
      exact (bne_iff_ne.mp hlq.2) hvar

/-- 辅助引理：如果公式 `φ` 原本就不含变量 `u`，那么对另一个变量 `v` 执行 `decimateVar v φ` 后，
所得公式依然不含变量 `u`。 -/
lemma decimateVar_preserves_no_var {n : ℕ} (v u : Fin n) (φ : CNF n)
    (hno : ∀ c ∈ φ, ∀ l ∈ c, l.var ≠ u) :
    ∀ c ∈ decimateVar v φ, ∀ l ∈ c, l.var ≠ u := by
  intro c hc l hl
  unfold decimateVar at hc
  rw [List.mem_append] at hc
  rcases hc with hrest | hres
  · unfold restClauses at hrest
    rw [List.mem_filter] at hrest
    exact hno c hrest.1 l hl
  · unfold resolvents at hres
    rw [List.mem_flatMap] at hres
    rcases hres with ⟨p, hp, hqmem⟩
    rw [List.mem_map] at hqmem
    rcases hqmem with ⟨q, hq, rfl⟩
    rw [List.mem_append] at hl
    rcases hl with hlp | hlq
    · unfold posClauses at hp
      rw [List.mem_map] at hp
      rcases hp with ⟨c1, hc1, rfl⟩
      rw [List.mem_filter] at hc1
      unfold stripVar at hlp
      rw [List.mem_filter] at hlp
      exact hno c1 hc1.1 l hlp.1
    · unfold negClauses at hq
      rw [List.mem_map] at hq
      rcases hq with ⟨c2, hc2, rfl⟩
      rw [List.mem_filter] at hc2
      unfold stripVar at hlq
      rw [List.mem_filter] at hlq
      exact hno c2 hc2.1 l hlq.1

/-- 辅助引理：经过 `decimateList vs φ` 后，列表 `vs` 中出现的所有变量都被完全消去。 -/
lemma decimateList_no_vars {n : ℕ} (vs : List (Fin n)) (φ : CNF n) :
    ∀ c ∈ decimateList vs φ, ∀ l ∈ c, l.var ∉ vs := by
  induction vs generalizing φ with
  | nil =>
    intro _ _ _ _ hmem
    exact List.not_mem_nil hmem
  | cons v vs ih =>
    intro c hc l hl hmem
    simp only [decimateList] at hc
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · -- 变量 v 在第一步已被消去，后续所有抽取步骤均保持不含 v
      have h1 : ∀ c' ∈ decimateVar l.var φ, ∀ l' ∈ c', l'.var ≠ l.var :=
        decimateVar_no_var l.var φ
      have hpres : ∀ (ws : List (Fin n)) (ψ : CNF n),
          (∀ c' ∈ ψ, ∀ l' ∈ c', l'.var ≠ l.var) →
          ∀ c' ∈ decimateList ws ψ, ∀ l' ∈ c', l'.var ≠ l.var := by
        intro ws
        induction ws with
        | nil => intro ψ hψ; exact hψ
        | cons w ws ihw =>
          intro ψ hψ
          simp only [decimateList]
          exact ihw (decimateVar w ψ) (decimateVar_preserves_no_var w l.var ψ hψ)
      exact hpres vs (decimateVar l.var φ) h1 c hc l hl rfl
    · exact ih (decimateVar v φ) c hc l hl htail

/-- 依次消去全部 `n` 个变量 `0, 1, ..., n-1` 的完整实空间重整化。 -/
def decimateAll (n : ℕ) (φ : CNF n) : CNF n :=
  decimateList (List.finRange n) φ

/-- 推论：消去全部变量后，残留的每一个子句都必然是空子句 `[]`。 -/
lemma decimateAll_clauses_empty {n : ℕ} (φ : CNF n) :
    ∀ c ∈ decimateAll n φ, c = [] := by
  intro c hc
  cases c with
  | nil => rfl
  | cons l ls =>
    exfalso
    have h := decimateList_no_vars (List.finRange n) φ (l :: ls) hc l List.mem_cons_self
    exact h (List.mem_finRange l.var)

/-- **定理 1（Davis-Putnam 归结反驳完备性定理）**：
公式 `φ` 不可满足，当且仅当经全部变量实空间重整化后生成的有效公式 `decimateAll n φ` 包含空子句 `[]`。 -/
theorem dp_refutation_complete {n : ℕ} (φ : CNF n) :
    ¬ Satisfiable φ ↔ [] ∈ decimateAll n φ := by
  rw [← decimateList_equisatisfiable (List.finRange n) φ]
  change ¬ Satisfiable (decimateAll n φ) ↔ [] ∈ decimateAll n φ
  constructor
  · intro hUnsat
    by_contra hNoEmpty
    apply hUnsat
    refine ⟨fun _ => false, ?_⟩
    intro c hc
    have hnil := decimateAll_clauses_empty φ c hc
    subst hnil
    exact False.elim (hNoEmpty hc)
  · intro hEmpty ⟨σ, hSat⟩
    have h := hSat [] hEmpty
    simp [evalClause] at h

/-! ## 第二部分：2-SAT 在真实重整化算子 `decimateVar` 下的封闭性 -/

/-- 辅助引理：若 `c` 包含变量 `v`（极性为 `pol`），则剥离 `v` 后长度严格减少：`length (stripVar v c) + 1 ≤ c.length`。 -/
lemma stripVar_length_lt {n : ℕ} (v : Fin n) (c : Clause n) (pol : Bool)
    (h : hasLit c v pol = true) :
    (stripVar v c).length + 1 ≤ c.length := by
  induction c with
  | nil => simp [hasLit] at h
  | cons l ls ih =>
    unfold stripVar
    rw [List.filter_cons]
    by_cases hvar : l.var = v
    · have hne : (l.var != v) = false := by simp [hvar]
      rw [hne]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have hle : (ls.filter (fun l' => l'.var != v)).length ≤ ls.length :=
        List.length_filter_le _ _
      omega
    · have hne : (l.var != v) = true := by simp [hvar]
      rw [hne]
      simp only [↓reduceIte, List.length_cons]
      unfold hasLit at h
      rw [List.any_cons, Bool.or_eq_true] at h
      rcases h with hl | hls
      · simp only [Bool.and_eq_true, beq_iff_eq] at hl
        exact False.elim (hvar hl.1)
      · have hrec := ih hls
        unfold stripVar at hrec
        omega

/-- **定理 2（2-SAT 实空间重整化封闭性）**：
如果 `φ` 是 2-SAT 公式（所有子句长度 `≤ 2`），
那么对任意变量 `v` 执行真实重整化算子 `decimateVar v φ` 后，
所得有效公式中的所有子句长度依然 `≤ 2`（严格封闭于 2-SAT 类）。 -/
theorem decimateVar_preserves_2sat {n : ℕ} (v : Fin n) (φ : CNF n)
    (h2 : ∀ c ∈ φ, c.length ≤ 2) :
    ∀ c ∈ decimateVar v φ, c.length ≤ 2 := by
  intro c hc
  unfold decimateVar at hc
  rw [List.mem_append] at hc
  rcases hc with hrest | hres
  · unfold restClauses at hrest
    rw [List.mem_filter] at hrest
    exact h2 c hrest.1
  · unfold resolvents at hres
    rw [List.mem_flatMap] at hres
    rcases hres with ⟨p, hp, hqmem⟩
    rw [List.mem_map] at hqmem
    rcases hqmem with ⟨q, hq, rfl⟩
    unfold posClauses at hp
    rw [List.mem_map] at hp
    rcases hp with ⟨c1, hc1, rfl⟩
    rw [List.mem_filter] at hc1
    unfold negClauses at hq
    rw [List.mem_map] at hq
    rcases hq with ⟨c2, hc2, rfl⟩
    rw [List.mem_filter] at hc2
    have h1_has : hasLit c1 v true = true := (Bool.and_eq_true _ _).mp hc1.2 |>.1
    have h2_has : hasLit c2 v false = true := (Bool.and_eq_true _ _).mp hc2.2 |>.2
    have hlen1 : (stripVar v c1).length ≤ 1 := by
      have hlt := stripVar_length_lt v c1 true h1_has
      have hle := h2 c1 hc1.1
      omega
    have hlen2 : (stripVar v c2).length ≤ 1 := by
      have hlt := stripVar_length_lt v c2 false h2_has
      have hle := h2 c2 hc2.1
      omega
    exact two_sat_resolution_closed (stripVar v c1) (stripVar v c2) hlen1 hlen2

end Mathmatica.ResolutionCompleteness
