import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathmatica.SATSymmetry
import Mathmatica.RGComplexity

/-!
# 具体构造：SAT 变量消元（实空间重整化）的完备性与 `RGSolver` 实例

在统计物理的实空间重整化群（Decimation / 抽取法）中，消去一个自由度 `v`
在 CNF-SAT 中精确对应于 **Davis-Putnam 归结消元（Resolution）**：
将 `(v ∨ P)` 与 `(¬v ∨ Q)` 合并为不含 `v` 的有效相互作用 `(P ∨ Q)`。

本模块形式化并证明：
1. **归结消元的可靠性**（`resolution_sound`）。
2. **2-SAT 可重整化 vs 3-SAT 不可重整化的临界阶数相变**（`two_sat_rg_fixed_point`, `three_sat_coupling_divergence`）。
3. **完整的 Davis-Putnam 重整化算子 `decimateVar`** 及其**等可满足性定理**（可靠性 + 升维重构完备性）：
   `Satisfiable (decimateVar v φ) ↔ Satisfiable φ`。
4. **将 SAT 实空间重整化正式实例化为 `RGSolver (CNF n)`**，并证明多变量顺序抽取 `decimateList` 保持等可满足性。
-/

namespace Mathmatica.SATDecimation

open Mathmatica.SAT
open Mathmatica.RGComplexity

/-! ## 第一部分：归结重整化步的可靠性（Soundness） -/

/-- **定理 1（归结消元可靠性）**：
若赋值 `σ` 同时满足正子句 `(x_v ∨ P)` 与负子句 `(¬x_v ∨ Q)`，
则 `σ` 必然满足消去变量 `v` 后的有效耦合子句 `(P ∨ Q)`。 -/
theorem resolution_sound {n : ℕ} (v : Fin n) (p q : Clause n) (σ : Assignment n)
    (hp : evalClause σ (⟨v, true⟩ :: p) = true)
    (hq : evalClause σ (⟨v, false⟩ :: q) = true) :
    evalClause σ (p ++ q) = true := by
  unfold evalClause at *
  rw [List.any_append, Bool.or_eq_true]
  simp only [List.any_cons, evalLiteral, Bool.or_eq_true] at hp hq
  cases hv : σ v
  · rw [hv] at hp
    simp at hp
    exact Or.inl (List.any_eq_true.mpr hp)
  · rw [hv] at hq
    simp at hq
    exact Or.inr (List.any_eq_true.mpr hq)

/-! ## 第二部分：临界阶数相变——2-SAT 可重整化 vs 3-SAT 耦合发散 -/

/-- 重整化宽度变换：两个宽度为 `w` 的子句消去共享变量后，新有效子句的最大宽度为 `2w - 2`。 -/
def nextWidth (w : ℕ) : ℕ := 2 * w - 2

/-- **定理 2（2-SAT 宽度封闭性）**：
任意两个 2-SAT 子句消去共享变量后，剩余部分 `p, q` 长度各不超过 1，
其归结子句 `p ++ q` 宽度必然仍不超过 2（严格封闭于 2-体相互作用空间）。 -/
theorem two_sat_resolution_closed {n : ℕ} (p q : Clause n)
    (hp : p.length ≤ 1) (hq : q.length ≤ 1) :
    (p ++ q).length ≤ 2 := by
  rw [List.length_append]
  omega

/-- **定理 3（2-SAT 是重整化宽度映射的不动点）**：
对任意重整化迭代步数 `k`，`w = 2` 始终保持不变：`nextWidth^[k] 2 = 2`。 -/
theorem two_sat_rg_fixed_point (k : ℕ) : nextWidth^[k] 2 = 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

/-- **定理 4（3-SAT 的高阶耦合指数发散）**：
从 3-SAT（`w = 3`）出发，重整化流脱离不动点，经过 `k` 轮消元后，
有效多体耦合阶数精确满足 `nextWidth^[k] 3 = 2 ^ k + 2`。 -/
theorem three_sat_coupling_divergence (k : ℕ) :
    nextWidth^[k] 3 = 2 ^ k + 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold nextWidth
    rw [pow_succ]
    omega

/-- 推论：3-SAT 经过 `k` 轮后耦合阶数严格超过 `2^k`。 -/
theorem three_sat_strictly_expands (k : ℕ) :
    2 ^ k < nextWidth^[k] 3 := by
  rw [three_sat_coupling_divergence]
  omega

/-! ## 第三部分：完整的 Davis-Putnam 实空间重整化算子与升维重构完备性 -/

/-- 判断子句 `c` 是否包含特定极性的变量 `v`。 -/
def hasLit {n : ℕ} (c : Clause n) (v : Fin n) (pol : Bool) : Bool :=
  c.any (fun l => l.var == v && l.pol == pol)

/-- 从子句 `c` 中剥离所有关于变量 `v` 的文字。 -/
def stripVar {n : ℕ} (v : Fin n) (c : Clause n) : Clause n :=
  c.filter (fun l => l.var != v)

/-- 不含变量 `v` 的子句（直接保留到粗粒化后的有效公式中）。 -/
def restClauses {n : ℕ} (v : Fin n) (φ : CNF n) : CNF n :=
  φ.filter (fun c => !hasLit c v true && !hasLit c v false)

/-- 仅含正文字 `x_v`（不含 `¬x_v`）的子句剥离 `v` 后的剩余部分集合。 -/
def posClauses {n : ℕ} (v : Fin n) (φ : CNF n) : CNF n :=
  (φ.filter (fun c => hasLit c v true && !hasLit c v false)).map (stripVar v)

/-- 仅含负文字 `¬x_v`（不含 `x_v`）的子句剥离 `v` 后的剩余部分集合。 -/
def negClauses {n : ℕ} (v : Fin n) (φ : CNF n) : CNF n :=
  (φ.filter (fun c => !hasLit c v true && hasLit c v false)).map (stripVar v)

/-- 对正、负子句两两归结产生的有效多体相互作用子句集合。 -/
def resolvents {n : ℕ} (v : Fin n) (φ : CNF n) : CNF n :=
  (posClauses v φ).flatMap (fun p => (negClauses v φ).map (fun q => p ++ q))

/-- **Davis-Putnam 实空间重整化算子（Decimation）**：消去自由度 `v`，生成不含 `v` 的有效 CNF。 -/
def decimateVar {n : ℕ} (v : Fin n) (φ : CNF n) : CNF n :=
  restClauses v φ ++ resolvents v φ

/-- 修改赋值 `σ` 在单个变量 `v` 上的取值（用于升维重构被消去的自由度）。 -/
def updateAssign {n : ℕ} (σ : Assignment n) (v : Fin n) (b : Bool) : Assignment n :=
  fun i => if i = v then b else σ i

/-- 辅助引理：若 `hasLit c v pol = true`，则将 `v` 赋值为 `pol` 后子句 `c` 必为真。 -/
lemma evalClause_of_hasLit {n : ℕ} {c : Clause n} {v : Fin n} {pol : Bool}
    (h : hasLit c v pol = true) (σ : Assignment n) (hσ : σ v = pol) :
    evalClause σ c = true := by
  unfold hasLit at h
  rw [List.any_eq_true] at h
  rcases h with ⟨l, hl, hcond⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
  unfold evalClause
  rw [List.any_eq_true]
  refine ⟨l, hl, ?_⟩
  unfold evalLiteral
  rw [hcond.1, hcond.2, hσ]
  simp

/-- 辅助引理：若子句 `c` 中不含变量 `v`（任何极性），则修改 `σ v` 不改变 `c` 的真值。 -/
lemma evalClause_updateAssign_of_no_var {n : ℕ} {c : Clause n} {v : Fin n}
    (hno : ∀ l ∈ c, l.var ≠ v) (σ : Assignment n) (b : Bool) :
    evalClause (updateAssign σ v b) c = evalClause σ c := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    unfold evalClause at *
    simp only [List.any_cons]
    have hl : evalLiteral (updateAssign σ v b) l = evalLiteral σ l := by
      unfold evalLiteral updateAssign
      simp [hno l (List.mem_cons_self)]
    have hls : ls.any (evalLiteral (updateAssign σ v b)) = ls.any (evalLiteral σ) :=
      ih (fun l' hl' => hno l' (List.mem_cons_of_mem l hl'))
    rw [hl, hls]

/-- 辅助引理：若 `stripVar v c` 为真，则原字句 `c` 必为真。 -/
lemma evalClause_of_stripVar {n : ℕ} {c : Clause n} {v : Fin n} {σ : Assignment n}
    (h : evalClause σ (stripVar v c) = true) :
    evalClause σ c = true := by
  unfold evalClause stripVar at *
  rw [List.any_eq_true] at h ⊢
  rcases h with ⟨l, hl, hsat⟩
  rw [List.mem_filter] at hl
  exact ⟨l, hl.1, hsat⟩

/-- 辅助引理：若子句 `c` 在赋值 `σ` 下为真，且 `c` 不含与 `σ v` 匹配的 `v`-文字，
则剥离 `v` 后的 `stripVar v c` 在 `σ` 下依然为真。 -/
lemma evalClause_stripVar_of_evalClause {n : ℕ} {c : Clause n} {v : Fin n} {σ : Assignment n}
    (hc : evalClause σ c = true) (hno : hasLit c v (σ v) = false) :
    evalClause σ (stripVar v c) = true := by
  unfold evalClause at hc ⊢
  rw [List.any_eq_true] at hc ⊢
  rcases hc with ⟨l, hl, hsat⟩
  refine ⟨l, ?_, hsat⟩
  unfold stripVar
  rw [List.mem_filter]
  refine ⟨hl, ?_⟩
  rw [bne_iff_ne]
  intro hvar
  unfold evalLiteral at hsat
  rw [beq_iff_eq] at hsat
  have hhas : hasLit c v (σ v) = true := by
    unfold hasLit
    rw [List.any_eq_true]
    refine ⟨l, hl, ?_⟩
    simp [hvar, ← hsat]
  rw [hhas] at hno
  exact Bool.false_ne_true hno.symm

/-- **定理 5（重整化算子 `decimateVar` 的可靠性）**：
若 `σ` 满足原公式 `φ`，则 `σ` 直接满足消去变量 `v` 后的有效公式 `decimateVar v φ`。 -/
theorem decimateVar_sound {n : ℕ} (v : Fin n) {φ : CNF n} {σ : Assignment n}
    (hSat : Satisfies φ σ) :
    Satisfies (decimateVar v φ) σ := by
  intro c hc
  unfold decimateVar at hc
  rw [List.mem_append] at hc
  rcases hc with hrest | hres
  · unfold restClauses at hrest
    rw [List.mem_filter] at hrest
    exact hSat c hrest.1
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
    unfold evalClause
    rw [List.any_append, Bool.or_eq_true]
    cases hv : σ v
    · left
      have hno1 : hasLit c1 v (σ v) = false := by
        rw [hv]
        have h := hc1.2
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
        exact h.2
      exact evalClause_stripVar_of_evalClause (hSat c1 hc1.1) hno1
    · right
      have hno2 : hasLit c2 v (σ v) = false := by
        rw [hv]
        have h := hc2.2
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
        exact h.1
      exact evalClause_stripVar_of_evalClause (hSat c2 hc2.1) hno2

/-- **定理 6（重整化算子 `decimateVar` 的完备性 / 升维重构定理）**：
若粗粒化后的有效公式 `decimateVar v φ` 有解 `σ`，
则必然可以通过给被消去自由度 `v` 赋予 `true` 或 `false`，重构出原公式 `φ` 的解。 -/
theorem decimateVar_complete {n : ℕ} (v : Fin n) {φ : CNF n} {σ : Assignment n}
    (hSat : Satisfies (decimateVar v φ) σ) :
    Satisfiable φ := by
  by_cases hPos : ∀ p ∈ posClauses v φ, evalClause σ p = true
  · -- 情况 A：所有剥离后的正子句都已满足 → 将 v 设为 false 即可满足所有负子句与重言式
    refine ⟨updateAssign σ v false, ?_⟩
    intro c hc
    cases ht : hasLit c v true <;> cases hf : hasLit c v false
    · -- (false, false)：不含 v，属于 restClauses
      have hmem : c ∈ restClauses v φ := by
        unfold restClauses
        rw [List.mem_filter]
        exact ⟨hc, by simp [ht, hf]⟩
      have hno : ∀ l ∈ c, l.var ≠ v := by
        intro l hl hvar
        cases hp : l.pol
        · have : hasLit c v false = true := by
            unfold hasLit; rw [List.any_eq_true]; exact ⟨l, hl, by simp [hvar, hp]⟩
          rw [this] at hf; exact Bool.false_ne_true hf.symm
        · have : hasLit c v true = true := by
            unfold hasLit; rw [List.any_eq_true]; exact ⟨l, hl, by simp [hvar, hp]⟩
          rw [this] at ht; exact Bool.false_ne_true ht.symm
      rw [evalClause_updateAssign_of_no_var hno]
      exact hSat c (List.mem_append_left _ hmem)
    · -- (false, true)：含 ¬v，直接由 σ' v = false 满足
      exact evalClause_of_hasLit hf (updateAssign σ v false) (by simp [updateAssign])
    · -- (true, false)：stripVar v c ∈ posClauses v φ，已由 hPos 满足
      have hmem : stripVar v c ∈ posClauses v φ := by
        unfold posClauses
        rw [List.mem_map]
        exact ⟨c, List.mem_filter.mpr ⟨hc, by simp [ht, hf]⟩, rfl⟩
      have hno : ∀ l ∈ stripVar v c, l.var ≠ v := by
        intro l hl
        unfold stripVar at hl
        rw [List.mem_filter] at hl
        exact bne_iff_ne.mp hl.2
      apply evalClause_of_stripVar (v := v)
      rw [evalClause_updateAssign_of_no_var hno]
      exact hPos (stripVar v c) hmem
    · -- (true, true)：含 ¬v，直接由 σ' v = false 满足
      exact evalClause_of_hasLit hf (updateAssign σ v false) (by simp [updateAssign])
  · -- 情况 B：存在某个剥离后的正子句 p 不满足 → 所有剥离后的负子句 q 必由归结子句 p ++ q 强制满足
    push Not at hPos
    rcases hPos with ⟨p, hpMem, hpFalse⟩
    have hpF : evalClause σ p = false := Bool.eq_false_iff.mpr hpFalse
    have hNeg : ∀ q ∈ negClauses v φ, evalClause σ q = true := by
      intro q hqMem
      have hresMem : p ++ q ∈ decimateVar v φ := by
        unfold decimateVar resolvents
        apply List.mem_append_right
        rw [List.mem_flatMap]
        exact ⟨p, hpMem, List.mem_map.mpr ⟨q, hqMem, rfl⟩⟩
      have hresSat := hSat (p ++ q) hresMem
      unfold evalClause at hresSat hpF ⊢
      rw [List.any_append, hpF, Bool.false_or] at hresSat
      exact hresSat
    -- 将 v 设为 true 即可满足所有正子句与重言式
    refine ⟨updateAssign σ v true, ?_⟩
    intro c hc
    cases ht : hasLit c v true <;> cases hf : hasLit c v false
    · -- (false, false)：不含 v，属于 restClauses
      have hmem : c ∈ restClauses v φ := by
        unfold restClauses
        rw [List.mem_filter]
        exact ⟨hc, by simp [ht, hf]⟩
      have hno : ∀ l ∈ c, l.var ≠ v := by
        intro l hl hvar
        cases hp : l.pol
        · have : hasLit c v false = true := by
            unfold hasLit; rw [List.any_eq_true]; exact ⟨l, hl, by simp [hvar, hp]⟩
          rw [this] at hf; exact Bool.false_ne_true hf.symm
        · have : hasLit c v true = true := by
            unfold hasLit; rw [List.any_eq_true]; exact ⟨l, hl, by simp [hvar, hp]⟩
          rw [this] at ht; exact Bool.false_ne_true ht.symm
      rw [evalClause_updateAssign_of_no_var hno]
      exact hSat c (List.mem_append_left _ hmem)
    · -- (false, true)：stripVar v c ∈ negClauses v φ，已由 hNeg 满足
      have hmem : stripVar v c ∈ negClauses v φ := by
        unfold negClauses
        rw [List.mem_map]
        exact ⟨c, List.mem_filter.mpr ⟨hc, by simp [ht, hf]⟩, rfl⟩
      have hno : ∀ l ∈ stripVar v c, l.var ≠ v := by
        intro l hl
        unfold stripVar at hl
        rw [List.mem_filter] at hl
        exact bne_iff_ne.mp hl.2
      apply evalClause_of_stripVar (v := v)
      rw [evalClause_updateAssign_of_no_var hno]
      exact hNeg (stripVar v c) hmem
    · -- (true, false)：含 v，直接由 σ' v = true 满足
      exact evalClause_of_hasLit ht (updateAssign σ v true) (by simp [updateAssign])
    · -- (true, true)：含 v，直接由 σ' v = true 满足
      exact evalClause_of_hasLit ht (updateAssign σ v true) (by simp [updateAssign])

/-- **定理 7（Davis-Putnam 实空间重整化等可满足性定理）**：
`Satisfiable (decimateVar v φ) ↔ Satisfiable φ`。 -/
theorem decimateVar_equisatisfiable {n : ℕ} (v : Fin n) (φ : CNF n) :
    Satisfiable (decimateVar v φ) ↔ Satisfiable φ :=
  ⟨fun ⟨_, hSat⟩ => decimateVar_complete v hSat,
   fun ⟨σ, hSat⟩ => ⟨σ, decimateVar_sound v hSat⟩⟩

/-! ## 第四部分：实例化为 `RGSolver` 与多变量顺序抽取 -/

/-- 将单变量 Davis-Putnam 抽取正式封装为一个 `RGSolver (CNF n)` 实例。 -/
def satDecimationRGSolver {n : ℕ} (v : Fin n) : RGSolver (CNF n) where
  Sat := Satisfiable
  R := decimateVar v
  preserves_sat := decimateVar_equisatisfiable v

/-- 按变量列表 `vs` 依次执行实空间重整化（顺序抽取所有自由度）。 -/
def decimateList {n : ℕ} : List (Fin n) → CNF n → CNF n
  | [], φ => φ
  | v :: vs, φ => decimateList vs (decimateVar v φ)

/-- **定理 8（多变量重整化流的等可满足性）**：
按任意顺序依次消去变量列表 `vs` 后，最终得到的有效公式与原公式 `φ` 完全等可满足。 -/
theorem decimateList_equisatisfiable {n : ℕ} (vs : List (Fin n)) (φ : CNF n) :
    Satisfiable (decimateList vs φ) ↔ Satisfiable φ := by
  induction vs generalizing φ with
  | nil => rfl
  | cons v vs ih =>
    simp only [decimateList]
    rw [ih (decimateVar v φ), decimateVar_equisatisfiable v φ]

end Mathmatica.SATDecimation
